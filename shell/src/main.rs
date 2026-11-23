mod core;
mod linux;
mod sandbox;
mod site;

use std::env;
use std::fs::File;
use std::io::{self, IoSlice, Read, Write};
use std::net::Ipv4Addr;
use std::path::PathBuf;
use std::time::{Duration, Instant};
use std::{collections::HashMap, os::fd::OwnedFd};

use crate::core::{
    Credentials, Disposition, Reply, Secret, TlsState, HEADER_CAP, MAX_CHAIN, MAX_PLAINTEXT,
    RECORD_INPUT_CAP, RECORD_OUTPUT_CAP, REQUEST_CAP,
};
use site::Site;

const MAX_CONNECTIONS: usize = 4096;
const IDLE: Duration = Duration::from_secs(15);
const LINGER: Duration = Duration::from_secs(2);
const LISTENER: u64 = 0;

struct Settings {
    root: PathBuf,
    bind: Ipv4Addr,
    port: u16,
    credentials: Option<(PathBuf, PathBuf)>,
    ids: Option<(u32, u32)>,
}

fn invalid_arg(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.to_owned())
}

impl Settings {
    fn parse() -> io::Result<Self> {
        let mut root = None;
        let mut bind = Ipv4Addr::UNSPECIFIED;
        let mut port = 8080;
        let mut cert = None;
        let mut key = None;
        let mut uid = None;
        let mut gid = None;
        let mut args = env::args_os().skip(1);
        while let Some(flag) = args.next() {
            let value = args
                .next()
                .ok_or_else(|| invalid_arg("missing option value"))?;
            match flag.to_str() {
                Some("--root") => root = Some(value.into()),
                Some("--bind") => {
                    bind = value
                        .to_string_lossy()
                        .parse()
                        .map_err(|_| invalid_arg("bad --bind"))?
                }
                Some("--port") => {
                    port = value
                        .to_string_lossy()
                        .parse()
                        .map_err(|_| invalid_arg("bad --port"))?
                }
                Some("--uid") => {
                    uid = Some(
                        value
                            .to_string_lossy()
                            .parse()
                            .map_err(|_| invalid_arg("bad --uid"))?,
                    )
                }
                Some("--gid") => {
                    gid = Some(
                        value
                            .to_string_lossy()
                            .parse()
                            .map_err(|_| invalid_arg("bad --gid"))?,
                    )
                }
                Some("--tls-chain") => cert = Some(value.into()),
                Some("--tls-key") => key = Some(value.into()),
                _ => return Err(invalid_arg("unknown option")),
            }
        }
        let credentials = match (cert, key) {
            (Some(cert), Some(key)) => Some((cert, key)),
            (None, None) => None,
            _ => return Err(invalid_arg("--tls-chain and --tls-key go together")),
        };
        let ids = match (uid, gid) {
            (Some(0), _) | (_, Some(0)) => return Err(invalid_arg("refusing uid/gid 0")),
            (Some(uid), Some(gid)) => Some((uid, gid)),
            (None, None) => None,
            _ => return Err(invalid_arg("--uid and --gid go together")),
        };
        Ok(Self {
            root: root.ok_or_else(|| invalid_arg("--root required"))?,
            bind,
            port,
            credentials,
            ids,
        })
    }
}

fn load_credentials((chain, key): (PathBuf, PathBuf)) -> io::Result<Credentials> {
    let mut bytes = Vec::new();
    File::open(chain)?
        .take((MAX_CHAIN + 1) as u64)
        .read_to_end(&mut bytes)?;
    let mut secret = Box::new(Secret([0; 32]));
    let mut key = File::open(key)?;
    key.read_exact(&mut secret.0)?;
    let mut extra = Secret([0; 1]);
    if key.read(&mut extra.0)? != 0 {
        return Err(invalid_arg("TLS key must be a 32-byte P-256 scalar"));
    }
    Credentials::new(bytes, secret)
}

struct TlsIo {
    state: TlsState,
    rx: Box<[u8; RECORD_INPUT_CAP]>,
    rx_len: usize,
    tx: Box<[u8; RECORD_OUTPUT_CAP]>,
    tx_len: usize,
    tx_sent: usize,
    close_after_tx: bool,
}

impl TlsIo {
    fn new(credentials: &Credentials) -> Self {
        Self {
            state: TlsState::new(credentials),
            rx: Box::new([0; RECORD_INPUT_CAP]),
            rx_len: 0,
            tx: Box::new([0; RECORD_OUTPUT_CAP]),
            tx_len: 0,
            tx_sent: 0,
            close_after_tx: false,
        }
    }

    fn queue_close(&mut self) -> io::Result<()> {
        self.tx_len = self.state.close(&mut self.tx)?;
        self.close_after_tx = true;
        Ok(())
    }
}

struct Connection {
    socket: File,
    last: Instant,
    request: [u8; REQUEST_CAP],
    request_len: usize,
    header: [u8; HEADER_CAP],
    reply: Option<Reply>,
    sent: usize,
    lingering: bool,
    tls: Option<TlsIo>,
    interest: u32,
}

fn nonblocking(result: io::Result<usize>, empty: io::ErrorKind) -> io::Result<Option<usize>> {
    match result {
        Ok(0) => Err(empty.into()),
        Ok(n) => Ok(Some(n)),
        Err(err)
            if matches!(
                err.kind(),
                io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
            ) =>
        {
            Ok(None)
        }
        Err(err) => Err(err),
    }
}

impl Connection {
    fn new(socket: File, credentials: Option<&Credentials>) -> Self {
        Self {
            socket,
            last: Instant::now(),
            request: [0; REQUEST_CAP],
            request_len: 0,
            header: [0; HEADER_CAP],
            reply: None,
            sent: 0,
            lingering: false,
            tls: credentials.map(TlsIo::new),
            interest: linux::READ,
        }
    }

    fn read(&mut self) -> io::Result<()> {
        if self.lingering {
            nonblocking(
                self.socket.read(&mut [0; 1024]),
                io::ErrorKind::UnexpectedEof,
            )?;
            return Ok(());
        }
        let (buf, len): (&mut [u8], &mut usize) = match &mut self.tls {
            Some(tls) => (&mut tls.rx[..], &mut tls.rx_len),
            None => (&mut self.request[..], &mut self.request_len),
        };
        if *len == buf.len() {
            return Err(io::ErrorKind::InvalidData.into());
        }
        if let Some(n) = nonblocking(
            self.socket.read(&mut buf[*len..]),
            io::ErrorKind::UnexpectedEof,
        )? {
            *len += n;
            self.last = Instant::now();
        }
        Ok(())
    }

    fn linger(&mut self) -> u32 {
        linux::half_close(&self.socket);
        self.lingering = true;
        self.last = Instant::now();
        linux::READ
    }

    fn drive(
        &mut self,
        readable: bool,
        site: &Site,
        credentials: Option<&Credentials>,
        scratch: &mut [u8; MAX_PLAINTEXT],
    ) -> io::Result<u32> {
        if readable {
            self.read()?;
        }
        if self.lingering {
            return Ok(linux::READ);
        }

        let mut parse_pending = self.request_len != 0;
        loop {
            if let Some(tls) = &mut self.tls {
                while tls.tx_sent < tls.tx_len {
                    let pending = &tls.tx[tls.tx_sent..tls.tx_len];
                    let Some(n) =
                        nonblocking(self.socket.write(pending), io::ErrorKind::WriteZero)?
                    else {
                        return Ok(linux::WRITE);
                    };
                    tls.tx_sent += n;
                    self.last = Instant::now();
                }
                tls.tx_sent = 0;
                tls.tx_len = 0;
                if tls.close_after_tx {
                    return Ok(self.linger());
                }
            }

            if let Some(reply) = &self.reply {
                let head = &self.header[self.sent.min(reply.header_len)..reply.header_len];
                let body = &site.as_parts().1[reply.body.clone()];
                let body = &body[self.sent.saturating_sub(reply.header_len)..];
                if head.is_empty() && body.is_empty() {
                    let reply = self.reply.take().expect("a reply was just matched");
                    self.sent = 0;
                    if reply.close {
                        if let Some(tls) = &mut self.tls {
                            tls.queue_close()?;
                            continue;
                        }
                        return Ok(self.linger());
                    }
                    self.request
                        .copy_within(reply.consumed..self.request_len, 0);
                    self.request_len -= reply.consumed;
                    parse_pending = self.request_len != 0;
                    continue;
                }
                if let Some(tls) = &mut self.tls {
                    let take = (MAX_PLAINTEXT - head.len()).min(body.len());
                    let len = head.len() + take;
                    scratch[..head.len()].copy_from_slice(head);
                    scratch[head.len()..len].copy_from_slice(&body[..take]);
                    tls.tx_len = tls.state.seal(&scratch[..len], &mut tls.tx)?;
                    self.sent += len;
                } else {
                    let parts = [IoSlice::new(head), IoSlice::new(body)];
                    let Some(n) =
                        nonblocking(self.socket.write_vectored(&parts), io::ErrorKind::WriteZero)?
                    else {
                        return Ok(linux::WRITE);
                    };
                    self.sent += n;
                    self.last = Instant::now();
                }
                continue;
            }

            if parse_pending {
                parse_pending = false;
                self.reply =
                    core::request(&self.request[..self.request_len], site, &mut self.header)?;
                if self.reply.is_some() {
                    continue;
                }
                if self.request_len == REQUEST_CAP {
                    return Err(io::ErrorKind::InvalidData.into());
                }
            }

            let (Some(tls), Some(credentials)) = (&mut self.tls, credentials) else {
                return Ok(linux::READ);
            };
            if tls.rx_len == 0 {
                return Ok(linux::READ);
            }
            let record = tls.state.input(
                credentials,
                &tls.rx[..tls.rx_len],
                &mut tls.tx,
                &mut self.request[self.request_len..],
            )?;
            if record.consumed == 0 {
                return Ok(linux::READ);
            }
            tls.rx.copy_within(record.consumed..tls.rx_len, 0);
            tls.rx_len -= record.consumed;
            self.request_len += record.app;
            parse_pending = record.app != 0;
            tls.tx_len = record.output;
            match record.disposition {
                Disposition::Continue => (),
                Disposition::Fatal => tls.close_after_tx = true,
                Disposition::PeerClosed if record.output == 0 => tls.queue_close()?,
                Disposition::PeerClosed => tls.close_after_tx = true,
            }
        }
    }

    fn live_at(&self, now: Instant) -> bool {
        let timeout = if self.lingering { LINGER } else { IDLE };
        now.duration_since(self.last) <= timeout
    }
}

fn accept_ready(
    listener: &OwnedFd,
    poller: &linux::Poller,
    conns: &mut HashMap<u64, Box<Connection>>,
    next: &mut u64,
    credentials: Option<&Credentials>,
) -> io::Result<()> {
    for _ in 0..128 {
        let socket = match linux::accept(listener) {
            Ok(Some(socket)) => socket,
            Ok(None) => break,
            // A full descriptor table or a client abort is transient.
            Err(err)
                if matches!(
                    err.raw_os_error(),
                    Some(libc::EMFILE | libc::ENFILE | libc::ECONNABORTED)
                ) =>
            {
                break
            }
            Err(err) => return Err(err),
        };
        if conns.len() == MAX_CONNECTIONS {
            continue;
        }
        let id = *next;
        *next = next
            .checked_add(1)
            .ok_or_else(|| io::Error::other("connection IDs exhausted"))?;
        poller.add(&socket, id, linux::READ)?;
        conns.insert(id, Box::new(Connection::new(socket, credentials)));
    }
    Ok(())
}

fn run(settings: Settings) -> io::Result<()> {
    let credentials = settings.credentials.map(load_credentials).transpose()?;
    if let Some(credentials) = &credentials {
        let suites = if credentials.aes_ok() {
            "AES-128-GCM and ChaCha20-Poly1305"
        } else {
            "ChaCha20-Poly1305"
        };
        eprintln!("TLS 1.3 enabled ({suites})");
    }
    let site = Site::load(&settings.root)?;
    let (table, blob) = site.as_parts();
    eprintln!("loaded {} files, {} bytes", table.len() / 4, blob.len());

    let listener = linux::listener(settings.bind, settings.port)?;
    let poller = linux::Poller::new()?;
    poller.add(&listener, LISTENER, libc::EPOLLIN as u32)?;
    let mut conns = HashMap::with_capacity(MAX_CONNECTIONS);
    let mut events = [libc::epoll_event { events: 0, u64: 0 }; 128];
    let mut next = 1;
    let mut scratch = Secret([0; MAX_PLAINTEXT]);
    linux::install_signals()?;
    if let Some((uid, gid)) = settings.ids {
        linux::drop_privileges(uid, gid)?;
    }
    sandbox::enter()?;
    eprintln!("listening on {}:{}", settings.bind, settings.port);

    let mut swept = Instant::now();
    while !linux::stopping() {
        let n = poller.wait(&mut events)?;
        for event in &events[..n] {
            let id = event.u64;
            if id == LISTENER {
                accept_ready(
                    &listener,
                    &poller,
                    &mut conns,
                    &mut next,
                    credentials.as_ref(),
                )?;
                continue;
            }
            let Some(conn) = conns.get_mut(&id) else {
                continue;
            };
            let active = event.events;
            if active & linux::HANGUP != 0 {
                conns.remove(&id);
                continue;
            }
            let result = conn.drive(
                active & linux::READ != 0,
                &site,
                credentials.as_ref(),
                &mut scratch.0,
            );
            match result {
                Ok(interest) if interest != conn.interest => {
                    if poller.modify(&conn.socket, id, interest).is_ok() {
                        conn.interest = interest;
                    } else {
                        conns.remove(&id);
                    }
                }
                Ok(_) => (),
                Err(_) => {
                    conns.remove(&id);
                }
            }
        }
        let now = Instant::now();
        if now.duration_since(swept) >= Duration::from_secs(1) {
            swept = now;
            conns.retain(|_, conn| conn.live_at(now));
        }
    }
    Ok(())
}

fn main() {
    let settings = match Settings::parse() {
        Ok(settings) => settings,
        Err(err) => {
            eprintln!("{err}\nusage: server --root DIR [--port N] [--bind ADDR] [--uid N --gid N] [--tls-chain FILE --tls-key FILE]");
            linux::exit(2);
        }
    };
    match run(settings) {
        Ok(()) => linux::exit(0),
        Err(err) => {
            eprintln!("server: {err}");
            linux::exit(1);
        }
    }
}
