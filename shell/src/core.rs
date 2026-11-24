// The hand-written ABI boundary for the extracted Low* core.
use std::io;
use std::ops::Range;
use std::sync::OnceLock;

use crate::site::Site;

pub const REQUEST_CAP: usize = 8192;
pub const HEADER_CAP: usize = 4096;
pub const RECORD_INPUT_CAP: usize = 16700;
pub const RECORD_OUTPUT_CAP: usize = 20480;
pub const MAX_PLAINTEXT: usize = 16384;
pub const MAX_CHAIN: usize = 12000;
const STATE_LEN: usize = 512;
const TRANSCRIPT_LEN: usize = 20480;

extern "C" {
    fn Http_Server_handle(
        request: *const u8,
        length: u32,
        entries: *const u32,
        count: u32,
        blob: *const u8,
        blob_len: u32,
        out: *mut u8,
        result: *mut u32,
    );
    fn Tls_Conn_init(state: *mut u8, aes_ok: u8);
    fn Tls_Conn_input(
        state: *mut u8,
        transcript: *mut u8,
        chain: *const u8,
        chain_len: u32,
        key: *const u8,
        random: *const u8,
        input: *const u8,
        input_len: u32,
        out: *mut u8,
        app: *mut u8,
        app_cap: u32,
        result: *mut u32,
    );
    fn Tls_Conn_seal_app(state: *mut u8, plain: *const u8, len: u32, out: *mut u8) -> u32;
    fn Tls_Conn_close_notify(state: *mut u8, out: *mut u8) -> u32;
    fn EverCrypt_AutoConfig2_init();
    fn EverCrypt_AutoConfig2_has_aesni() -> bool;
    fn EverCrypt_AutoConfig2_has_pclmulqdq() -> bool;
    fn EverCrypt_AutoConfig2_has_sse() -> bool;
    fn EverCrypt_AutoConfig2_has_avx() -> bool;
    fn EverCrypt_AutoConfig2_has_movbe() -> bool;
    fn Lib_Memzero0_memzero0(dst: *mut u8, len: u64);
}

fn invalid_result() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid result from verified core",
    )
}

pub struct Reply {
    pub consumed: usize,
    pub header_len: usize,
    pub body: Range<usize>,
    pub close: bool,
}

pub fn request(
    request: &[u8],
    site: &Site,
    header: &mut [u8; HEADER_CAP],
) -> io::Result<Option<Reply>> {
    if request.len() > REQUEST_CAP {
        return Err(invalid_result());
    }
    let mut result = [0; 10];
    let (entries, blob) = site.as_parts();
    // The site owns disjoint table and blob allocations. Request, header, and
    // the local result are separate from these allocations and each other.
    unsafe {
        Http_Server_handle(
            request.as_ptr(),
            request.len() as u32,
            entries.as_ptr(),
            (entries.len() / 4) as u32,
            blob.as_ptr(),
            blob.len() as u32,
            header.as_mut_ptr(),
            result.as_mut_ptr(),
        );
    }
    match result[0] {
        0 => Ok(None),
        1 => {
            let [_, consumed, header_len, off, len, close, ..] = result;
            let (consumed, header_len, off, len) = (
                consumed as usize,
                header_len as usize,
                off as usize,
                len as usize,
            );
            let end = off.checked_add(len).ok_or_else(invalid_result)?;
            if consumed == 0
                || consumed > request.len()
                || header_len > HEADER_CAP
                || end > blob.len()
            {
                return Err(invalid_result());
            }
            Ok(Some(Reply {
                consumed,
                header_len,
                body: off..end,
                close: close != 0,
            }))
        }
        _ => Err(invalid_result()),
    }
}

pub struct Secret<const N: usize>(pub [u8; N]);

impl<const N: usize> Drop for Secret<N> {
    fn drop(&mut self) {
        // The vendored wipe primitive takes a live writable byte span.
        unsafe { Lib_Memzero0_memzero0(self.0.as_mut_ptr(), N as u64) };
    }
}

pub struct Credentials {
    chain: Vec<u8>,
    key: Box<Secret<32>>,
    aes_ok: bool,
}

impl Credentials {
    pub fn new(chain: Vec<u8>, key: Box<Secret<32>>) -> io::Result<Self> {
        if chain.is_empty() || chain.len() > MAX_CHAIN {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid TLS chain size",
            ));
        }
        static AES_OK: OnceLock<bool> = OnceLock::new();
        // Match the feature check in EverCrypt's one-shot AES-GCM entry points.
        let aes_ok = *AES_OK.get_or_init(|| unsafe {
            EverCrypt_AutoConfig2_init();
            EverCrypt_AutoConfig2_has_aesni()
                && EverCrypt_AutoConfig2_has_pclmulqdq()
                && EverCrypt_AutoConfig2_has_sse()
                && EverCrypt_AutoConfig2_has_avx()
                && EverCrypt_AutoConfig2_has_movbe()
        });
        Ok(Self { chain, key, aes_ok })
    }

    pub fn aes_ok(&self) -> bool {
        self.aes_ok
    }
}

pub struct TlsState {
    state: Secret<STATE_LEN>,
    transcript: Box<[u8; TRANSCRIPT_LEN]>,
}

pub enum Disposition {
    Continue,
    Fatal,
    PeerClosed,
}

pub struct Record {
    pub consumed: usize,
    pub output: usize,
    pub app: usize,
    pub disposition: Disposition,
}

impl TlsState {
    pub fn new(credentials: &Credentials) -> Self {
        let mut state = Secret([0; STATE_LEN]);
        // The state array matches Tls.State.stb.
        unsafe { Tls_Conn_init(state.0.as_mut_ptr(), u8::from(credentials.aes_ok)) };
        Self {
            state,
            transcript: Box::new([0; TRANSCRIPT_LEN]),
        }
    }

    pub fn input(
        &mut self,
        credentials: &Credentials,
        input: &[u8],
        out: &mut [u8; RECORD_OUTPUT_CAP],
        app: &mut [u8],
    ) -> io::Result<Record> {
        if input.len() > RECORD_INPUT_CAP || app.len() > REQUEST_CAP {
            return Err(invalid_result());
        }
        let mut random = Secret([0; 96]);
        if self.state.0[0] == 0 {
            // Tls.State.o_phase: waiting for ClientHello.
            crate::linux::fill_random(&mut random.0)?;
        }
        let mut result = [0; 4];
        // Fixed arrays enforce the state, transcript, key, random, and output
        // lengths. The independently owned immutable inputs and exclusive
        // mutable borrows enforce the core's buffer-disjointness requirements.
        unsafe {
            Tls_Conn_input(
                self.state.0.as_mut_ptr(),
                self.transcript.as_mut_ptr(),
                credentials.chain.as_ptr(),
                credentials.chain.len() as u32,
                credentials.key.0.as_ptr(),
                random.0.as_ptr(),
                input.as_ptr(),
                input.len() as u32,
                out.as_mut_ptr(),
                app.as_mut_ptr(),
                app.len() as u32,
                result.as_mut_ptr(),
            );
        }
        let [consumed, output, produced, disposition] = result;
        let (consumed, output, produced) = (consumed as usize, output as usize, produced as usize);
        let disposition = match disposition {
            0 => Disposition::Continue,
            1 => Disposition::Fatal,
            2 => Disposition::PeerClosed,
            _ => return Err(invalid_result()),
        };
        if consumed > input.len()
            || output > out.len()
            || produced > app.len()
            || (consumed == 0
                && (output != 0 || produced != 0 || !matches!(disposition, Disposition::Continue)))
        {
            return Err(invalid_result());
        }
        Ok(Record {
            consumed,
            output,
            app: produced,
            disposition,
        })
    }

    pub fn seal(&mut self, plain: &[u8], out: &mut [u8; RECORD_OUTPUT_CAP]) -> io::Result<usize> {
        if plain.len() > MAX_PLAINTEXT {
            return Err(invalid_result());
        }
        // The array has more than the maximum plaintext length plus 22 bytes.
        let n = unsafe {
            Tls_Conn_seal_app(
                self.state.0.as_mut_ptr(),
                plain.as_ptr(),
                plain.len() as u32,
                out.as_mut_ptr(),
            )
        } as usize;
        if n == 0 {
            return Err(io::Error::new(
                io::ErrorKind::ConnectionAborted,
                "TLS record encryption failed or sequence exhausted",
            ));
        }
        if n != plain.len() + 22 {
            return Err(invalid_result());
        }
        Ok(n)
    }

    pub fn close(&mut self, out: &mut [u8; RECORD_OUTPUT_CAP]) -> io::Result<usize> {
        // The output is disjoint from the state and has at least 24 bytes.
        let n =
            unsafe { Tls_Conn_close_notify(self.state.0.as_mut_ptr(), out.as_mut_ptr()) } as usize;
        if n > 24 {
            return Err(invalid_result());
        }
        Ok(n)
    }
}
