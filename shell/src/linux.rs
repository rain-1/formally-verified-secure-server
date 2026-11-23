// Linux descriptor and syscall boundary. The event loop uses owned File handles.
use std::fs::File;
use std::io;
use std::mem::{size_of, zeroed};
use std::net::Ipv4Addr;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering};

pub const READ: u32 = (libc::EPOLLIN | libc::EPOLLRDHUP) as u32;
pub const WRITE: u32 = libc::EPOLLOUT as u32;
pub const HANGUP: u32 = (libc::EPOLLERR | libc::EPOLLHUP) as u32;

pub fn syscall_ok(result: libc::c_long) -> io::Result<()> {
    if result < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

// A nonnegative fd must be live and its ownership must transfer to this function.
pub unsafe fn owned_fd(fd: RawFd) -> io::Result<OwnedFd> {
    syscall_ok(fd.into())?;
    // Each caller transfers a descriptor returned by a successful open syscall.
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}

pub fn listener(addr: Ipv4Addr, port: u16) -> io::Result<OwnedFd> {
    // socket returns an owned descriptor that is closed if setup fails.
    let fd = unsafe {
        owned_fd(libc::socket(
            libc::AF_INET,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        ))
    }?;
    let one: libc::c_int = 1;
    let sockaddr = libc::sockaddr_in {
        sin_family: libc::AF_INET as libc::sa_family_t,
        sin_port: port.to_be(),
        sin_addr: libc::in_addr {
            s_addr: u32::from_ne_bytes(addr.octets()),
        },
        sin_zero: [0; 8],
    };
    // Both stack values outlive their synchronous syscall, with the exact ABI sizes.
    unsafe {
        syscall_ok(
            libc::setsockopt(
                fd.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_REUSEADDR,
                (&one as *const libc::c_int).cast(),
                size_of::<libc::c_int>() as libc::socklen_t,
            )
            .into(),
        )?;
        syscall_ok(
            libc::bind(
                fd.as_raw_fd(),
                (&sockaddr as *const libc::sockaddr_in).cast(),
                size_of::<libc::sockaddr_in>() as libc::socklen_t,
            )
            .into(),
        )?;
        syscall_ok(libc::listen(fd.as_raw_fd(), 511).into())?;
    }
    Ok(fd)
}

pub fn accept(listener: &OwnedFd) -> io::Result<Option<File>> {
    loop {
        // Both address arguments are null because the shell does not use the peer address.
        let fd = unsafe {
            libc::accept4(
                listener.as_raw_fd(),
                ptr::null_mut(),
                ptr::null_mut(),
                libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            )
        };
        if fd >= 0 {
            // accept4 returned a new descriptor.
            let fd = unsafe { owned_fd(fd) }?;
            let one: libc::c_int = 1;
            // TCP_NODELAY is opportunistic. The argument points to an initialized c_int.
            unsafe {
                libc::setsockopt(
                    fd.as_raw_fd(),
                    libc::IPPROTO_TCP,
                    libc::TCP_NODELAY,
                    (&one as *const libc::c_int).cast(),
                    size_of::<libc::c_int>() as libc::socklen_t,
                );
            }
            return Ok(Some(File::from(fd)));
        }
        let error = io::Error::last_os_error();
        match error.kind() {
            io::ErrorKind::Interrupted => continue,
            io::ErrorKind::WouldBlock => return Ok(None),
            _ => return Err(error),
        }
    }
}

pub fn half_close(socket: &File) {
    // The caller keeps ownership of the live socket and will drain any queued reads.
    unsafe { libc::shutdown(socket.as_raw_fd(), libc::SHUT_WR) };
}

pub struct Poller(OwnedFd);

impl Poller {
    pub fn new() -> io::Result<Self> {
        // epoll_create1 has no pointer arguments and transfers its new descriptor.
        Ok(Self(unsafe {
            owned_fd(libc::epoll_create1(libc::EPOLL_CLOEXEC))
        }?))
    }

    fn watch(&self, fd: &impl AsRawFd, id: u64, events: u32, op: libc::c_int) -> io::Result<()> {
        let mut event = libc::epoll_event { events, u64: id };
        // epoll_ctl copies the event before returning. Both descriptors are borrowed.
        syscall_ok(unsafe {
            libc::epoll_ctl(self.0.as_raw_fd(), op, fd.as_raw_fd(), &mut event).into()
        })
    }

    pub fn add(&self, fd: &impl AsRawFd, id: u64, events: u32) -> io::Result<()> {
        self.watch(fd, id, events, libc::EPOLL_CTL_ADD)
    }

    pub fn modify(&self, fd: &impl AsRawFd, id: u64, events: u32) -> io::Result<()> {
        self.watch(fd, id, events, libc::EPOLL_CTL_MOD)
    }

    pub fn wait(&self, events: &mut [libc::epoll_event; 128]) -> io::Result<usize> {
        // The kernel may write at most the number of initialized entries supplied.
        let n = unsafe {
            libc::epoll_wait(
                self.0.as_raw_fd(),
                events.as_mut_ptr(),
                events.len() as libc::c_int,
                1000,
            )
        };
        if n < 0 {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                return Ok(0);
            }
            return Err(err);
        }
        Ok(n as usize)
    }
}

pub fn fill_random(mut out: &mut [u8]) -> io::Result<()> {
    while !out.is_empty() {
        // getrandom writes only to the live mutable suffix and retains no pointer.
        let n = unsafe { libc::getrandom(out.as_mut_ptr().cast(), out.len(), 0) };
        if n < 0 {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(err);
        }
        if n == 0 {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        out = &mut out[n as usize..];
    }
    Ok(())
}

static STOP: AtomicBool = AtomicBool::new(false);

extern "C" fn stop(_: libc::c_int) {
    STOP.store(true, Ordering::Relaxed);
}

pub fn stopping() -> bool {
    STOP.load(Ordering::Relaxed)
}

pub fn install_signals() -> io::Result<()> {
    // A zeroed sigaction is populated with the signal-safe handler and an empty mask.
    unsafe {
        let mut action: libc::sigaction = zeroed();
        action.sa_sigaction = stop as *const () as libc::sighandler_t;
        syscall_ok(libc::sigemptyset(&mut action.sa_mask).into())?;
        syscall_ok(libc::sigaction(libc::SIGINT, &action, ptr::null_mut()).into())?;
        syscall_ok(libc::sigaction(libc::SIGTERM, &action, ptr::null_mut()).into())?;
        action.sa_sigaction = libc::SIG_IGN;
        syscall_ok(libc::sigaction(libc::SIGPIPE, &action, ptr::null_mut()).into())
    }
}

pub fn drop_privileges(uid: libc::uid_t, gid: libc::gid_t) -> io::Result<()> {
    // The shell is single-threaded and changes IDs before handling any input.
    unsafe {
        syscall_ok(libc::setgroups(0, ptr::null()).into())?;
        syscall_ok(libc::setgid(gid).into())?;
        syscall_ok(libc::setuid(uid).into())?;
        if libc::setuid(0) == 0 {
            return Err(io::Error::other("privilege drop is reversible"));
        }
    }
    Ok(())
}

pub fn exit(status: i32) -> ! {
    // run() has dropped its resources. _exit avoids post-main runtime teardown
    // syscalls (e.g. signal-stack cleanup) outside the serving allowlist.
    unsafe { libc::_exit(status) }
}
