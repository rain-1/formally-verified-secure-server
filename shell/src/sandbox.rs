// Post-startup confinement. Keep the allowlist independent of Rust I/O policy.
use std::io;
use std::mem::{offset_of, size_of};
use std::os::fd::AsRawFd;
use std::ptr;

use crate::linux::{owned_fd, syscall_ok};

#[cfg(target_arch = "x86_64")]
const AUDIT_ARCH: u32 = 0xc000_003e;
#[cfg(target_arch = "aarch64")]
const AUDIT_ARCH: u32 = 0xc000_00b7;

#[repr(C)]
struct LandlockRuleset {
    fs: u64,
    net: u64,
}

fn landlock() -> io::Result<()> {
    const VERSION: libc::c_uint = 1; // LANDLOCK_CREATE_RULESET_VERSION
                                     // A version query takes a null ruleset pointer and size zero.
    let abi = unsafe {
        libc::syscall(
            libc::SYS_landlock_create_ruleset,
            ptr::null::<LandlockRuleset>(),
            0usize,
            VERSION,
        )
    };
    if abi < 1 {
        eprintln!("sandbox: Landlock unavailable (continuing with seccomp only)");
        return Ok(());
    }

    let mut ruleset = LandlockRuleset {
        fs: (1 << 13) - 1,
        net: 0,
    };
    if abi >= 2 {
        ruleset.fs |= 1 << 13;
    } // LANDLOCK_ACCESS_FS_REFER
    if abi >= 3 {
        ruleset.fs |= 1 << 14;
    } // LANDLOCK_ACCESS_FS_TRUNCATE
    if abi >= 5 {
        ruleset.fs |= 1 << 15;
    } // LANDLOCK_ACCESS_FS_IOCTL_DEV
    let size = if abi >= 4 {
        ruleset.net = 3; // LANDLOCK_ACCESS_NET_BIND_TCP | LANDLOCK_ACCESS_NET_CONNECT_TCP
        size_of::<LandlockRuleset>()
    } else {
        offset_of!(LandlockRuleset, net)
    };
    // The size advertises only the ABI fields supported by this kernel.
    let fd = unsafe { libc::syscall(libc::SYS_landlock_create_ruleset, &ruleset, size, 0u32) };
    syscall_ok(fd)?;
    // landlock_create_ruleset returned a new descriptor.
    let fd = unsafe { owned_fd(fd as libc::c_int) }?;
    // With no rules, all access covered by the ruleset is denied.
    syscall_ok(unsafe { libc::syscall(libc::SYS_landlock_restrict_self, fd.as_raw_fd(), 0u32) })
}

#[repr(C)]
struct SeccompData {
    nr: i32,
    arch: u32,
}

fn stmt(code: u32, k: u32) -> libc::sock_filter {
    libc::sock_filter {
        code: code as u16,
        jt: 0,
        jf: 0,
        k,
    }
}

fn equals(k: u32, yes: u8, no: u8) -> libc::sock_filter {
    libc::sock_filter {
        code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16,
        jt: yes,
        jf: no,
        k,
    }
}

fn seccomp() -> io::Result<()> {
    let load_word = libc::BPF_LD | libc::BPF_W | libc::BPF_ABS;
    let kill = stmt(libc::BPF_RET | libc::BPF_K, libc::SECCOMP_RET_KILL_PROCESS);
    let allow = stmt(libc::BPF_RET | libc::BPF_K, libc::SECCOMP_RET_ALLOW);
    let mut filter = vec![
        stmt(load_word, offset_of!(SeccompData, arch) as u32),
        equals(AUDIT_ARCH, 1, 0),
        kill,
        stmt(load_word, offset_of!(SeccompData, nr) as u32),
    ];
    for nr in [
        libc::SYS_read,
        libc::SYS_write,
        libc::SYS_writev,
        libc::SYS_close,
        libc::SYS_epoll_wait,
        libc::SYS_epoll_pwait,
        libc::SYS_epoll_ctl,
        libc::SYS_accept4,
        libc::SYS_shutdown,
        libc::SYS_setsockopt,
        libc::SYS_getrandom,
        libc::SYS_clock_gettime,
        libc::SYS_rt_sigreturn,
        libc::SYS_rt_sigprocmask,
        libc::SYS_brk,
        libc::SYS_mmap,
        libc::SYS_munmap,
        libc::SYS_mremap,
        libc::SYS_madvise,
        libc::SYS_exit_group,
        libc::SYS_exit,
        #[cfg(target_arch = "x86_64")]
        libc::SYS_time,
    ] {
        filter.push(equals(nr as u32, 0, 1));
        filter.push(allow);
    }
    filter.push(kill);
    let program = libc::sock_fprog {
        len: filter.len() as u16,
        filter: filter.as_mut_ptr(),
    };
    // seccomp copies the initialized program before returning.
    let rc = unsafe {
        libc::syscall(
            libc::SYS_seccomp,
            libc::SECCOMP_SET_MODE_FILTER,
            libc::SECCOMP_FILTER_FLAG_TSYNC,
            &program,
        )
    };
    if rc != 0 {
        syscall_ok(rc)?;
        return Err(io::Error::other("seccomp filter did not synchronize"));
    }
    Ok(())
}

pub fn enter() -> io::Result<()> {
    // prctl's variadic arguments are unsigned long.
    let zero: libc::c_ulong = 0;
    let one: libc::c_ulong = 1;
    unsafe {
        syscall_ok(libc::prctl(libc::PR_SET_NO_NEW_PRIVS, one, zero, zero, zero).into())?;
        syscall_ok(libc::prctl(libc::PR_SET_DUMPABLE, zero, zero, zero, zero).into())?;
        let no_core = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        syscall_ok(libc::setrlimit(libc::RLIMIT_CORE, &no_core).into())?;
    }
    landlock()?;
    seccomp()
}
