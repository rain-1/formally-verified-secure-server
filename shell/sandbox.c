/* Post-startup confinement of the serving process (defense in depth, NOT part of the proofs).
   After the site is loaded and the listener is open, the process needs only socket I/O.
   - PR_SET_NO_NEW_PRIVS, non-dumpable, no core files (key material in memory)
   - Landlock: deny ALL filesystem access and new TCP bind/connect (best effort; needs kernel >= 5.13/6.7)
   - seccomp-bpf: allowlist of the few syscalls the event loop uses; anything else kills the process */
#define _GNU_SOURCE
#include <errno.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#ifdef __has_include
# if __has_include(<linux/landlock.h>)
#  include <linux/landlock.h>
#  define HAVE_LANDLOCK 1
# endif
#endif
#include "sandbox.h"

#if defined(__x86_64__)
# define AUDIT_ARCH_CUR AUDIT_ARCH_X86_64
#elif defined(__aarch64__)
# define AUDIT_ARCH_CUR AUDIT_ARCH_AARCH64
#else
# error "unsupported architecture for seccomp filter"
#endif

static int landlock_deny_all(void) {
#ifdef HAVE_LANDLOCK
  int abi = (int)syscall(SYS_landlock_create_ruleset, NULL, 0, LANDLOCK_CREATE_RULESET_VERSION);
  if (abi < 1) { fprintf(stderr, "sandbox: Landlock unavailable (continuing with seccomp only)\n"); return 0; }
  struct landlock_ruleset_attr attr = {0};
  attr.handled_access_fs = (1ULL << 13) - 1;                 /* ABI 1 */
  if (abi >= 2) attr.handled_access_fs |= (1ULL << 13);      /* REFER */
  if (abi >= 3) attr.handled_access_fs |= (1ULL << 14);      /* TRUNCATE */
  if (abi >= 5) attr.handled_access_fs |= (1ULL << 15);      /* IOCTL_DEV */
  size_t sz = sizeof attr;
  if (abi >= 4) attr.handled_access_net = 3;                 /* BIND_TCP | CONNECT_TCP */
  else sz = offsetof(struct landlock_ruleset_attr, handled_access_net);
  int fd = (int)syscall(SYS_landlock_create_ruleset, &attr, sz, 0);
  if (fd < 0) { perror("landlock_create_ruleset"); return -1; }
  int rc = (int)syscall(SYS_landlock_restrict_self, fd, 0);  /* no rules added => everything handled is denied */
  close(fd);
  if (rc) { perror("landlock_restrict_self"); return -1; }
#endif
  return 0;
}

#define ALLOW(nr) BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (nr), 0, 1), BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)

static int seccomp_allowlist(void) {
  struct sock_filter f[] = {
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, arch)),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_CUR, 1, 0),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
    ALLOW(SYS_read), ALLOW(SYS_write), ALLOW(SYS_writev), ALLOW(SYS_close),
    ALLOW(SYS_epoll_wait), ALLOW(SYS_epoll_pwait), ALLOW(SYS_epoll_ctl),
    ALLOW(SYS_accept4), ALLOW(SYS_shutdown), ALLOW(SYS_setsockopt),
    ALLOW(SYS_getrandom), ALLOW(SYS_clock_gettime), ALLOW(SYS_rt_sigreturn),
    ALLOW(SYS_rt_sigprocmask),   /* glibc's vDSO getrandom blocks signals while setting up its state */
    ALLOW(SYS_brk), ALLOW(SYS_mmap), ALLOW(SYS_munmap), ALLOW(SYS_mremap), ALLOW(SYS_madvise),
    ALLOW(SYS_exit_group), ALLOW(SYS_exit),
#ifdef SYS_time
    ALLOW(SYS_time),
#endif
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
  };
  struct sock_fprog prog = { .len = (unsigned short)(sizeof f / sizeof f[0]), .filter = f };
  if (syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, SECCOMP_FILTER_FLAG_TSYNC, &prog)) { perror("seccomp"); return -1; }
  return 0;
}

int sandbox_enter(void) {
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) { perror("no_new_privs"); return -1; }
  prctl(PR_SET_DUMPABLE, 0, 0, 0, 0);
  struct rlimit rl = {0, 0};
  setrlimit(RLIMIT_CORE, &rl);
  if (landlock_deny_all()) return -1;
  return seccomp_allowlist();
}
