/* Trusted I/O shell: epoll loop, sockets, timeouts. All HTTP logic lives in the
   verified core (Http_Server_handle). This file is intentionally small. */
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <time.h>
#include <unistd.h>
#include <pwd.h>
#include <grp.h>
#include <sys/random.h>
#include "Http_Server.h"
#include "Tls_Conn.h"
#include "EverCrypt_AutoConfig2.h"
#include "site.h"
#include "sandbox.h"

#define MAX_CONNS 4096
#define IDLE_SECS 15
#define REQ_MAX 8192
#define OUT_CAP 4096

typedef struct {
  int fd;                       /* -1 = free */
  time_t last;
  uint8_t in[REQ_MAX];  uint32_t inlen;
  uint8_t hdr[OUT_CAP]; uint32_t hlen, hoff;
  const uint8_t *body;  uint32_t blen, boff;
  uint32_t consumed;
  int writing, close_after, lingering;
  /* TLS mode only */
  uint8_t tls_st[512];
  uint8_t *tr, *rin, *tx;                    /* malloc'd while the connection is open */
  uint32_t rinlen, txlen, txoff;
  int tls_close_after_tx;
} conn_t;

#define RIN_CAP 16700
#define TX_CAP  20480
static conn_t *conns;
static int ep;
static site_t site;
static int use_tls, aes_ok;
static uint8_t *tls_chain, *tls_key;      /* chain: framed CertificateEntry list; key: raw P-256 scalar (32) */
static uint32_t tls_chain_len;
static uint8_t plain_scratch[16384];
static volatile sig_atomic_t stop;

static void ep_mod(conn_t *c, uint32_t ev) {
  struct epoll_event e = { .events = ev, .data.ptr = c };
  epoll_ctl(ep, EPOLL_CTL_MOD, c->fd, &e);
}
static void conn_close(conn_t *c) {
  if (c->fd >= 0) { epoll_ctl(ep, EPOLL_CTL_DEL, c->fd, NULL); close(c->fd); c->fd = -1; }
  free(c->tr); free(c->rin); free(c->tx); c->tr = c->rin = c->tx = NULL;
  if (use_tls) memset(c->tls_st, 0, sizeof c->tls_st);     /* wipe key material */
}
static void begin_linger(conn_t *c) {
  shutdown(c->fd, SHUT_WR);
  c->lingering = 1; c->last = time(NULL);
  ep_mod(c, EPOLLIN | EPOLLRDHUP);
}
static void tls_pump(conn_t *c);
static void tls_do_write(conn_t *c);

/* try to run the verified handler on whatever is buffered */
static void process(conn_t *c) {
  uint32_t res[8] = {0};
  Http_Server_handle(c->in, c->inlen, site.ent, site.count, site.blob, (uint32_t)site.blen, c->hdr, res);
  if (res[0] == 0) {
    if (c->inlen >= REQ_MAX) conn_close(c);
    return;
  }
  c->hlen = res[2]; c->hoff = 0;
  c->body = site.blob + res[3]; c->blen = res[4]; c->boff = 0;
  c->consumed = res[1]; c->close_after = (int)res[5];
  c->writing = 1;
  ep_mod(c, EPOLLOUT | EPOLLRDHUP);
  if (use_tls) tls_do_write(c);
}

static void do_write(conn_t *c) {
  while (c->hoff < c->hlen || c->boff < c->blen) {
    struct iovec iov[2]; int n = 0;
    if (c->hoff < c->hlen) { iov[n].iov_base = c->hdr + c->hoff; iov[n].iov_len = c->hlen - c->hoff; n++; }
    if (c->boff < c->blen) { iov[n].iov_base = (void *)(c->body + c->boff); iov[n].iov_len = c->blen - c->boff; n++; }
    ssize_t w = writev(c->fd, iov, n);
    if (w < 0) { if (errno == EAGAIN || errno == EINTR) return; conn_close(c); return; }
    c->last = time(NULL);
    size_t left = (size_t)w;
    uint32_t hrem = c->hlen - c->hoff;
    if (left >= hrem) { left -= hrem; c->hoff = c->hlen; c->boff += (uint32_t)left; }
    else c->hoff += (uint32_t)left;
  }
  /* response fully written */
  c->writing = 0;
  if (c->close_after) {
    /* lingering close: half-close, then discard input until EOF/timeout, so that
       unread request bytes cannot trigger a RST that destroys our response */
    begin_linger(c);
    return;
  }
  memmove(c->in, c->in + c->consumed, c->inlen - c->consumed);
  c->inlen -= c->consumed;
  ep_mod(c, EPOLLIN | EPOLLRDHUP);
  if (c->inlen) process(c);       /* pipelined request already buffered */
}

static void do_read(conn_t *c) {
  if (c->lingering) {
    uint8_t junk[1024];
    ssize_t r = read(c->fd, junk, sizeof junk);
    if (r == 0 || (r < 0 && errno != EAGAIN && errno != EINTR)) conn_close(c);
    return;
  }
  if (c->inlen >= REQ_MAX) { conn_close(c); return; }
  ssize_t r = read(c->fd, c->in + c->inlen, REQ_MAX - c->inlen);
  if (r == 0) { conn_close(c); return; }
  if (r < 0) { if (errno != EAGAIN && errno != EINTR) conn_close(c); return; }
  c->inlen += (uint32_t)r; c->last = time(NULL);
  process(c);
  if (c->fd >= 0 && c->writing) do_write(c);
}


/* ---------------- TLS mode ---------------- */

/* write pending sealed bytes; returns 1 if all drained, 0 if blocked/closed */
static int tx_flush(conn_t *c) {
  while (c->txoff < c->txlen) {
    ssize_t w = write(c->fd, c->tx + c->txoff, c->txlen - c->txoff);
    if (w < 0) { if (errno == EAGAIN || errno == EINTR) { ep_mod(c, EPOLLOUT | EPOLLRDHUP); return 0; } conn_close(c); return 0; }
    c->txoff += (uint32_t)w; c->last = time(NULL);
  }
  c->txoff = c->txlen = 0;
  return 1;
}

static void tls_queue_close(conn_t *c) {            /* close_notify then linger */
  uint32_t n = Tls_Conn_close_notify(c->tls_st, c->tx);
  c->txlen = n; c->txoff = 0; c->tls_close_after_tx = 1;
}

static void tls_do_write(conn_t *c) {
  for (;;) {
    if (c->fd < 0) return;
    if (!tx_flush(c)) return;
    if (c->tls_close_after_tx) { begin_linger(c); return; }
    if (!c->writing) { ep_mod(c, EPOLLIN | EPOLLRDHUP); return; }
    uint32_t hrem = c->hlen - c->hoff, brem = c->blen - c->boff;
    if (hrem == 0 && brem == 0) {                    /* response done */
      c->writing = 0;
      if (c->close_after) { tls_queue_close(c); continue; }
      memmove(c->in, c->in + c->consumed, c->inlen - c->consumed);
      c->inlen -= c->consumed;
      ep_mod(c, EPOLLIN | EPOLLRDHUP);
      if (c->inlen) { process(c); return; }          /* pipelined request already buffered */
      tls_pump(c);                                   /* more records may be buffered */
      return;
    }
    uint32_t n = 0;
    if (hrem) { memcpy(plain_scratch, c->hdr + c->hoff, hrem); n = hrem; c->hoff += hrem; }
    uint32_t take = 16384 - n; if (take > brem) take = brem;
    memcpy(plain_scratch + n, c->body + c->boff, take); n += take; c->boff += take;
    uint32_t rl = Tls_Conn_seal_app(c->tls_st, plain_scratch, n, c->tx);
    if (rl == 0) { conn_close(c); return; }
    c->txlen = rl; c->txoff = 0;
  }
}

/* feed buffered raw bytes through the verified TLS core, one record at a time */
static void tls_pump(conn_t *c) {
  while (c->fd >= 0 && c->rinlen > 0 && !c->writing && c->txlen == c->txoff && !c->tls_close_after_tx) {
    uint8_t rnd[96] = {0};
    if (c->tls_st[0] == 0 && getrandom(rnd, sizeof rnd, 0) != (ssize_t)sizeof rnd) { conn_close(c); return; }
    uint32_t res[4] = {0};
    Tls_Conn_input(c->tls_st, c->tr, tls_chain, tls_chain_len, tls_key, rnd, c->rin, c->rinlen,
                   c->tx, c->in + c->inlen, REQ_MAX - c->inlen, res);
    memset(rnd, 0, sizeof rnd);
    if (res[0] == 0) break;                           /* incomplete record */
    memmove(c->rin, c->rin + res[0], c->rinlen - res[0]);
    c->rinlen -= res[0];
    c->inlen += res[2];
    if (res[1]) { c->txlen = res[1]; c->txoff = 0; }
    if (res[3] == 1) c->tls_close_after_tx = 1;
    else if (res[3] == 2 && c->txlen == c->txoff) tls_queue_close(c);
    if (res[1] || res[3]) { tls_do_write(c); if (c->fd < 0 || c->lingering) return; continue; }
    if (res[2]) { process(c); if (c->fd < 0) return; }
  }
  if (c->fd >= 0 && !c->lingering) ep_mod(c, c->writing || c->txlen > c->txoff ? (EPOLLOUT | EPOLLRDHUP) : (EPOLLIN | EPOLLRDHUP));
}

static void tls_read(conn_t *c) {
  if (c->lingering) { uint8_t junk[1024]; ssize_t r = read(c->fd, junk, sizeof junk);
    if (r == 0 || (r < 0 && errno != EAGAIN && errno != EINTR)) conn_close(c); return; }
  if (c->rinlen >= RIN_CAP) { conn_close(c); return; }
  ssize_t r = read(c->fd, c->rin + c->rinlen, RIN_CAP - c->rinlen);
  if (r == 0) { conn_close(c); return; }
  if (r < 0) { if (errno != EAGAIN && errno != EINTR) conn_close(c); return; }
  c->rinlen += (uint32_t)r; c->last = time(NULL);
  tls_pump(c);
}

static int load_file(const char *path, uint8_t **buf, uint32_t *len, uint32_t max) {
  FILE *f = fopen(path, "rb"); if (!f) { perror(path); return -1; }
  uint8_t *b = malloc(max + 1); size_t n = fread(b, 1, max + 1, f); fclose(f);
  if (n > max || n == 0) { fprintf(stderr, "%s: bad size\n", path); free(b); return -1; }
  *buf = b; *len = (uint32_t)n; return 0;
}

static void on_sig(int s) { (void)s; stop = 1; }

int main(int argc, char **argv) {
  const char *root = NULL, *bind_a = "0.0.0.0", *user = NULL, *cert = NULL, *keyf = NULL;
  int port = 8080;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--root") && i + 1 < argc) root = argv[++i];
    else if (!strcmp(argv[i], "--port") && i + 1 < argc) port = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--bind") && i + 1 < argc) bind_a = argv[++i];
    else if (!strcmp(argv[i], "--user") && i + 1 < argc) user = argv[++i];
    else if (!strcmp(argv[i], "--tls-chain") && i + 1 < argc) cert = argv[++i];
    else if (!strcmp(argv[i], "--tls-key") && i + 1 < argc) keyf = argv[++i];
    else { fprintf(stderr, "usage: %s --root DIR [--port N] [--bind ADDR] [--user NAME] [--tls-chain FILE --tls-key FILE]\n", argv[0]); return 2; }
  }
  if (!root) { fprintf(stderr, "--root required\n"); return 2; }
  if (!!cert != !!keyf) { fprintf(stderr, "--tls-chain and --tls-key go together\n"); return 2; }
  if (cert) {
    uint32_t kl;
    if (load_file(cert, &tls_chain, &tls_chain_len, 12000) || load_file(keyf, &tls_key, &kl, 32) || kl != 32) return 1;
    use_tls = 1;
    EverCrypt_AutoConfig2_init();
    aes_ok = EverCrypt_AutoConfig2_has_aesni() && EverCrypt_AutoConfig2_has_pclmulqdq() && EverCrypt_AutoConfig2_has_sse();
    fprintf(stderr, "TLS 1.3 enabled; AES-128-GCM %s\n", aes_ok ? "available (AES-NI)" : "unavailable, ChaCha20-Poly1305 only");
  }
  if (site_load(&site, root)) return 1;
  fprintf(stderr, "loaded %u files, %zu bytes\n", site.count, site.blen);

  int ls = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
  int one = 1; setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons((uint16_t)port) };
  if (inet_pton(AF_INET, bind_a, &a.sin_addr) != 1) { fprintf(stderr, "bad --bind\n"); return 2; }
  if (bind(ls, (struct sockaddr *)&a, sizeof a) || listen(ls, 511)) { perror("bind/listen"); return 1; }

  conns = calloc(MAX_CONNS, sizeof(conn_t));
  for (int i = 0; i < MAX_CONNS; i++) conns[i].fd = -1;
  ep = epoll_create1(EPOLL_CLOEXEC);
  struct epoll_event le = { .events = EPOLLIN, .data.ptr = NULL };
  epoll_ctl(ep, EPOLL_CTL_ADD, ls, &le);

  signal(SIGPIPE, SIG_IGN);
  struct sigaction sa = { .sa_handler = on_sig }; sigaction(SIGINT, &sa, NULL); sigaction(SIGTERM, &sa, NULL);

  if (user) {
    struct passwd *pw = getpwnam(user);
    if (!pw) { fprintf(stderr, "no such user %s\n", user); return 1; }
    if (setgroups(0, NULL) || setgid(pw->pw_gid) || setuid(pw->pw_uid)) { perror("drop privileges"); return 1; }
  }
  if (sandbox_enter()) { fprintf(stderr, "sandbox failed\n"); return 1; }
  fprintf(stderr, "listening on %s:%d\n", bind_a, port);

  struct epoll_event evs[128];
  time_t lastsweep = time(NULL);
  while (!stop) {
    int n = epoll_wait(ep, evs, 128, 1000);
    for (int i = 0; i < n; i++) {
      conn_t *c = evs[i].data.ptr;
      if (!c) {                                    /* listener */
        for (;;) {
          int fd = accept4(ls, NULL, NULL, SOCK_NONBLOCK | SOCK_CLOEXEC);
          if (fd < 0) break;
          conn_t *slot = NULL;
          for (int k = 0; k < MAX_CONNS; k++) if (conns[k].fd < 0) { slot = &conns[k]; break; }
          if (!slot) { close(fd); continue; }
          setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
          slot->fd = fd; slot->inlen = 0; slot->writing = 0; slot->lingering = 0; slot->last = time(NULL);
          slot->rinlen = slot->txlen = slot->txoff = 0; slot->tls_close_after_tx = 0;
          if (use_tls) {
            slot->tr = malloc(20480); slot->rin = malloc(RIN_CAP); slot->tx = malloc(TX_CAP);
            if (!slot->tr || !slot->rin || !slot->tx) { slot->fd = -1; close(fd); free(slot->tr); free(slot->rin); free(slot->tx); slot->tr = slot->rin = slot->tx = NULL; continue; }
            Tls_Conn_init(slot->tls_st, aes_ok ? 1 : 0);
          }
          struct epoll_event e = { .events = EPOLLIN | EPOLLRDHUP, .data.ptr = slot };
          epoll_ctl(ep, EPOLL_CTL_ADD, fd, &e);
        }
        continue;
      }
      if (c->fd < 0) continue;
      if (evs[i].events & (EPOLLERR | EPOLLHUP)) { conn_close(c); continue; }
      if (use_tls) {
        if (evs[i].events & EPOLLOUT) tls_do_write(c);
        else if (evs[i].events & (EPOLLIN | EPOLLRDHUP)) tls_read(c);
      } else if (c->writing) { if (evs[i].events & EPOLLOUT) do_write(c); }
      else if (evs[i].events & (EPOLLIN | EPOLLRDHUP)) do_read(c);
    }
    time_t now = time(NULL);
    if (now != lastsweep) {
      lastsweep = now;
      for (int k = 0; k < MAX_CONNS; k++)
        if (conns[k].fd >= 0 && now - conns[k].last > (conns[k].lingering ? 2 : IDLE_SECS)) conn_close(&conns[k]);
    }
  }
  return 0;
}
