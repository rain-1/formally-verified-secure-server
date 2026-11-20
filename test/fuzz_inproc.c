/* In-process fuzzer for the extracted verified entry points (build with ASan+UBSan: `make fuzz`).
   Checks: no sanitizer report, and the output invariants the verified contracts promise. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "Http_Server.h"
#include "Tls_Conn.h"
#include "EverCrypt_AutoConfig2.h"

static uint64_t rs = 88172645463325252ULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 11); }
static void mutate(uint8_t *b, size_t *n, size_t cap) {
  int k = 1 + rnd() % 6;
  while (k--) {
    switch (rnd() % 6) {
      case 0: if (*n) b[rnd() % *n] = (uint8_t)rnd(); break;
      case 1: if (*n) b[rnd() % *n] ^= 1u << (rnd() % 8); break;
      case 2: if (*n > 1) *n = 1 + rnd() % *n; break;
      case 3: if (*n + 8 < cap) { size_t p = rnd() % (*n + 1); memmove(b + p + 4, b + p, *n - p); for (int i = 0; i < 4; i++) b[p + i] = (uint8_t)rnd(); *n += 4; } break;
      case 4: if (*n > 8) { size_t p = rnd() % (*n - 4); memmove(b + p, b + p + 4, *n - p - 4); *n -= 4; } break;
      default: if (*n) { const uint8_t m[] = {0, 0xff, 13, 10, 32, 58, 0x80}; b[rnd() % *n] = m[rnd() % 7]; } break;
    }
  }
}

int main(int argc, char **argv) {
  long iters = argc > 1 ? atol(argv[1]) : 200000;
  /* tiny site */
  static uint8_t blob[64] = "index.html<h1>x</h1>a/b.cssbody{}";
  uint32_t ent[8] = {0, 10, 10, 9, 19, 7, 26, 7};
  const char *seeds[] = {
    "GET / HTTP/1.1\r\nHost: x\r\n\r\n",
    "GET /a/b.css?q=1 HTTP/1.1\r\nHost: x\r\nConnection: close\r\nContent-Length: 0\r\n\r\n",
    "HEAD /index.html HTTP/1.1\r\nhost: y\r\nX-A: b\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n",
    "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n",
  };
  static uint8_t req[8192], out[4096];
  for (long i = 0; i < iters; i++) {
    const char *sd = seeds[rnd() % 4]; size_t n = strlen(sd); memcpy(req, sd, n);
    if (rnd() % 8 == 0) { n = rnd() % 8192; for (size_t j = 0; j < n; j++) req[j] = (uint8_t)rnd(); }
    else mutate(req, &n, sizeof req);
    uint32_t res[8] = {0};
    Http_Server_handle(req, (uint32_t)n, ent, 2, blob, sizeof blob, out, res);
    if (res[0] == 1) {
      if (res[1] > n || res[2] > 512 || (uint64_t)res[3] + res[4] > sizeof blob) { fprintf(stderr, "HTTP invariant violated\n"); return 1; }
    } else if (res[0] != 0) { fprintf(stderr, "bad status\n"); return 1; }
  }
  fprintf(stderr, "http: %ld iterations ok\n", iters);

  EverCrypt_AutoConfig2_init();
  FILE *f = fopen("test/clienthello.bin", "rb"); static uint8_t ch[4096]; size_t chn = fread(ch, 1, sizeof ch, f); fclose(f);
  static uint8_t chain[64], key[32], rn[96], tr[20480], tx[20480], app[8192], buf[20000];
  static uint8_t st[512];
  for (long i = 0; i < iters / 4; i++) {
    uint32_t phase = rnd() % 4;                         /* phase 0: handshake; 1,2: random keys => MAC/format paths */
    Tls_Conn_init(st, rnd() & 1);
    if (phase) { st[0] = (uint8_t)phase; for (int j = 8; j < 300; j++) if (j != 240 && j != 241 && j != 245 && j != 246) st[j] = (uint8_t)rnd(); st[245] = (rnd() & 1) ? 1 : 3; st[240] = st[241] = 0; }
    for (int j = 0; j < 32; j++) key[j] = (uint8_t)(j + 1);
    for (int j = 0; j < 96; j++) rn[j] = (uint8_t)rnd();
    size_t n;
    if (phase == 0 && rnd() % 5) { memcpy(buf, ch, chn); n = chn; mutate(buf, &n, 4096); }
    else { n = rnd() % 3000; for (size_t j = 0; j < n; j++) buf[j] = (uint8_t)rnd();
           if (n >= 5) { buf[0] = (uint8_t)(20 + rnd() % 4); buf[1] = 3; buf[2] = 3; uint32_t l = rnd() % (n - 4 + 1); buf[3] = (uint8_t)(l >> 8); buf[4] = (uint8_t)l; } }
    uint32_t res[4] = {0};
    Tls_Conn_input(st, tr, chain, 20, key, rn, buf, (uint32_t)n, tx, app, sizeof app, res);
    if (res[0] > n || res[1] > 20480 || res[2] > sizeof app) { fprintf(stderr, "TLS invariant violated\n"); return 1; }
  }
  fprintf(stderr, "tls: %ld iterations ok\n", iters / 4);
  return 0;
}
