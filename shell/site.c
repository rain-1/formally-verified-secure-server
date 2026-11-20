/* Trusted site loader: reads the document root into memory ONCE at startup.
   Requests never touch the filesystem. Symlinks are not followed. */
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include "site.h"

static int seg_ok(const char *s) {
  if (!*s || s[0] == '.') return 0;
  for (; *s; s++) {
    unsigned char c = (unsigned char)*s;
    if (!((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
          c == '.' || c == '_' || c == '~' || c == '-'))
      return 0;
  }
  return 1;
}

static int add_entry(site_t *s, const char *key, int fd, off_t size) {
  size_t klen = strlen(key);
  if (size < 0 || (uint64_t)s->blen + klen + (uint64_t)size > 0x7fffffffULL) {
    fprintf(stderr, "site too large (limit 2GiB)\n"); return -1;
  }
  if (s->count == s->cap) {
    s->cap = s->cap ? s->cap * 2 : 64;
    s->ent = realloc(s->ent, (size_t)s->cap * 4 * sizeof(uint32_t));
    if (!s->ent) return -1;
  }
  size_t need = s->blen + klen + (size_t)size;
  if (need > s->bcap) {
    size_t nc = s->bcap ? s->bcap : 4096;
    while (nc < need) nc *= 2;
    s->blob = realloc(s->blob, nc);
    if (!s->blob) return -1;
    s->bcap = nc;
  }
  uint32_t *e = &s->ent[(size_t)s->count * 4];
  e[0] = (uint32_t)s->blen; e[1] = (uint32_t)klen;
  memcpy(s->blob + s->blen, key, klen); s->blen += klen;
  e[2] = (uint32_t)s->blen; e[3] = (uint32_t)size;
  size_t got = 0;
  while (got < (size_t)size) {
    ssize_t r = read(fd, s->blob + s->blen + got, (size_t)size - got);
    if (r <= 0) { fprintf(stderr, "short read for %s\n", key); return -1; }
    got += (size_t)r;
  }
  s->blen += (size_t)size;
  s->count++;
  return 0;
}

static int walk(site_t *s, int dfd, const char *prefix, int depth) {
  if (depth > 16) return 0;
  DIR *d = fdopendir(dfd);
  if (!d) { close(dfd); return -1; }
  struct dirent *de;
  int rc = 0;
  while ((de = readdir(d))) {
    if (!seg_ok(de->d_name)) continue;           /* also skips ".", "..", dotfiles */
    char key[1100];
    int n = snprintf(key, sizeof key, "%s%s", prefix, de->d_name);
    if (n < 0 || n >= 1024) continue;
    struct stat st;
    if (fstatat(dfd, de->d_name, &st, AT_SYMLINK_NOFOLLOW) < 0) continue;
    if (S_ISREG(st.st_mode)) {
      int fd = openat(dfd, de->d_name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
      if (fd < 0) continue;
      rc = add_entry(s, key, fd, st.st_size);
      close(fd);
      if (rc) break;
    } else if (S_ISDIR(st.st_mode)) {
      int sub = openat(dfd, de->d_name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
      if (sub < 0) continue;
      char p2[1100]; snprintf(p2, sizeof p2, "%s/", key);
      rc = walk(s, sub, p2, depth + 1);          /* consumes sub */
      if (rc) break;
    }
  }
  closedir(d);
  return rc;
}

int site_load(site_t *s, const char *root) {
  memset(s, 0, sizeof *s);
  int fd = open(root, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  if (fd < 0) { perror(root); return -1; }
  int rc = walk(s, fd, "", 0);
  return rc;
}
