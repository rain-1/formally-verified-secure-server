#ifndef SITE_H
#define SITE_H
#include <stddef.h>
#include <stdint.h>
typedef struct {
  uint32_t *ent;   /* 4 u32 per entry: key_off key_len body_off body_len */
  uint32_t count, cap;
  uint8_t *blob;
  size_t blen, bcap;
} site_t;
int site_load(site_t *s, const char *root);
#endif
