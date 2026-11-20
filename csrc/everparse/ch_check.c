/* Thin glue (hand-written) around the EverParse-generated ClientHello validator (spec/ClientHello.3d).
   Returns true iff the body is exactly one grammar-valid ClientHello: the verified validator succeeds AND its end
   position equals the body length. */
#include <stdbool.h>
#include <stdint.h>
#include "ClientHello.h"

static void ignore_error(const char *a, const char *b, const char *c, uint64_t code, uint8_t *ctx, uint8_t *in, uint64_t pos) {
  (void)a; (void)b; (void)c; (void)code; (void)ctx; (void)in; (void)pos;
}

bool Tls_ChValid_check(uint8_t *b, uint32_t len) {
  uint64_t r = ClientHelloValidateClientHelloBody((uint8_t *)0, ignore_error, b, (uint64_t)len, 0);
  return !EverParseIsError(r) && r == (uint64_t)len;
}
