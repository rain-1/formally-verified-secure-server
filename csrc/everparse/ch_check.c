/* Adapt the generated validator to the Low* binding. The verified caller
   checks exact consumption using the returned end position or error code. */
#include <stddef.h>
#include "ClientHello.h"
/* Each generated header brings its own definition. This adapter uses neither. */
#undef KRML_CHECK_SIZE
#include "internal/Tls_ChValid.h"

_Static_assert(EVERPARSE_VALIDATOR_MAX_LENGTH == 1152921504606846975ULL,
               "EverParse result encoding must match Tls.ChValid");

static void ignore_error(const char *a, const char *b, const char *c, uint64_t code, uint8_t *ctx, uint8_t *in, uint64_t pos) {
  (void)a; (void)b; (void)c; (void)code; (void)ctx; (void)in; (void)pos;
}

uint64_t Tls_ChValid_validate_prefix(uint8_t *b, uint32_t len) {
  return ClientHelloValidateClientHelloBody(NULL, ignore_error, b, len, 0);
}
