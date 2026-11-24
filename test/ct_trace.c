/* Run with Valgrind Memcheck. Its undefined-value tracking stands in for
 * secret taint in these fixed-size, synthetic fixtures.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <valgrind/memcheck.h>

#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_P256.h"
#include "internal/Tls_Conn.h"

int main(int argc, char **argv)
{
    if (!RUNNING_ON_VALGRIND) {
        fputs("ct-trace requires Valgrind Memcheck\n", stderr);
        return 2;
    }

    uint8_t key[32] = {[31] = 42};
    if (argc == 2 && !strcmp(argv[1], "control")) {
        VALGRIND_MAKE_MEM_UNDEFINED(key, sizeof key);
        /* Synthetic positive control for the instrumentation. */
        if (key[31] != 0)
            puts("tainted control branch");
        return 0;
    }
    if (argc != 1)
        return 2;

    uint8_t peer[32] = {9}, nonce[32] = {[31] = 19};
    uint8_t transcript[32] = {23}, derived[32], mac[32], shared[32], signature[64];
    uint8_t info[] = {0, 32, 14, 't', 'l', 's', '1', '3', ' ',
                      'f', 'i', 'n', 'i', 's', 'h', 'e', 'd', 0};
    uint8_t plaintext[33] = {23}, cipher[33], iv[12] = {0}, tag[16], aad[5] = {0};

    EverCrypt_AutoConfig2_init();
    bool aes = EverCrypt_AutoConfig2_has_aesni() && EverCrypt_AutoConfig2_has_pclmulqdq()
        && EverCrypt_AutoConfig2_has_sse();

    VALGRIND_MAKE_MEM_UNDEFINED(key, sizeof key);
    VALGRIND_MAKE_MEM_UNDEFINED(nonce, sizeof nonce);
    VALGRIND_MAKE_MEM_UNDEFINED(plaintext, sizeof plaintext);
    VALGRIND_MAKE_MEM_UNDEFINED(iv, sizeof iv);

    puts("HKDF-Expand, HMAC and Finished comparison");
    Hacl_HKDF_expand_sha2_256(derived, key, sizeof key, info, sizeof info, sizeof derived);
    Hacl_HMAC_compute_sha2_256(mac, derived, sizeof derived, transcript, sizeof transcript);
    bool equal = Tls_Util_ct_eq(mac, transcript, sizeof mac, 0, 0);
    VALGRIND_MAKE_MEM_DEFINED(&equal, sizeof equal); /* protocol declassifies equality */
    if (equal)
        return 1;

    puts("X25519 and ECDSA-P256/SHA-256");
    bool dh_ok = Hacl_Curve25519_51_ecdh(shared, key, peer);
    bool sign_ok = Hacl_P256_ecdsa_sign_p256_sha2(signature, sizeof transcript, transcript, key, nonce);
    VALGRIND_MAKE_MEM_DEFINED(&dh_ok, sizeof dh_ok);
    VALGRIND_MAKE_MEM_DEFINED(&sign_ok, sizeof sign_ok);
    if (!dh_ok || !sign_ok)
        return 1;

    puts("ChaCha20-Poly1305 encryption");
    Hacl_AEAD_Chacha20Poly1305_encrypt(cipher, tag, plaintext, sizeof plaintext, aad, sizeof aad, key, iv);
    if (aes) {
        puts("AES-128-GCM encryption");
        EverCrypt_Error_error_code code = EverCrypt_AEAD_encrypt_expand_aes128_gcm(
            key, iv, sizeof iv, aad, sizeof aad, plaintext, sizeof plaintext, cipher, tag);
        VALGRIND_MAKE_MEM_DEFINED(&code, sizeof code);
        if (code != EverCrypt_Error_Success)
            return 1;
    } else {
        puts("AES-128-GCM trace skipped (AES acceleration unavailable in Memcheck)");
    }
    return 0;
}
