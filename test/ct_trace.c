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
#include "Tls_Conn.h"
#include "internal/Tls_Conn.h"

static bool seal_record(uint8_t suite)
{
    /* Offsets from Tls.State for the extracted connection fixture. */
    enum { STATE_LEN = 512, PHASE = 0, SERVER_KEY = 188, SERVER_IV = 220, SUITE = 245 };
    uint8_t state[STATE_LEN], plaintext[32] = {23}, record[20480];
    uint8_t inner[33] = {23, [32] = 23};
    uint8_t expected[5 + sizeof inner + 16] = {23, 3, 3, 0, sizeof inner + 16};
    uint8_t *cipher = expected + 5;
    uint8_t *tag = cipher + sizeof inner;
    bool aes = suite == 1;
    Tls_Conn_init(state, aes);
    state[PHASE] = 2;
    state[SUITE] = suite;
    state[SERVER_KEY] = 42;
    state[SERVER_IV] = 19;

    /* Sequence number zero makes the nonce equal to the fixed server IV. */
    if (aes) {
        if (EverCrypt_AEAD_encrypt_expand_aes128_gcm(state + SERVER_KEY, state + SERVER_IV,
                12, expected, 5, inner, sizeof inner, cipher, tag) != EverCrypt_Error_Success)
            return false;
    } else {
        Hacl_AEAD_Chacha20Poly1305_encrypt(cipher, tag, inner, sizeof inner, expected, 5,
            state + SERVER_KEY, state + SERVER_IV);
    }

    VALGRIND_MAKE_MEM_UNDEFINED(state + SERVER_KEY, 32);
    VALGRIND_MAKE_MEM_UNDEFINED(state + SERVER_IV, 12);
    VALGRIND_MAKE_MEM_UNDEFINED(plaintext, sizeof plaintext);
    uint32_t length = Tls_Conn_seal_app(state, plaintext, sizeof plaintext, record);
    if (length != sizeof expected)
        return false;
    VALGRIND_MAKE_MEM_DEFINED(record, sizeof expected); /* wire bytes are public */
    return memcmp(record, expected, sizeof expected) == 0;
}

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
    uint8_t transcript[32] = {23}, derived[32], mac[32], share[32], shared[32], signature[64];
    uint8_t info[] = {0, 32, 14, 't', 'l', 's', '1', '3', ' ',
                      'f', 'i', 'n', 'i', 's', 'h', 'e', 'd', 0};

    EverCrypt_AutoConfig2_init();
    bool aes = EverCrypt_AutoConfig2_has_aesni() && EverCrypt_AutoConfig2_has_pclmulqdq()
        && EverCrypt_AutoConfig2_has_sse() && EverCrypt_AutoConfig2_has_avx()
        && EverCrypt_AutoConfig2_has_movbe();

    VALGRIND_MAKE_MEM_UNDEFINED(key, sizeof key);
    VALGRIND_MAKE_MEM_UNDEFINED(nonce, sizeof nonce);

    puts("HKDF-Expand, HMAC and Finished comparison");
    Hacl_HKDF_expand_sha2_256(derived, key, sizeof key, info, sizeof info, sizeof derived);
    Hacl_HMAC_compute_sha2_256(mac, derived, sizeof derived, transcript, sizeof transcript);
    bool equal = Tls_Util_ct_eq(mac, transcript, sizeof mac, 0, 0);
    VALGRIND_MAKE_MEM_DEFINED(&equal, sizeof equal); /* protocol declassifies equality */
    if (equal)
        return 1;

    puts("X25519 and ECDSA-P256/SHA-256");
    Hacl_Curve25519_51_secret_to_public(share, key);
    bool dh_ok = Hacl_Curve25519_51_ecdh(shared, key, peer);
    bool sign_ok = Hacl_P256_ecdsa_sign_p256_sha2(signature, sizeof transcript, transcript, key, nonce);
    VALGRIND_MAKE_MEM_DEFINED(&dh_ok, sizeof dh_ok);
    VALGRIND_MAKE_MEM_DEFINED(&sign_ok, sizeof sign_ok);
    if (!dh_ok || !sign_ok)
        return 1;

    puts("TLS ChaCha20-Poly1305 record sealing");
    if (!seal_record(3))
        return 1;
    if (aes) {
        puts("TLS AES-128-GCM record sealing");
        if (!seal_record(1))
            return 1;
    } else {
        puts("AES-128-GCM trace skipped (AES acceleration unavailable in Memcheck)");
    }
    return 0;
}
