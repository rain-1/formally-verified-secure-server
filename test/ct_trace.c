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
#include "Hacl_Hash_SHA2.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_P256.h"
#include "Tls_Conn.h"
#include "internal/Tls_Conn.h"
#include "cv_fixture.h"

/* Offsets from Tls.State for the extracted connection fixture. */
enum { STATE_LEN = 512, PHASE = 0, CLIENT_KEY = 136, CLIENT_IV = 168, CLIENT_SEQ = 180,
       SERVER_KEY = 188, SERVER_IV = 220, SUITE = 245 };

enum { HEADER_LEN = 5, TAG_LEN = 16, CONTENT_LEN = 128, PADDING_LEN = 16,
       INNER_LEN = CONTENT_LEN + 1, BODY_LEN = INNER_LEN + TAG_LEN,
       RECORD_LEN = HEADER_LEN + BODY_LEN };

static const char cv_context[] = "TLS 1.3, server CertificateVerify";
enum { CV_SPACES = 64, CV_HASH = 32, CV_INPUT_LEN = CV_SPACES + sizeof cv_context + CV_HASH };

bool __real_Hacl_P256_ecdsa_sign_p256_sha2(uint8_t *signature, uint32_t length, uint8_t *input,
    uint8_t *key, uint8_t *nonce);

bool __wrap_Hacl_P256_ecdsa_sign_p256_sha2(uint8_t *signature, uint32_t length, uint8_t *input,
    uint8_t *key, uint8_t *nonce)
{
    bool ok = __real_Hacl_P256_ecdsa_sign_p256_sha2(signature, length, input, key, nonce);
    if (length == CV_INPUT_LEN) {
        /* The peer receives the signature. Keep the signing key and nonce tainted. */
        VALGRIND_MAKE_MEM_DEFINED(&ok, sizeof ok);
        if (ok)
            VALGRIND_MAKE_MEM_DEFINED(signature, 64);
    }
    return ok;
}

static bool check_certificate_verify(uint8_t *transcript, size_t length, uint8_t *public_key)
{
    enum { CV_HEADER_LEN = 8, DER_LEN = 70, FINISHED_LEN = 36, R_LEN = 33, S_LEN = 31 };
    const uint8_t cv_header[CV_HEADER_LEN] = {15, 0, 0, 4 + DER_LEN, 4, 3, 0, DER_LEN};
    const uint8_t der_prefix[] = {0x30, DER_LEN - 2, 0x02, R_LEN, 0};
    const uint8_t s_header[] = {0x02, S_LEN};
    const uint8_t finished_header[] = {20, 0, 0, CV_HASH};
    if (length < CV_HEADER_LEN + DER_LEN + FINISHED_LEN)
        return false;

    size_t prefix_length = length - CV_HEADER_LEN - DER_LEN - FINISHED_LEN;
    uint8_t *cv = transcript + prefix_length;
    uint8_t *der = cv + CV_HEADER_LEN;
    uint8_t *r = der + sizeof der_prefix;
    uint8_t *s_tag = r + 32;
    uint8_t *s_bytes = s_tag + sizeof s_header;
    if (memcmp(cv, cv_header, sizeof cv_header) || memcmp(der, der_prefix, sizeof der_prefix)
        || memcmp(s_tag, s_header, sizeof s_header) || memcmp(der + DER_LEN, finished_header, sizeof finished_header)
        || r[0] < 0x80 || s_bytes[0] == 0 || s_bytes[0] >= 0x80)
        return false;

    uint8_t input[CV_INPUT_LEN], s[32] = {0};
    memset(input, ' ', CV_SPACES);
    memcpy(input + CV_SPACES, cv_context, sizeof cv_context);
    Hacl_Hash_SHA2_hash_256(input + CV_SPACES + sizeof cv_context, transcript, (uint32_t)prefix_length);
    memcpy(s + 1, s_bytes, S_LEN);
    return Hacl_P256_ecdsa_verif_p256_sha2(sizeof input, input, public_key, r, s);
}

static bool trace_certificate_verify(void)
{
    uint8_t state[STATE_LEN], transcript[CV_TRANSCRIPT_CAPACITY], hello[CV_HELLO_CAPACITY], out[20480], app[1];
    uint8_t chain[1] = {0}, key[32] = {[31] = 42}, public_key[64];
    /* This nonce gives a signature with a 33-byte DER r and a 31-byte DER s. */
    uint8_t random[96] = {[63] = 7, [94] = 0x04, [95] = 0x9a};
    uint32_t result[4];
    uint32_t hello_length = read_cv_client_hello(hello);
    if (!hello_length || !Hacl_P256_dh_initiator(public_key, key))
        return false;

    Tls_Conn_init(state, false);
    VALGRIND_MAKE_MEM_UNDEFINED(key, sizeof key);
    VALGRIND_MAKE_MEM_UNDEFINED(random + 64, 32);
    Tls_Conn_input(state, transcript, chain, sizeof chain, key, random, hello, hello_length,
        out, app, sizeof app, result);
    size_t length = cv_transcript_length(state);
    return state[PHASE] == 1 && result[0] == hello_length && result[1] > 0 && result[2] == 0 && result[3] == 0
        && length <= sizeof transcript && check_certificate_verify(transcript, length, public_key);
}

static bool make_record(bool aes, uint8_t *key, const uint8_t *iv, uint8_t seq,
    uint8_t inner[INNER_LEN], uint8_t record[RECORD_LEN])
{
    const uint8_t header[HEADER_LEN] = {23, 3, 3, 0, BODY_LEN};
    uint8_t nonce[12];
    memcpy(record, header, sizeof header);
    memcpy(nonce, iv, sizeof nonce);
    nonce[11] ^= seq;

    uint8_t *cipher = record + HEADER_LEN;
    uint8_t *tag = cipher + INNER_LEN;
    if (aes)
        return EverCrypt_AEAD_encrypt_expand_aes128_gcm(key, nonce, sizeof nonce,
            record, HEADER_LEN, inner, INNER_LEN, cipher, tag) == EverCrypt_Error_Success;
    Hacl_AEAD_Chacha20Poly1305_encrypt(cipher, tag, inner, INNER_LEN, record, HEADER_LEN, key, nonce);
    return true;
}

static bool open_fixture(uint8_t *state, uint8_t record[RECORD_LEN], const uint8_t inner[INNER_LEN],
    uint32_t expected_length, uint8_t expected_type, uint8_t next_sequence)
{
    uint8_t opened[16640], type = 0;
    const uint8_t next_seq[8] = {[7] = next_sequence};
    memset(opened, 0xff, INNER_LEN);
    uint32_t content_length = Tls_Conn_open_rec(state, record, BODY_LEN, opened, &type);

    /* Clear taint only after the extracted code has found the inner content type. */
    VALGRIND_MAKE_MEM_DEFINED(opened, INNER_LEN);
    VALGRIND_MAKE_MEM_DEFINED(&type, sizeof type);
    VALGRIND_MAKE_MEM_DEFINED(&content_length, sizeof content_length);
    return content_length == expected_length && type == expected_type
        && memcmp(opened, inner, INNER_LEN) == 0
        && memcmp(state + CLIENT_SEQ, next_seq, sizeof next_seq) == 0;
}

static bool trace_record(uint8_t suite)
{
    uint8_t state[STATE_LEN], plaintext[CONTENT_LEN] = {23}, record[20480];
    uint8_t inner[INNER_LEN] = {23, [CONTENT_LEN] = 23};
    uint8_t padded_inner[INNER_LEN] = {23, [CONTENT_LEN - PADDING_LEN] = 22};
    uint8_t all_padding[INNER_LEN] = {0};
    uint8_t expected[RECORD_LEN], padded[RECORD_LEN], malformed[RECORD_LEN];
    bool aes = suite == 1;
    Tls_Conn_init(state, aes);
    state[PHASE] = 2;
    state[SUITE] = suite;
    state[SERVER_KEY] = 42;
    state[SERVER_IV] = 19;
    memcpy(state + CLIENT_KEY, state + SERVER_KEY, 32);
    memcpy(state + CLIENT_IV, state + SERVER_IV, 12);

    /* Keep the wire size fixed while shifting the type and padding inside the record. */
    if (!make_record(aes, state + CLIENT_KEY, state + CLIENT_IV, 0, inner, expected)
        || !make_record(aes, state + CLIENT_KEY, state + CLIENT_IV, 1, padded_inner, padded)
        || !make_record(aes, state + CLIENT_KEY, state + CLIENT_IV, 2, all_padding, malformed))
        return false;

    VALGRIND_MAKE_MEM_UNDEFINED(state + SERVER_KEY, 32);
    VALGRIND_MAKE_MEM_UNDEFINED(state + SERVER_IV, 12);
    VALGRIND_MAKE_MEM_UNDEFINED(plaintext, sizeof plaintext);
    uint32_t length = Tls_Conn_seal_app(state, plaintext, sizeof plaintext, record);
    if (length != sizeof expected)
        return false;
    VALGRIND_MAKE_MEM_DEFINED(record, sizeof expected); /* wire bytes are public */
    if (memcmp(record, expected, sizeof expected) != 0)
        return false;

    uint8_t opened[16640], type = 0;
    const uint8_t initial_seq[8] = {0};
    VALGRIND_MAKE_MEM_UNDEFINED(state + CLIENT_KEY, 32);
    VALGRIND_MAKE_MEM_UNDEFINED(state + CLIENT_IV, 12);

    expected[HEADER_LEN + INNER_LEN] ^= 1;
    uint32_t rejected = Tls_Conn_open_rec(state, expected, BODY_LEN, opened, &type);
    VALGRIND_MAKE_MEM_DEFINED(&rejected, sizeof rejected);
    if (rejected != UINT32_MAX || type != 0 || memcmp(state + CLIENT_SEQ, initial_seq, sizeof initial_seq))
        return false;
    expected[HEADER_LEN + INNER_LEN] ^= 1;

    return open_fixture(state, expected, inner, CONTENT_LEN, 23, 1)
        && open_fixture(state, padded, padded_inner, CONTENT_LEN - PADDING_LEN, 22, 2)
        && open_fixture(state, malformed, all_padding, UINT32_MAX - 1, 0, 3);
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

    puts("TLS CertificateVerify signing and DER serialization");
    if (!trace_certificate_verify()) {
        fputs("TLS CertificateVerify fixture failed\n", stderr);
        return 1;
    }

    puts("TLS ChaCha20-Poly1305 record sealing and opening");
    if (!trace_record(3)) {
        fputs("ChaCha20-Poly1305 record fixture failed\n", stderr);
        return 1;
    }
    if (aes) {
        puts("TLS AES-128-GCM record sealing and opening");
        if (!trace_record(1)) {
            fputs("AES-128-GCM record fixture failed\n", stderr);
            return 1;
        }
    } else {
        puts("AES-128-GCM trace skipped (AES acceleration unavailable in Memcheck)");
    }
    return 0;
}
