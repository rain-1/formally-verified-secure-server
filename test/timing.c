/* Timing smoke test for the native objects linked into the x86-64 server.
 * Each experiment compares classes with the same observable outcome.
 * The test uses synthetic data and never opens sockets.
 */
#include <cpuid.h>
#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <x86intrin.h>

#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_P256.h"
#include "Tls_Conn.h"
#include "internal/Tls_Conn.h"
#include "cv_fixture.h"

enum { MAC_LEN = 32, BATCH = 32, WARMUP = 4096 };

/* Offsets from Tls.State used to seed fixtures at the extracted boundary. */
enum {
    STATE_LEN = 512, PHASE = 0, CLIENT_HS_SECRET = 8, TRANSCRIPT_HASH = 104,
    CLIENT_KEY = 136, CLIENT_SEQ = 180, SERVER_KEY = 188, SERVER_SEQ = 232,
    SUITE = 245,
};

struct stats {
    uint64_t count;
    double mean;
    double squared_diff;
};

static uint64_t rng = UINT64_C(0x73ec1a2bed509c4f);

static uint64_t next(void)
{
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
}

static uint64_t ticks(unsigned int *cpu)
{
    _mm_lfence();
    uint64_t now = __rdtscp(cpu);
    _mm_lfence();
    return now;
}

static void record(struct stats *s, double x)
{
    s->count++;
    double delta = x - s->mean;
    s->mean += delta / (double)s->count;
    s->squared_diff += delta * (x - s->mean);
}

static double report(const char *name, const struct stats s[2], unsigned batch)
{
    if (s[0].count < 2 || s[1].count < 2) {
        fprintf(stderr, "%s: insufficient same-CPU observations\n", name);
        exit(1);
    }
    double variance = 0;
    for (size_t i = 0; i < 2; i++)
        variance += s[i].squared_diff / ((double)s[i].count * (double)(s[i].count - 1));
    double t = (s[0].mean - s[1].mean) / sqrt(variance);
    printf("%-28s %9" PRIu64 " / %-9" PRIu64 "  %8.3f / %-8.3f  t=%+.3f\n",
           name, s[0].count, s[1].count, s[0].mean / batch, s[1].mean / batch, t);
    return t;
}

typedef bool (*compare_fn)(uint8_t *, uint8_t *, uint32_t, uint32_t, uint8_t);

/* A deliberately early-exiting comparison for calibration on the same data. */
static bool early_exit(uint8_t *a, uint8_t *b, uint32_t n, uint32_t i, uint8_t acc)
{
    for (; i < n; i++)
        if (a[i] != b[i])
            return false;
    return acc == 0;
}

enum comparison { POSITION_WARM, POSITION_COLD, OPERANDS_WARM };

static double compare(const char *name, compare_fn fn, enum comparison scenario, uint64_t samples)
{
    _Alignas(64) uint8_t expected[MAC_LEN] = {0};
    _Alignas(64) uint8_t got[MAC_LEN];
    struct stats groups[2] = {0};
    unsigned batch = scenario == POSITION_COLD ? 1 : BATCH;

    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        if (scenario == OPERANDS_WARM) {
            uint8_t mask = (uint8_t)(0U - group);
            for (size_t j = 0; j < sizeof expected; j++)
                expected[j] = (uint8_t)next() & mask;
        }
        memcpy(got, expected, sizeof got);
        got[scenario == OPERANDS_WARM ? MAC_LEN - 1 : group * (MAC_LEN - 1)] ^= 1;
        if (scenario == POSITION_COLD) {
            _mm_clflush(expected);
            _mm_clflush(got);
            _mm_mfence();
        }

        bool matched = false;
        unsigned cpu_before, cpu_after;
        uint64_t before = ticks(&cpu_before);
        for (unsigned j = 0; j < batch; j++)
            matched |= fn(expected, got, MAC_LEN, 0, 0);
        uint64_t after = ticks(&cpu_after);
        if (matched) {
            fprintf(stderr, "%s: comparison accepted a mismatch\n", name);
            exit(1);
        }
        if (i >= WARMUP && cpu_before == cpu_after && after >= before)
            record(&groups[group], (double)(after - before));
    }
    return report(name, groups, batch);
}

static void finished(const char *name, uint8_t suite, bool aes, uint64_t samples)
{
    /* Initialize the state fields used by check_cfin. See Tls.State for offsets. */
    uint8_t state[STATE_LEN];
    Tls_Conn_init(state, aes);
    state[PHASE] = 1;
    state[SUITE] = suite;
    memset(state + CLIENT_HS_SECRET, 0x53, MAC_LEN);
    memset(state + TRANSCRIPT_HASH, 0x79, MAC_LEN);

    uint8_t label[] = { 0, MAC_LEN, 14, 't', 'l', 's', '1', '3', ' ',
                        'f', 'i', 'n', 'i', 's', 'h', 'e', 'd', 0 };
    uint8_t key[MAC_LEN], expected[MAC_LEN];
    Hacl_HKDF_expand_sha2_256(key, state + CLIENT_HS_SECRET, MAC_LEN, label, sizeof label, MAC_LEN);
    Hacl_HMAC_compute_sha2_256(expected, key, MAC_LEN, state + TRANSCRIPT_HASH, MAC_LEN);

    _Alignas(64) uint8_t inner[16640] = {20, 0, 0, MAC_LEN};
    uint8_t out[20480];
    uint32_t result[4];
    struct stats groups[2] = {0};

    memcpy(inner + 4, expected, MAC_LEN);
    uint8_t matched_state[sizeof state];
    memcpy(matched_state, state, sizeof state);
    Tls_Conn_check_cfin(matched_state, inner, out, result, 58);
    if (matched_state[PHASE] != 2 || result[3] != 0) {
        fprintf(stderr, "%s: fixture failed to accept the reference Finished\n", name);
        exit(1);
    }

    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        memcpy(inner + 4, expected, MAC_LEN);
        inner[4 + group * (MAC_LEN - 1)] ^= 1;
        memset(state + SERVER_SEQ, 0, 8);

        unsigned cpu_before, cpu_after;
        uint64_t before = ticks(&cpu_before);
        Tls_Conn_check_cfin(state, inner, out, result, 58);
        uint64_t after = ticks(&cpu_after);
        if (state[PHASE] != 1 || result[0] != 58 || result[1] != 24
            || result[2] != 0 || result[3] != 1) {
            fprintf(stderr, "%s: comparison did not take the expected rejection path\n", name);
            exit(1);
        }
        if (i >= WARMUP && cpu_before == cpu_after && after >= before)
            record(&groups[group], (double)(after - before));
    }
    report(name, groups, 1);
}

static void record_open(const char *name, uint8_t suite, bool aes, uint64_t samples)
{
    enum { HEADER = 5, RECORD_OVERHEAD = HEADER + 1 + 16 };
    uint8_t state[STATE_LEN], key[32];
    uint8_t plaintext[1024] = {0x53}, record_bytes[20480], inner[16640], content_type;
    struct stats groups[2] = {0};
    Tls_Conn_init(state, aes);
    state[PHASE] = 2;
    state[SUITE] = suite;

    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        uint8_t mask = (uint8_t)(0U - group);
        for (size_t j = 0; j < sizeof key; j++)
            key[j] = (uint8_t)next() & mask;

        /* Repeat an identical nonce, plaintext and record length in a synthetic fixture. */
        memcpy(state + SERVER_KEY, key, sizeof key);
        memcpy(state + CLIENT_KEY, key, sizeof key);
        memset(state + SERVER_SEQ, 0, 8);
        memset(state + CLIENT_SEQ, 0, 8);
        uint32_t length = Tls_Conn_seal_app(state, plaintext, sizeof plaintext, record_bytes);
        if (length != sizeof plaintext + RECORD_OVERHEAD) {
            fprintf(stderr, "%s: fixture produced an unexpected record length\n", name);
            exit(1);
        }

        unsigned cpu_before, cpu_after;
        uint64_t before = ticks(&cpu_before);
        uint32_t opened = Tls_Conn_open_rec(state, record_bytes, length - HEADER, inner, &content_type);
        uint64_t after = ticks(&cpu_after);
        if (opened != sizeof plaintext || content_type != 23 || memcmp(inner, plaintext, sizeof plaintext)) {
            fprintf(stderr, "%s: fixture failed to open an authenticated record\n", name);
            exit(1);
        }
        if (i >= WARMUP && cpu_before == cpu_after && after >= before)
            record(&groups[group], (double)(after - before));
    }
    report(name, groups, 1);
}

static void key_exchange(uint64_t samples)
{
    const char *name = "X25519 exchange";
    uint8_t peer_scalar[32] = {19}, peer[32];
    uint8_t scalar[32], public_share[32], shared[32], peer_shared[32];
    struct stats groups[2] = {0};
    Hacl_Curve25519_51_secret_to_public(peer, peer_scalar);

    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        uint8_t mask = (uint8_t)(0U - group);
        for (size_t j = 0; j < sizeof scalar; j++)
            scalar[j] = (uint8_t)next() & mask;

        /* The server generates its public share and shared secret in this order. */
        unsigned cpu_before, cpu_after;
        uint64_t before = ticks(&cpu_before);
        Hacl_Curve25519_51_secret_to_public(public_share, scalar);
        bool ok = Hacl_Curve25519_51_ecdh(shared, scalar, peer);
        uint64_t after = ticks(&cpu_after);

        if (!ok || !Hacl_Curve25519_51_ecdh(peer_shared, peer_scalar, public_share)
            || memcmp(shared, peer_shared, sizeof shared)) {
            fprintf(stderr, "%s: peers did not agree on a shared secret\n", name);
            exit(1);
        }
        if (i >= WARMUP && cpu_before == cpu_after && after >= before)
            record(&groups[group], (double)(after - before));
    }
    report(name, groups, 1);
}

static void signing_scalar(uint8_t scalar[32], uint8_t mask)
{
    for (size_t j = 0; j < 32; j++)
        scalar[j] = (uint8_t)next() & mask;
    scalar[0] &= 0x7f;  /* Below the P-256 order. */
    scalar[31] |= 1;    /* Nonzero. */
}

static void signing(const char *name, bool vary_nonce, uint64_t samples)
{
    uint8_t message[130] = {0}, signature[64];
    uint8_t key[32] = {[31] = 1}, nonce[32] = {[31] = 1};
    uint8_t *scalar = vary_nonce ? nonce : key;
    struct stats groups[2] = {0};

    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        signing_scalar(scalar, (uint8_t)(0U - group));

        unsigned cpu_before, cpu_after;
        uint64_t before = ticks(&cpu_before);
        bool ok = Hacl_P256_ecdsa_sign_p256_sha2(signature, sizeof message, message, key, nonce);
        uint64_t after = ticks(&cpu_after);
        if (!ok) {
            fprintf(stderr, "%s: signing fixture failed\n", name);
            exit(1);
        }
        if (i >= WARMUP && cpu_before == cpu_after && after >= before)
            record(&groups[group], (double)(after - before));
    }
    report(name, groups, 1);
}

/* The integer lengths and presence of sign bytes describe the DER encoding path. */
static uint32_t certificate_verify_shape(const uint8_t *transcript, size_t length)
{
    const uint8_t *message = transcript;
    while (length >= 4) {
        size_t body = ((size_t)message[1] << 16) | ((size_t)message[2] << 8) | message[3];
        if (body > length - 4)
            return 0;
        if (message[0] == 15) {
            if (body < 12 || body > 76 || message[4] != 4 || message[5] != 3
                || message[6] != 0 || message[7] != body - 4)
                return 0;
            const uint8_t *der = message + 8;
            if (der[0] != 0x30 || der[1] != body - 6 || der[2] != 0x02)
                return 0;
            unsigned r_len = der[3];
            if (!r_len || r_len > 33 || body < 11 + r_len || der[4 + r_len] != 0x02)
                return 0;
            unsigned s_len = der[5 + r_len];
            if (!s_len || s_len > 33 || body != 10 + r_len + s_len)
                return 0;
            return (r_len << 16) | (s_len << 8) | ((der[4] == 0) << 1) | (der[6 + r_len] == 0);
        }
        length -= 4 + body;
        message += 4 + body;
    }
    return 0;
}

struct cv_trial {
    uint8_t state[STATE_LEN], transcript[CV_TRANSCRIPT_CAPACITY], hello[CV_HELLO_CAPACITY];
    uint8_t chain[1], key[32], random[96], out[20480], app[1];
    uint32_t hello_length, result[4];
};

struct cv_sample {
    uint64_t elapsed;
    uint32_t flight_length, der_shape;
};

static struct cv_sample cv_sample(struct cv_trial *trial)
{
    Tls_Conn_init(trial->state, false);
    unsigned cpu_before, cpu_after;
    uint64_t before = ticks(&cpu_before);
    Tls_Conn_input(trial->state, trial->transcript, trial->chain, sizeof trial->chain, trial->key,
        trial->random, trial->hello, trial->hello_length, trial->out, trial->app, sizeof trial->app,
        trial->result);
    uint64_t after = ticks(&cpu_after);

    size_t length = cv_transcript_length(trial->state);
    if (trial->state[PHASE] != 1 || trial->result[0] != trial->hello_length || !trial->result[1]
        || trial->result[2] || trial->result[3] || length > sizeof trial->transcript) {
        fputs("CertificateVerify timing fixture did not produce a server flight\n", stderr);
        exit(1);
    }
    uint32_t shape = certificate_verify_shape(trial->transcript, length);
    if (!shape) {
        fputs("CertificateVerify timing fixture produced invalid framing\n", stderr);
        exit(1);
    }
    uint64_t elapsed = cpu_before == cpu_after && after >= before ? after - before : 0;
    return (struct cv_sample){elapsed, trial->result[1], shape};
}

static void certificate_verify(const char *name, bool vary_nonce, uint64_t samples)
{
    enum { POOL_SIZE = 128, MAX_CANDIDATES = 4096 };
    struct cv_trial trial = {.key = {[31] = 42}, .random = {[63] = 7, [95] = 19}};
    trial.hello_length = read_cv_client_hello(trial.hello);
    if (!trial.hello_length) {
        fputs("CertificateVerify timing fixture could not read test/clienthello.bin\n", stderr);
        exit(1);
    }

    uint8_t fixed[32], pool[POOL_SIZE][32];
    uint8_t *scalar = vary_nonce ? trial.random + 64 : trial.key;
    memcpy(fixed, scalar, sizeof fixed);
    struct cv_sample reference = cv_sample(&trial);
    size_t count = 0;
    for (size_t i = 0; i < MAX_CANDIDATES && count < POOL_SIZE; i++) {
        signing_scalar(scalar, 0xff);
        struct cv_sample candidate = cv_sample(&trial);
        if (candidate.flight_length == reference.flight_length && candidate.der_shape == reference.der_shape)
            memcpy(pool[count++], scalar, sizeof fixed);
    }
    if (count != POOL_SIZE) {
        fprintf(stderr, "%s: insufficient candidates with matching DER and flight lengths\n", name);
        exit(1);
    }

    struct stats groups[2] = {0};
    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        const uint8_t *candidate = pool[next() % POOL_SIZE];
        uint8_t mask = (uint8_t)(0U - group);
        for (size_t j = 0; j < sizeof fixed; j++)
            scalar[j] = (fixed[j] & (uint8_t)~mask) | (candidate[j] & mask);

        struct cv_sample sample = cv_sample(&trial);
        if (sample.flight_length != reference.flight_length || sample.der_shape != reference.der_shape) {
            fprintf(stderr, "%s: CertificateVerify output shape changed\n", name);
            exit(1);
        }
        if (i >= WARMUP && sample.elapsed)
            record(&groups[group], (double)sample.elapsed);
    }
    report(name, groups, 1);
}

int main(int argc, char **argv)
{
    uint64_t samples = 500000;
    if (argc == 2) {
        char *end;
        errno = 0;
        samples = strtoull(argv[1], &end, 10);
        if (errno || *end != '\0' || samples < 10000 || samples > 100000000)
            return fprintf(stderr, "samples must be in [10000, 100000000]\n"), 2;
    } else if (argc != 1) {
        return fprintf(stderr, "usage: %s [samples per experiment]\n", argv[0]), 2;
    }

    unsigned a, b, c, d;
    if (!__get_cpuid(0x80000001, &a, &b, &c, &d) || !(d & (1U << 27))) {
        fputs("timing tests require x86-64 RDTSCP\n", stderr);
        return 2;
    }
    bool flush = __get_cpuid(1, &a, &b, &c, &d) && (d & (1U << 19));
    EverCrypt_AutoConfig2_init();
    bool aes = EverCrypt_AutoConfig2_has_aesni() && EverCrypt_AutoConfig2_has_pclmulqdq()
        && EverCrypt_AutoConfig2_has_sse() && EverCrypt_AutoConfig2_has_avx()
        && EverCrypt_AutoConfig2_has_movbe();

    puts("Experiment                    Class 0 / Class 1          TSC ticks/call       Welch t");
    double control = compare("early-exit control", early_exit, POSITION_WARM, samples);
    if (!isfinite(control) || fabs(control) < 5) {
        fputs("timing calibration did not distinguish the early-exit control\n", stderr);
        return 1;
    }
    compare("MAC position, warm", Tls_Util_ct_eq, POSITION_WARM, samples);
    compare("MAC operands, warm", Tls_Util_ct_eq, OPERANDS_WARM, samples);
    if (flush)
        compare("MAC position, flushed", Tls_Util_ct_eq, POSITION_COLD, samples);
    else
        puts("MAC position, flushed: skipped (CLFLUSH unavailable)");
    finished("Finished reject, ChaCha20", 3, aes, samples);
    if (aes)
        finished("Finished reject, AES-GCM", 1, aes, samples);
    else
        puts("Finished reject, AES-GCM: skipped (AES acceleration unavailable)");
    record_open("Open record, ChaCha20", 3, aes, samples);
    if (aes)
        record_open("Open record, AES-GCM", 1, aes, samples);
    else
        puts("Open record, AES-GCM: skipped (AES acceleration unavailable)");
    key_exchange(samples / 10);
    signing("P-256 signing key", false, samples / 10);
    signing("P-256 signing nonce", true, samples / 10);
    certificate_verify("CertificateVerify key", false, samples / 10);
    certificate_verify("CertificateVerify nonce", true, samples / 10);
    return 0;
}
