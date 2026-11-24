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
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_P256.h"
#include "Tls_Conn.h"
#include "internal/Tls_Conn.h"

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

static void signing(const char *name, bool vary_nonce, uint64_t samples)
{
    uint8_t message[130] = {0}, signature[64];
    uint8_t key[32] = {[31] = 1}, nonce[32] = {[31] = 1};
    uint8_t *scalar = vary_nonce ? nonce : key;
    struct stats groups[2] = {0};

    for (uint64_t i = 0; i < samples + WARMUP; i++) {
        unsigned group = next() & 1U;
        uint8_t mask = (uint8_t)(0U - group);
        for (size_t j = 0; j < sizeof key; j++)
            scalar[j] = (uint8_t)next() & mask;
        scalar[0] &= 0x7f;    /* Below the P-256 order. */
        scalar[31] |= 1;      /* Nonzero. */

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
    signing("P-256 signing key", false, samples / 10);
    signing("P-256 signing nonce", true, samples / 10);
    return 0;
}
