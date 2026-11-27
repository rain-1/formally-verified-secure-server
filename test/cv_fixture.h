#ifndef SWS_CV_FIXTURE_H
#define SWS_CV_FIXTURE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

enum { CV_HELLO_CAPACITY = 4105, CV_TRANSCRIPT_CAPACITY = 20480, CV_TRANSCRIPT_LENGTH_OFFSET = 240 };

static inline uint32_t read_cv_client_hello(uint8_t hello[CV_HELLO_CAPACITY])
{
    FILE *fixture = fopen("test/clienthello.bin", "rb");
    if (!fixture)
        return 0;
    size_t length = fread(hello, 1, CV_HELLO_CAPACITY, fixture);
    bool read_ok = feof(fixture) && !ferror(fixture);
    fclose(fixture);
    return read_ok ? (uint32_t)length : 0;
}

static inline size_t cv_transcript_length(const uint8_t *state)
{
    return state[CV_TRANSCRIPT_LENGTH_OFFSET] + 256u * state[CV_TRANSCRIPT_LENGTH_OFFSET + 1];
}

#endif
