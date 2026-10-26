/*
 * Command line demo / benchmark for the BCH (511, 385, 14) code.
 *
 *   ./m17_bch        encode and decode 100000 codewords, 14 bit errors each
 *   ./m17_bch 5      same, but with 5 bit errors per codeword
 *
 * Prints the number of failed codewords, the duration and the equivalent
 * payload bit rate. Built as part of the CMake project, or by hand:
 *
 *   g++ -O2 -I src src/demo.cpp src/m17_bch.cpp -o m17_bch
 */
#include "m17_bch.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <chrono>

//
// Deterministic PRNG: the same run reproduces the same test data, so a failure
// can be re-run exactly. The original used rand() without seeding.
//
static uint32_t g_state = 0x20220612u;
static uint32_t xs32(void) {
    g_state ^= g_state << 13;
    g_state ^= g_state >> 17;
    g_state ^= g_state << 5;
    return g_state;
}

//
// Flip exactly n distinct positions. Picking with replacement (as this demo
// used to) silently cancels some of the errors, so "14 errors" was really
// 14 errors only about 84% of the time.
//
static void add_errors(uint8_t *bits, int n) {
    int used[BCH_N] = {0};
    int placed = 0;
    while (placed < n) {
        int p = (int)(xs32() % BCH_N);
        if (!used[p]) {
            used[p] = 1;
            bits[p] ^= 1;
            placed++;
        }
    }
}

static bool one_codeword(int n_errors) {
    uint8_t bits[BCH_N];
    for (int i = 0; i < BCH_K; i++) bits[i] = (uint8_t)(xs32() & 1);

    m17_bch_encode(bits);
    add_errors(bits, n_errors);
    m17_bch_decode(bits);
    return m17_bch_check(bits);
}

static void test(int m) {
    const int n = 100000;
    const float d = 100.0f / n;

    printf("Start of BCH test %d errors per frame\n", m);

    int fails = 0;
    auto start = std::chrono::steady_clock::now();
    for (int i = 0; i < n; i++) {
        if (!one_codeword(m)) fails++;
    }
    auto end = std::chrono::steady_clock::now();

    double secs = std::chrono::duration<double>(end - start).count();

    printf("Number Failed codewords %d, percentage failure %.2f\n", fails, fails * d);
    printf("Duration of test %.2f secs\n", secs);
    printf("Number of 511 bit codewords received %d\n", n);
    printf("Equivalent bitrate %.2f Mbs\n", (n * BCH_K) / (secs * 1000000.0));
}

int main(int argc, char **argv) {
    m17_bch_init();

    int m = 14;
    if (argc == 2) m = atoi(argv[1]);
    if (m < 0) m = 0;
    if (m > BCH_T) m = BCH_T;

    test(m);
    return 0;
}
