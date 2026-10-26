/*
 * BCH (511, 385, 14) encoder and decoder - public interface.
 *
 * Code parameters
 *   n = 511, k = 385, n-k = 126 parity bits, m = 9, t = 14
 *   field          GF(2^9)
 *   primitive poly p(x) = x^9 + x^5 + 1        (0x21 low-order field element)
 *   generator      g(x) = product of the minimal polynomials of
 *                  alpha^1, alpha^3, ... alpha^27  (degree 126)
 *
 * Bit ordering contract
 *   Words are held as one bit per byte, values 0 or 1, length BCH_N.
 *   Index 0 is the first transmitted bit and the highest-order coefficient.
 *   Encoding writes the 126 parity bits into inout[BCH_K .. BCH_N-1], so a
 *   codeword is the message followed by its parity, both MSB first.
 *   This is a systematic code: the first BCH_K bits are unchanged by encoding.
 *
 * Return value of bch511385_decode()
 *    0   codeword was already valid, buffer untouched
 *   >0   number of bit errors corrected, buffer now holds a valid codeword
 *   -1   uncorrectable: the decoder gave up and the buffer is UNCHANGED.
 *        Treat the block as erased; do not trust the data.
 *
 * Threading / reentrancy
 *   All functions are reentrant and safe to call from multiple threads or an
 *   ISR once bch511385_init() has completed. Decoding uses roughly 1 kB of stack.
 *
 * Written by C.H. Brain G4GUO, 12 June 2022. Public domain, no copyright.
 */
#ifndef BCH511385_H
#define BCH511385_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define BCH_N   511              /* codeword length in bits            */
#define BCH_K   385              /* message length in bits             */
#define BCH_NK  (BCH_N - BCH_K)  /* 126 parity bits                    */
#define BCH_M   9                /* GF(2^9), so n = 2^9 - 1            */
#define BCH_T   14               /* correctable errors per codeword    */

/* Build the Galois and lookup tables. Call once, before any other function.
 * Takes about 1.2 ms on a modern x86-64 and allocates roughly 520 kB of
 * static RAM (almost all of it the 512 kB multiply table; see the note in
 * the README if that is too much for your target). */
void bch511385_init(void);

/* Bitwise encoder. Slow path, no tables, useful as a reference. */
void bch511385_encode(uint8_t *inout);

/* Table-driven encoder, about 40% faster than bch511385_encode(). */
void bch511385_encode_fast(uint8_t *inout);

/* Return true if the BCH_N bits form a valid codeword. Does not modify them. */
bool bch511385_check(const uint8_t *in);

/* Correct up to BCH_T bit errors in place. See return values above. */
int bch511385_decode(uint8_t *inout);

#ifdef __cplusplus
}
#endif

#endif /* BCH511385_H */
