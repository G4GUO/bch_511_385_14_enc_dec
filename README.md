# bch_511_385_14_enc_dec

Encoder and decoder for the **BCH (511, 385, 14)** code, plus a small simulator/demo
that encodes a codeword, injects a known number of bit errors and decodes it again.

Portable C++ with no dependencies: one translation unit, one header, no allocations
after `m17_bch_init()`.

## Code parameters

| | |
|---|---|
| Length | n = 511 bits |
| Message | k = 385 bits |
| Parity | n - k = 126 bits |
| Field | GF(2^9), primitive polynomial **p(x) = x^9 + x^5 + 1** |
| Generator | g(x) = product of the minimal polynomials of α^1, α^3 … α^27 (degree 126) |
| Correction | up to **t = 14** bit errors per codeword |
| Detection | 15 or more errors is reported as uncorrectable (d_min = 29) |

The bit order matters and is fixed by this implementation:

* words are **one bit per byte**, values 0 or 1, length `BCH_N`;
* index 0 is the **first transmitted bit and the highest-order coefficient**;
* encoding is systematic: it writes the 126 parity bits into
  `inout[BCH_K … BCH_N-1]` and leaves `inout[0 … BCH_K-1]` untouched.

A different primitive polynomial produces a code with the same parameters but
different codewords, so it will **not** interoperate with this one. If you change
`p(x)` you must change the 14 base polynomials with it.

## API

```c
#include "m17_bch.h"

m17_bch_init();                  /* once, before anything else              */
m17_bch_encode(bits);            /* bitwise reference encoder               */
m17_bch_encode_fast(bits);       /* table driven, ~40% faster               */
m17_bch_check(bits);             /* true if the 511 bits are a valid word   */
int r = m17_bch_decode(bits);    /* correct in place                        */
```

`m17_bch_decode()` returns:

| value | meaning |
|---|---|
| 0 | word was already valid, buffer untouched |
| > 0 | number of bit errors corrected; buffer is now a valid codeword |
| -1 | uncorrectable; **buffer is unchanged**, treat the block as erased |

All functions are reentrant: the decoder keeps its working state on the stack
(roughly 1 kB), so it can be called from several threads or from an ISR.

## Building

CMake (recommended):

```sh
cmake -S . -B build
cmake --build build
ctest --test-dir build --output-on-failure
./build/m17_bch 14
```

Or by hand:

```sh
g++ -O2 -Isrc src/demo.cpp src/m17_bch.cpp -o m17_bch
```

The original Eclipse-generated makefile is still there and still works:

```sh
cd Release && make && ./m17_bch
```

## Running the demo

```sh
./m17_bch        # 100000 codewords, 14 bit errors each
./m17_bch 5      # same, with 5 bit errors per codeword
```

Each iteration generates a random message, encodes it, flips exactly *n* distinct
bits and decodes. The summary reports failed codewords, wall time and the
equivalent payload bit rate.

Example output, CMake `Release` build (`-O3`):

```
Start of BCH test 14 errors per frame
Number Failed codewords 0, percentage failure 0.00
Duration of test 1.73 secs
Number of 511 bit codewords received 100000
Equivalent bitrate 22.29 Mbs
```

Rough throughput on the same machine (`-O2`, one core):

| operation | rate |
|---|---|
| encode | 425 000 codewords/s (163 Mbit/s of payload) |
| decode, no errors | 2 240 000 codewords/s |
| decode, 14 errors | 65 000 codewords/s (25.1 Mbit/s) |

Correction only runs when the received word is invalid, so decode speed is not
constant — a clean channel is about 34x faster than a fully loaded one.

## Tests

`tests/test_bch.cpp` (run via `ctest`) checks:

* three known-answer vectors: 385-bit message → 511-bit codeword;
* a known 6-bit error pattern is corrected back to the exact codeword;
* round trips at every error count 0 … 14, with *distinct* positions;
* 15 … 29 errors are reported as uncorrectable and leave the buffer untouched;
* the two encoders agree bit for bit;
* `m17_bch_check()` rejects words with 1 … 5 errors.

The known-answer vectors were produced by an independent GF(2^9) reference
implementation and agree with this code bit for bit, which is what pins the code
down to a specific polynomial and bit ordering rather than merely being
self-consistent.

## Memory

`m17_bch_init()` builds a 512 kB multiply table (`m_mult`) plus a few small
tables: about **520 kB of static RAM in total**. That is fine on a PC and too much
for a small microcontroller. Commenting out the `#define __LUT__` in
`m17_bch.cpp` drops the big table and multiplies in software instead: slower, and
far smaller. A log/antilog multiply would be a better middle ground if you need
both.

## Licence

Public domain, as stated in the original source header — see `LICENSE`
(Unlicense).

## Provenance

The code, and the original single-file demo, were written by **C.H. Brain, G4GUO**
in June 2022.

This branch is a maintenance contribution by **Hermes Agent** (an AI agent built by
Nous Research), prepared at G4GUO's request and reviewed by him before merge. It
splits the program into a library plus a demo, adds the header, tests, CMake build,
`.gitignore`/licence files and this documentation, makes the decoder reentrant and
fixes the error injection in the demo. The DSP and algebraic core is unchanged.
Commits on this branch are authored by `Hermes Agent <agent@localhost>` so their
origin stays visible in the history.
