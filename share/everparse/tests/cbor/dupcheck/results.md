# Verified duplicate map key checks for EverCBOR nondet: results

This directory tests and benchmarks the three verified duplicate map key checks
of the EverCBOR non-deterministic API. All three accept exactly the same inputs
(well-formed CBOR, no duplicate map keys at any depth, map depth ≤ D, map length ≤ N),
and none of them allocates.

| variant | entry point | scratch provided by the caller | key comparisons |
|---|---|---|---|
| bounded (reference) | `cbor_nondet_parse_bounded(D, N, …)` | none | pairwise, O(N²) per map, recursive |
| sort | `cbor_nondet_parse_bounded_sort(D, N, scratch, len, …)` | `3·N·D` `size_t` | index sort of each map's entries (in-place heap sort over index triples), adjacent equality |
| hash | `cbor_nondet_parse_bounded_hash(D, N, k0, k1, scratch, len, hscratch, hlen, …)` | `3·N·D + N` `size_t` and `N` `uint64_t` | keyed SipHash-1-3 of each key (canonical: invariant under map entry order and non-minimal heads), then index sort on (hash, key); keys are compared only on equal hashes |

Additional entry points:

- `cbor_nondet_bounded_{sort,hash}_scratch_ok` check scratch sizes.
- The hash variant has unverified random-key wrappers:
  - C: `cbor_nondet_parse_bounded_hash_random` in `include/everparse/CBORNondetHashRandom.h`. It uses BCryptGenRandom, arc4random_buf or getrandom, and falls back to sort if the RNG fails.
  - Rust: `cbor_nondet_parse_bounded_hash_random`, keyed from `std`'s `RandomState`.

Hash correctness does not depend on the key: equal hashes are always confirmed
by a full comparison. The key only protects the running time against inputs
crafted to collide.

## Running

    make test        # differential tests vs. the reference, no-malloc check (--wrap)
    make test-asan   # same under ASan/UBSan
    make bench       # -> bench.csv (≈ 1.5 min)

`test_dupcheck.c` checks that all variants agree on 100,000 random inputs
plus hand-written cases. The hash variant is tested with three keys,
including the SipHash test vector key and a random key, and through the
random wrapper. It also checks rejection at scratch size − 1 and NULL
scratch handling. Rust tests are in `src/cbor/pulse/nondet/rust/tests/example.rs`
(`cargo test`).

## Benchmark setup

- Machine: AMD EPYC 7V13, gcc 13.3 `-O2`, single thread.
- Timing: median of 5 batches of ≥ 20 ms each; a single call if it takes more than 0.1 s.
- Capping: a variant is no longer run on a family's larger parameters once a single call takes more than 0.5 s (shown as —).
- `bounded` on B7_key_chain_dup only runs at t = 16: at t = 64, a single call
  did not finish in 40 minutes, because the reference compares equal nested map keys in exponential time.
- `scratch` counts `size_t` plus `uint64_t` elements.
- Families are the same as for the unverified prototypes, plus B7.
  - A1/A3: map of n integer keys (minimal / 8-byte heads).
  - A2: n byte-string keys of 256 bytes sharing a prefix.
  - A4: array of m COSE-like maps of 8 entries.
  - A5: chain of d maps nested in values.
  - B1: two equal keys, each a nested map of depth d (duplicate).
  - B2/B4: n keys, each a map of m shuffled entries differing only in their last entry (B4: with one duplicate).
  - B3: t levels of nested map keys that each need re-sorting.
  - B6: keys are arrays of k maps.
  - B7: two keys, each a chain of t single-entry maps nested in keys.

## Summary

- **Both new variants remove the reference's quadratic and exponential behaviours** that are reachable at
  bounded D, N. On A1, at N = 16384, the reference takes 4.9 s, sort 3.7 ms and hash 2.7 ms.
  On B1 at d = 20, the reference takes 762 ms, sort 27 µs and hash 149 µs.
- **Hash beats sort when key comparisons are expensive.** This covers long keys (A2), keys that are maps needing
  re-sorting (B2, B4, B6) and large maps (A1/A3 at large N, 0.5–0.6×). The gain grows with key
  size, from 0.06× on A2 to 0.08× on B2.
- **Nested re-sorting (B3) is the decisive case.** With O(D·N) memory, comparing two map keys
  re-sorts their nested maps at every level. Sort is therefore exponential in the nesting depth t, like the
  reference: 3.7 s at t = 6. Hash hashes each nested key once per enclosing map and stays near-linear in
  the input size, at 35 ms for t = 6 and 758 ms for 1.6 MB at t = 8.
- **Sort is better on small or shallow maps and on deep chains of map keys.** On A4 (COSE-like, N = 8) hash costs about
  1.5× sort; on A5 (maps in values) about 2×; on B1 (maps in keys) about 6×.
  On B7, hash costs about 10× sort when there is no duplicate and 6× with one. The hash variant
  rehashes every key once per enclosing map, which is O(D · input size): Θ(t²) on B7,
  where sort is also quadratic. Even the worst B7 case stays polynomial, at 2.7 s for a 16 KB input at
  D = 4097, an extreme setting.
- **Scratch**: hash needs N more `size_t` and N `uint64_t` than sort. Both are O(D·N), fixed by the
  bounds rather than the input, and never allocated by the library.

**Recommendation.** Use hash, with a random key, as the default for untrusted inputs that may have
maps in map keys or large maps. Use sort when D and N are small, keys are simple, and
a deterministic running time without a key is desirable. The reference remains
appropriate only for very small N with no maps in keys.

## Results (bench.csv)

#### A1_wide_int

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 33 | 1 | 16 | 5.62 µs | 1.17 µs | 1.5 µs | 1.28 | 0 | 48 / 80 |
| 64 | 170 | 1 | 64 | 84.5 µs | 6.54 µs | 6.43 µs | 0.98 | 0 | 192 / 320 |
| 256 | 747 | 1 | 256 | 1.3 ms | 33.4 µs | 23.1 µs | 0.69 | 0 | 768 / 1280 |
| 1024 | 3819 | 1 | 1024 | 21.4 ms | 183 µs | 112 µs | 0.61 | 0 | 3072 / 5120 |
| 4096 | 16107 | 1 | 4096 | 320 ms | 910 µs | 569 µs | 0.62 | 0 | 12288 / 20480 |
| 16384 | 65259 | 1 | 16384 | 4.89 s | 3.72 ms | 2.68 ms | 0.72 | 0 | 49152 / 81920 |
| 65536 | 261869 | 1 | 65536 | — | 19.2 ms | 11.9 ms | 0.62 | 0 | 196608 / 327680 |
| 262144 | 1441517 | 1 | 262144 | — | 93.6 ms | 54.6 ms | 0.58 | 0 | 786432 / 1310720 |
| 1048576 | 6160109 | 1 | 1048576 | — | 427 ms | 233 ms | 0.55 | 0 | 3145728 / 5242880 |

#### A3_wide_int_8byte

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 161 | 1 | 16 | 6.78 µs | 1.27 µs | 1.55 µs | 1.22 | 0 | 48 / 80 |
| 64 | 642 | 1 | 64 | 101 µs | 7.34 µs | 6.48 µs | 0.88 | 0 | 192 / 320 |
| 256 | 2563 | 1 | 256 | 1.53 ms | 39.8 µs | 25.8 µs | 0.65 | 0 | 768 / 1280 |
| 1024 | 10243 | 1 | 1024 | 23.6 ms | 207 µs | 106 µs | 0.51 | 0 | 3072 / 5120 |
| 4096 | 40963 | 1 | 4096 | 363 ms | 1.01 ms | 611 µs | 0.60 | 0 | 12288 / 20480 |
| 16384 | 163843 | 1 | 16384 | 5.97 s | 4.72 ms | 2.69 ms | 0.57 | 0 | 49152 / 81920 |
| 65536 | 655365 | 1 | 65536 | — | 22.7 ms | 11.9 ms | 0.52 | 0 | 196608 / 327680 |
| 262144 | 2621445 | 1 | 262144 | — | 104 ms | 52.9 ms | 0.51 | 0 | 786432 / 1310720 |
| 1048576 | 10485765 | 1 | 1048576 | — | 452 ms | 233 ms | 0.52 | 0 | 3145728 / 5242880 |

#### A2_wide_prefix_L256

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 4161 | 1 | 16 | 48.1 µs | 17.5 µs | 4.52 µs | 0.26 | 0 | 48 / 80 |
| 64 | 16642 | 1 | 64 | 714 µs | 105 µs | 18.4 µs | 0.17 | 0 | 192 / 320 |
| 256 | 66563 | 1 | 256 | 11.7 ms | 697 µs | 69.8 µs | 0.10 | 0 | 768 / 1280 |
| 1024 | 266243 | 1 | 1024 | 231 ms | 3.56 ms | 275 µs | 0.08 | 0 | 3072 / 5120 |
| 4096 | 1064963 | 1 | 4096 | 3.75 s | 17.8 ms | 1.26 ms | 0.07 | 0 | 12288 / 20480 |
| 16384 | 4259843 | 1 | 16384 | — | 86 ms | 5.57 ms | 0.06 | 0 | 49152 / 81920 |
| 65536 | 17039365 | 1 | 65536 | — | 385 ms | 21.4 ms | 0.06 | 0 | 196608 / 327680 |

#### A4_cose_like_array

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 4033 | 2 | 8 | 28.6 µs | 8.59 µs | 13.5 µs | 1.57 | 0 | 48 / 64 |
| 64 | 16130 | 2 | 8 | 116 µs | 34.7 µs | 49.8 µs | 1.44 | 0 | 48 / 64 |
| 256 | 64515 | 2 | 8 | 462 µs | 135 µs | 216 µs | 1.60 | 0 | 48 / 64 |
| 1024 | 258051 | 2 | 8 | 1.89 ms | 545 µs | 776 µs | 1.42 | 0 | 48 / 64 |
| 4096 | 1032195 | 2 | 8 | 7.72 ms | 2.3 ms | 3.43 ms | 1.49 | 0 | 48 / 64 |
| 16384 | 4128771 | 2 | 8 | 31.2 ms | 8.49 ms | 12.8 ms | 1.50 | 0 | 48 / 64 |
| 65536 | 16515077 | 2 | 8 | 115 ms | 37.1 ms | 51 ms | 1.38 | 0 | 48 / 64 |
| 262144 | 66060293 | 2 | 8 | 468 ms | 140 ms | 214 ms | 1.54 | 0 | 48 / 64 |

#### A5_map_chain

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 33 | 16 | 1 | 5.22 µs | 696 ns | 1.44 µs | 2.07 | 0 | 48 / 50 |
| 64 | 129 | 64 | 1 | 63.5 µs | 2.47 µs | 5.93 µs | 2.40 | 0 | 192 / 194 |
| 256 | 513 | 256 | 1 | 899 µs | 10.5 µs | 23.7 µs | 2.25 | 0 | 768 / 770 |
| 1024 | 2049 | 1024 | 1 | 15.2 ms | 46.6 µs | 101 µs | 2.17 | 0 | 3072 / 3074 |
| 4096 | 8193 | 4096 | 1 | 242 ms | 206 µs | 416 µs | 2.02 | 0 | 12288 / 12290 |
| 16384 | 32769 | 16384 | 1 | 3.78 s | 878 µs | 1.59 ms | 1.81 | 0 | 49152 / 49154 |

#### B1_map_dupkey

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 21 | 3 | 2 | 2.08 µs | 816 ns | 2.87 µs | 3.52 | 1 | 18 / 22 |
| 4 | 37 | 5 | 2 | 10.6 µs | 1.96 µs | 8.69 µs | 4.43 | 1 | 30 / 34 |
| 6 | 53 | 7 | 2 | 46.6 µs | 3.64 µs | 15.8 µs | 4.35 | 1 | 42 / 46 |
| 8 | 69 | 9 | 2 | 187 µs | 5.3 µs | 26.8 µs | 5.06 | 1 | 54 / 58 |
| 10 | 85 | 11 | 2 | 692 µs | 7.61 µs | 37.1 µs | 4.87 | 1 | 66 / 70 |
| 12 | 101 | 13 | 2 | 2.78 ms | 11.3 µs | 57.6 µs | 5.12 | 1 | 78 / 82 |
| 14 | 117 | 15 | 2 | 12.2 ms | 14.3 µs | 72.1 µs | 5.03 | 1 | 90 / 94 |
| 16 | 133 | 17 | 2 | 44.9 ms | 16.8 µs | 91.7 µs | 5.45 | 1 | 102 / 106 |
| 18 | 149 | 19 | 2 | 179 ms | 20.5 µs | 115 µs | 5.62 | 1 | 114 / 118 |
| 20 | 165 | 21 | 2 | 762 ms | 26.9 µs | 149 µs | 5.55 | 1 | 126 / 130 |
| 22 | 181 | 23 | 2 | — | 31.9 µs | 179 µs | 5.60 | 1 | 138 / 142 |
| 24 | 197 | 25 | 2 | — | 37.1 µs | 211 µs | 5.67 | 1 | 150 / 154 |
| 26 | 213 | 27 | 2 | — | 42.9 µs | 238 µs | 5.55 | 1 | 162 / 166 |
| 28 | 229 | 29 | 2 | — | 45.7 µs | 282 µs | 6.16 | 1 | 174 / 178 |
| 30 | 245 | 31 | 2 | — | 55.6 µs | 323 µs | 5.80 | 1 | 186 / 190 |
| 32 | 261 | 33 | 2 | — | 62.5 µs | 365 µs | 5.84 | 1 | 198 / 202 |
| 34 | 277 | 35 | 2 | — | 69.9 µs | 411 µs | 5.88 | 1 | 210 / 214 |
| 36 | 293 | 37 | 2 | — | 77.6 µs | 458 µs | 5.90 | 1 | 222 / 226 |
| 38 | 309 | 39 | 2 | — | 84.5 µs | 510 µs | 6.03 | 1 | 234 / 238 |
| 40 | 325 | 41 | 2 | — | 94.5 µs | 562 µs | 5.95 | 1 | 246 / 250 |
| 42 | 341 | 43 | 2 | — | 104 µs | 619 µs | 5.98 | 1 | 258 / 262 |
| 44 | 357 | 45 | 2 | — | 113 µs | 678 µs | 6.01 | 1 | 270 / 274 |
| 46 | 373 | 47 | 2 | — | 123 µs | 740 µs | 6.03 | 1 | 282 / 286 |
| 48 | 389 | 49 | 2 | — | 133 µs | 803 µs | 6.05 | 1 | 294 / 298 |
| 50 | 405 | 51 | 2 | — | 143 µs | 870 µs | 6.07 | 1 | 306 / 310 |
| 52 | 421 | 53 | 2 | — | 154 µs | 917 µs | 5.95 | 1 | 318 / 322 |
| 54 | 437 | 55 | 2 | — | 163 µs | 926 µs | 5.68 | 1 | 330 / 334 |
| 56 | 453 | 57 | 2 | — | 168 µs | 1.06 ms | 6.29 | 1 | 342 / 346 |
| 58 | 469 | 59 | 2 | — | 174 µs | 1.08 ms | 6.19 | 1 | 354 / 358 |
| 60 | 485 | 61 | 2 | — | 202 µs | 1.24 ms | 6.13 | 1 | 366 / 370 |
| 62 | 501 | 63 | 2 | — | 205 µs | 1.28 ms | 6.23 | 1 | 378 / 382 |
| 64 | 517 | 65 | 2 | — | 214 µs | 1.3 ms | 6.08 | 1 | 390 / 394 |

#### B2_resort_n_m32

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 1201 | 2 | 32 | 1.55 ms | 313 µs | 121 µs | 0.39 | 0 | 192 / 256 |
| 64 | 4842 | 2 | 64 | 23.6 ms | 2.35 ms | 468 µs | 0.20 | 0 | 384 / 512 |
| 256 | 19435 | 2 | 256 | 407 ms | 13.6 ms | 1.99 ms | 0.15 | 0 | 1536 / 2048 |
| 1024 | 78571 | 2 | 1024 | 6.34 s | 68.1 ms | 8.49 ms | 0.12 | 0 | 6144 / 8192 |
| 4096 | 315115 | 2 | 4096 | — | 304 ms | 33.7 ms | 0.11 | 0 | 24576 / 32768 |
| 16384 | 1261291 | 2 | 16384 | — | 1.54 s | 130 ms | 0.08 | 0 | 98304 / 131072 |

#### B2_resort_m_n64

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 4 | 682 | 2 | 64 | 1.13 ms | 166 µs | 66.5 µs | 0.40 | 0 | 384 / 512 |
| 16 | 2218 | 2 | 64 | 7.54 ms | 896 µs | 224 µs | 0.25 | 0 | 384 / 512 |
| 64 | 10986 | 2 | 64 | 85 ms | 5.47 ms | 968 µs | 0.18 | 0 | 384 / 512 |
| 256 | 47914 | 2 | 256 | 1.35 s | 24.8 ms | 4 ms | 0.16 | 0 | 1536 / 2048 |
| 1024 | 244522 | 2 | 1024 | — | 140 ms | 18.3 ms | 0.13 | 0 | 6144 / 8192 |
| 4096 | 1030954 | 2 | 4096 | — | 646 ms | 75.4 ms | 0.12 | 0 | 24576 / 32768 |
| 16384 | 4176682 | 2 | 16384 | — | — | 314 ms | — | 0 | — / 131072 |

#### B4_resort_dup_n_m32

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 1201 | 2 | 32 | 134 µs | 354 µs | 117 µs | 0.33 | 1 | 192 / 256 |
| 64 | 4842 | 2 | 64 | 1.08 ms | 2.58 ms | 502 µs | 0.19 | 1 | 384 / 512 |
| 256 | 19435 | 2 | 256 | 3.81 ms | 12.7 ms | 2.13 ms | 0.17 | 1 | 1536 / 2048 |
| 1024 | 78571 | 2 | 1024 | 21.7 ms | 64.2 ms | 8.54 ms | 0.13 | 1 | 6144 / 8192 |
| 4096 | 315115 | 2 | 4096 | 88.1 ms | 321 ms | 34.2 ms | 0.11 | 1 | 24576 / 32768 |
| 16384 | 1261291 | 2 | 16384 | 423 ms | 1.48 s | 129 ms | 0.09 | 1 | 98304 / 131072 |

#### B3_nested_resort_m4_n8

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 97 | 2 | 8 | 22.4 µs | 7.11 µs | 7.64 µs | 1.07 | 0 | 48 / 64 |
| 2 | 401 | 3 | 8 | 266 µs | 109 µs | 52.5 µs | 0.48 | 0 | 72 / 88 |
| 3 | 1617 | 4 | 8 | 3.07 ms | 1.78 ms | 323 µs | 0.18 | 0 | 96 / 112 |
| 4 | 6481 | 5 | 8 | 34.5 ms | 22.8 ms | 1.51 ms | 0.07 | 0 | 120 / 136 |
| 5 | 25937 | 6 | 8 | 382 ms | 305 ms | 7.86 ms | 0.03 | 0 | 144 / 160 |
| 6 | 103761 | 7 | 8 | 4.52 s | 3.69 s | 35.5 ms | 0.01 | 0 | 168 / 184 |
| 7 | 415057 | 8 | 8 | — | — | 168 ms | — | 0 | — / 208 |
| 8 | 1660241 | 9 | 8 | — | — | 758 ms | — | 0 | — / 232 |

#### B7_key_chain

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 69 | 17 | 2 | 21.1 µs | 5.82 µs | 38.9 µs | 6.67 | 0 | 102 / 106 |
| 64 | 261 | 65 | 2 | 240 µs | 63.2 µs | 590 µs | 9.34 | 0 | 390 / 394 |
| 256 | 1029 | 257 | 2 | 3.51 ms | 900 µs | 8.76 ms | 9.73 | 0 | 1542 / 1546 |
| 1024 | 4101 | 1025 | 2 | 59.9 ms | 13.9 ms | 144 ms | 10.36 | 0 | 6150 / 6154 |
| 4096 | 16389 | 4097 | 2 | 896 ms | 226 ms | 2.31 s | 10.24 | 0 | 24582 / 24586 |

#### B7_key_chain_dup

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 69 | 17 | 2 | 23.4 ms | 9.91 µs | 48.9 µs | 4.94 | 1 | 102 / 106 |
| 64 | 261 | 65 | 2 | — | 119 µs | 680 µs | 5.69 | 1 | 390 / 394 |
| 256 | 1029 | 257 | 2 | — | 1.81 ms | 10.6 ms | 5.88 | 1 | 1542 / 1546 |
| 1024 | 4101 | 1025 | 2 | — | 30.1 ms | 183 ms | 6.09 | 1 | 6150 / 6154 |
| 4096 | 16389 | 4097 | 2 | — | 462 ms | 2.73 s | 5.92 | 1 | 24582 / 24586 |

#### B6_array_of_maps_key_n64_m16

| param | bytes | D | N | bounded | sort | hash | hash/sort | result | scratch (sort / hash) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 2282 | 2 | 64 | 7.33 ms | 595 µs | 245 µs | 0.41 | 0 | 384 / 512 |
| 4 | 8618 | 2 | 64 | 82.4 ms | 2.72 ms | 972 µs | 0.36 | 0 | 384 / 512 |
| 16 | 33962 | 2 | 64 | 365 ms | 10.1 ms | 3.63 ms | 0.36 | 0 | 384 / 512 |
| 64 | 135402 | 2 | 64 | 1.53 s | 41.1 ms | 14.9 ms | 0.36 | 0 | 384 / 512 |
| 256 | 540970 | 2 | 64 | — | 161 ms | 59.1 ms | 0.37 | 0 | 384 / 512 |
| 1024 | 2162986 | 2 | 64 | — | 660 ms | 257 ms | 0.39 | 0 | 384 / 512 |
| 4096 | 8651050 | 2 | 64 | — | — | 970 ms | — | 0 | — / 512 |
