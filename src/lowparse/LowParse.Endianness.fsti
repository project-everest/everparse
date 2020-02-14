module LowParse.Endianness
include FStar.Endianness
open FStar.Mul

module S = FStar.Seq
module U8 = FStar.UInt8

val index_be_to_n
  (b: bytes)
  (i: nat)
: Lemma
  (requires (
    i < S.length b
  ))
  (ensures (
    U8.v (S.index b i) == (be_to_n b / pow2 (8 * (S.length b - 1 - i))) % pow2 8
  ))

val index_n_to_be
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    U8.v (S.index (n_to_be len n) i)) == (n / pow2 (8 * (len - 1 - i)) % pow2 8
  ))

val index_n_to_be_zero_left
  (len: nat)
  (n: nat)
  (j: nat)
  (i: nat)
: Lemma
  (requires (
    i < j /\
    j <= len /\
    n < pow2 (8 * (len - j))
  ))
  (ensures (
    pow2 (8 * (len - j)) <= pow2 (8 * len) /\
    U8.v (S.index (n_to_be len n) i) == 0
  ))

val index_n_to_be_zero_right
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len) /\
    n % pow2 (8 * (len - i)) == 0
  ))
  (ensures (
    U8.v (S.index (n_to_be len n) i) == 0
  ))

val be_to_n_append
  (hi lo: bytes)
: Lemma
  (ensures (be_to_n (hi `S.append` lo) == be_to_n hi * pow2 (8 * S.length lo) + be_to_n lo))

val n_to_be_append
  (len: nat)
  (n: nat)
  (len_lo: nat)
: Lemma
  (requires (
    n < pow2 (8 * len) /\
    len_lo <= len
  ))
  (ensures (
    let hi = n / pow2 (8 * len_lo) in
    let lo = n % pow2 (8 * len_lo) in
    0 <= hi /\
    hi < pow2 (8 * (len - len_lo)) /\
    0 <= lo /\
    lo < pow2 (8 * len_lo) /\
    n_to_be len n == n_to_be (len - len_lo) hi `S.append` n_to_be len_lo lo
  ))

val reveal_n_to_be
  (len: nat)
  (n: nat)
: Lemma
  (requires (
    n < pow2 (8 * len)
  ))
  (ensures (
    (len > 0 ==> (0 <= n / pow2 8 /\ n / pow2 8 < pow2 (8 * (len - 1)))) /\
    n_to_be len n `S.equal` (if len = 0 then S.empty else n_to_be (len - 1) (n / pow2 8) `S.snoc` (U8.uint_to_t (n % pow2 8)))
  ))

val slice_n_to_be
  (len: nat)
  (n: nat)
  (i j: nat)
: Lemma
  (requires (
    i <= j /\
    j <= len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    let res = (n / pow2 (8 * (len - j))) % pow2 (8 * (j - i)) in
    0 <= res /\
    res < pow2 (8 * (j - i)) /\
    S.slice (n_to_be len n) i j == n_to_be (j - i) res
  ))

val index_le_to_n
  (b: bytes)
  (i: nat)
: Lemma
  (requires (
    i < S.length b
  ))
  (ensures (
    U8.v (S.index b i) == (le_to_n b / pow2 (8 * i)) % pow2 8
  ))

val index_n_to_le
  (len: nat)
  (n: nat)
  (i: nat)
: Lemma
  (requires (
    i < len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    U8.v (S.index (n_to_le len n) i)) == (n / pow2 (8 * i) % pow2 8
  ))

val reveal_n_to_le
  (len: nat)
  (n: nat)
: Lemma
  (requires (
    n < pow2 (8 * len)
  ))
  (ensures (
    (len > 0 ==> (0 <= n / pow2 8 /\ n / pow2 8 < pow2 (8 * (len - 1)))) /\
    n_to_le len n `S.equal` (if len = 0 then S.empty else (U8.uint_to_t (n % pow2 8) `S.cons` n_to_le (len - 1) (n / pow2 8)))
  ))
