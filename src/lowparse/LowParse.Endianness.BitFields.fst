module LowParse.Endianness.BitFields
include LowParse.Endianness
module BF = LowParse.BitFields

module S = FStar.Seq

open FStar.Mul

let slice_n_to_be_bitfield
  (len: pos)
  (n: nat)
  (i j: nat)
: Lemma
  (requires (
    i <= j /\
    j <= len /\
    n < pow2 (8 * len)
  ))
  (ensures (
    S.slice (n_to_be len n) i j == n_to_be (j - i) (BF.get_bitfield #(8 * len) n (8 * (len - j)) (8 * (len - i)))
  ))
= slice_n_to_be len n i j;
  BF.get_bitfield_eq #(8 * len) n (8 * (len - j)) (8 * (len - i))

module U8 = FStar.UInt8

let bitfield_be_to_n_slice
  (s: S.seq U8.t)
  (i: nat)
  (j: nat)
: Lemma
  (requires (
    Seq.length s > 0 /\
    i <= j /\ j <= S.length s
  ))
  (ensures (
    let len = S.length s in
    be_to_n s < pow2 (8 * len) /\
    be_to_n (S.slice s i j) == BF.get_bitfield #(8 * len) (be_to_n s) (8 * (len - j)) (8 * (len - i))
  ))
= let len = S.length s in
  lemma_be_to_n_is_bounded s;
  slice_n_to_be_bitfield len (be_to_n s) i j
