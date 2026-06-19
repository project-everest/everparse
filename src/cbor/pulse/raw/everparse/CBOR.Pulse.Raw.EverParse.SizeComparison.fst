module CBOR.Pulse.Raw.EverParse.SizeComparison
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Mul

module SZ = FStar.SizeT
module U64 = FStar.UInt64

(* A portable comparison between an untrusted [U64.t] (a CBOR header argument:
   an element count or byte length) and a [size_t] budget, without assuming
   [SZ.fits_u64] (i.e. sound on 16/32/64/wider-bit size_t).

   It works in base 2^15 = 32768, the largest power of two guaranteed to fit any
   size_t (the C standard mandates size_t is at least 16 bits, exposed in F* as
   [SZ.fits_at_least_16]). We compute [b / 2^60] with four divisions by 32768; if
   it is >= 16 then [SZ.v b >= 2^64 > U64.v a], otherwise [SZ.v b < 2^64] so [b]
   narrows to [U64.t] exactly and the comparison is a plain [U64.lte]. *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn u64_lte_sizet (a: U64.t) (b: SZ.t)
  requires emp
  returns res: bool
  ensures pure (res == (U64.v a <= SZ.v b))
{
  let q1 = SZ.div b 32768sz;
  let q2 = SZ.div q1 32768sz;
  let q3 = SZ.div q2 32768sz;
  let q4 = SZ.div q3 32768sz;
  FStar.Math.Lemmas.division_multiplication_lemma (SZ.v b) 32768 32768;
  FStar.Math.Lemmas.division_multiplication_lemma (SZ.v b) (32768 * 32768) 32768;
  FStar.Math.Lemmas.division_multiplication_lemma (SZ.v b) (32768 * 32768 * 32768) 32768;
  assert (pure (SZ.v q4 == SZ.v b / 0x1000000000000000));
  if SZ.gte q4 16sz {
    assert (pure (SZ.v b >= 16 * 0x1000000000000000));
    assert (pure (SZ.v b >= pow2 64));
    true
  } else {
    assert (pure (SZ.v b < 16 * 0x1000000000000000));
    assert (pure (SZ.v b < pow2 64));
    let b64 = SZ.sizet_to_uint64 b;
    FStar.Math.Lemmas.small_mod (SZ.v b) (pow2 64);
    U64.lte a b64
  }
}
