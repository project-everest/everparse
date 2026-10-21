module LowParse.Pulse.SizeComparison
#lang-pulse
open Pulse.Lib.Pervasives
open LowParse.Pulse.Base
open LowParse.Spec.VCList

module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module S = Pulse.Lib.Slice

(* Portable comparisons between an untrusted machine integer (a wire-read length
   or element count) and a [size_t] budget, WITHOUT assuming [SZ.fits_u64]
   (i.e. sound on 16/32/64/wider-bit size_t).

   They work in base 2^15 = 32768, the largest power of two guaranteed to fit any
   size_t (the C standard mandates size_t is at least 16 bits, exposed in F* as
   [SZ.fits_at_least_16]). We compute [b / 2^60] with four divisions by 32768; if
   it is >= 16 then [SZ.v b >= 2^64], otherwise [SZ.v b < 2^64] so [b] narrows to
   [U64.t] exactly and the comparison is a plain [U64] comparison. In C/Rust these
   compile to shifts/masks and are sound at 16/32/64-bit width. *)

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

(* Portable check whether a [size_t] [b] fits in [U64.t], i.e. [SZ.v b < 2^64].
   Same base-2^15 technique as [u64_lte_sizet]: [b / 2^60 < 16]. When it holds,
   [SZ.sizet_to_uint64 b] is exact (no truncation). *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn sizet_fits_u64 (b: SZ.t)
  requires emp
  returns res: bool
  ensures pure (res == (SZ.v b < pow2 64))
{
  let q1 = SZ.div b 32768sz;
  let q2 = SZ.div q1 32768sz;
  let q3 = SZ.div q2 32768sz;
  let q4 = SZ.div q3 32768sz;
  FStar.Math.Lemmas.division_multiplication_lemma (SZ.v b) 32768 32768;
  FStar.Math.Lemmas.division_multiplication_lemma (SZ.v b) (32768 * 32768) 32768;
  FStar.Math.Lemmas.division_multiplication_lemma (SZ.v b) (32768 * 32768 * 32768) 32768;
  assert (pure (SZ.v q4 == SZ.v b / 0x1000000000000000));
  if SZ.lt q4 16sz {
    assert (pure (SZ.v b < 16 * 0x1000000000000000));
    assert (pure (SZ.v b < pow2 64));
    true
  } else {
    assert (pure (SZ.v b >= 16 * 0x1000000000000000));
    assert (pure (SZ.v b >= pow2 64));
    false
  }
}

(* Portable, EXACT decision of [SZ.v x + SZ.v y <= SZ.v budget] against a caller
   supplied [size_t] budget. This is the decidable counterpart of the (provably
   impossible) exact decision of [SZ.fits (SZ.v x + SZ.v y)]: the latter compares
   the sum against the platform's unknown [SIZE_MAX] (not exposed in F*, and not
   observable at any fixed size_t value), whereas here we compare against a KNOWN
   [size_t] value. Overflow-free: we never form [x + y]; we test [y] against the
   exact remaining room [budget - x]. On success a caller obtains [fits (x + y)]
   for free via [SZ.fits_lte (x + y) budget], since [budget] is a [size_t]. This
   is the size-arithmetic analogue of the writer bounding lengths by its output
   slice length. *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn sizet_sum_within_budget (budget: SZ.t) (x: SZ.t) (y: SZ.t)
  requires emp
  returns res: bool
  ensures pure (res == (SZ.v x + SZ.v y <= SZ.v budget))
{
  if (SZ.lte x budget) {
    let room = SZ.sub budget x;
    SZ.lte y room
  } else {
    false
  }
}

(* Portable comparison [U32.t <= size_t], obtained by widening the [U32.t] to
   [U64.t] (always exact) and reusing [u64_lte_sizet]. Together with the weakened
   [SZ.uint32_to_sizet] (whose precondition is [fits_u32 \/ fits (U32.v x)]) this
   lets a caller convert a wire-read [U32.t] length to [size_t] soundly: after
   [u32_lte_sizet len budget] returns [true], [SZ.fits_lte] gives [fits (U32.v
   len)]. *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn u32_lte_sizet (a: U32.t) (b: SZ.t)
  requires emp
  returns res: bool
  ensures pure (res == (U32.v a <= SZ.v b))
{
  let a64 = Cast.uint32_to_uint64 a;
  u64_lte_sizet a64 b
}

(* Portable decision of [SZ.v n <= U32.v m] (the reverse orientation of
   [u32_lte_sizet]), WITHOUT assuming [SZ.fits_u64]: widen [m] to [U64.t]
   (exact, since [U32.v m < 2^32 <= 2^64]), add one (no overflow), and negate the
   portable [u64_lte_sizet] test: [not (U32.v m + 1 <= SZ.v n)] == [SZ.v n <= U32.v m]. *)

inline_for_extraction
noextract [@@noextract_to "krml"]
fn sizet_lte_u32 (n: SZ.t) (m: U32.t)
  requires emp
  returns res: bool
  ensures pure (res == (SZ.v n <= U32.v m))
{
  let m64 = Cast.uint32_to_uint64 m;
  FStar.Math.Lemmas.pow2_lt_compat 64 32;
  let m64p1 = U64.add m64 1uL;
  not (u64_lte_sizet m64p1 n)
}

(* A serialized [nlist n p] whose element parser consumes at least one byte
   occupies at least [n] bytes, so its element count [n] necessarily fits
   [size_t]. Packaged as a reusable ghost lemma so only the resulting
   [SZ.fits n] fact enters the caller's SMT context. *)

ghost
fn nlist_count_fits
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n: nat)
  (input: S.slice byte)
  (#pm: perm)
  (#v: nlist n t)
  requires pts_to_serialized (serialize_nlist n s) input #pm v ** pure (k.parser_kind_low >= 1)
  ensures pts_to_serialized (serialize_nlist n s) input #pm v ** pure (SZ.fits n)
{
  pts_to_serialized_length (serialize_nlist n s) input;
  parse_nlist_kind_low n k;
  FStar.Math.Lemmas.lemma_mult_le_right n 1 k.parser_kind_low;
  SZ.fits_lte n (SZ.v (S.len input));
}
