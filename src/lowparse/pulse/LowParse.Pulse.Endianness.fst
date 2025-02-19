module LowParse.Pulse.Endianness
#lang-pulse
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
include LowParse.Spec.Endianness

module U8 = FStar.UInt8
module E = LowParse.Endianness
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice

inline_for_extraction
noextract
let be_to_n_t
  (#t: Type0)
  (#tot: nat)
  (u: uinttype u#0 t tot)
  (len: nat { len <= tot })
: Tot Type
= (x: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  (pos: SZ.t) ->
  stt t
    (pts_to x #pm v ** pure (
      SZ.v pos == len /\
      len <= Seq.length v
    ))
    (fun res -> pts_to x #pm v ** pure (
      SZ.v pos == len /\
      len <= Seq.length v /\
      u.v res == E.be_to_n (Seq.slice v 0 len)
    ))

inline_for_extraction
noextract
fn be_to_n_0
  (#t: Type0)
  (#tot: nat)
  (u: uinttype t tot)
: be_to_n_t #t #tot u 0
= (x: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_be_to_n (Seq.slice (v) 0 0);
  UIntType?.zero u
}

open FStar.Math.Lemmas
open FStar.Mul

inline_for_extraction
noextract
fn be_to_n_1
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot { tot > 0 })
: (be_to_n_t #t #tot u 1)
= (x: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_be_to_n (Seq.slice (v) 0 1);
  E.reveal_be_to_n (Seq.slice (v) 0 0);
  let last = S.op_Array_Access x 0sz;
  UIntType?.from_byte u last
}

inline_for_extraction
noextract
fn be_to_n_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat { len + 1 <= tot })
  (ih: be_to_n_t #t #tot u len)
: (be_to_n_t #t #tot u (len + 1))
= (x: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  assert_norm (pow2 8 == 256);
  E.reveal_be_to_n (Seq.slice (v) 0 (len + 1));
  E.lemma_be_to_n_is_bounded (Seq.slice (v) 0 len);
  pow2_le_compat (8 * tot) (8 * (len + 1));
  pow2_le_compat (8 * (len + 1)) (8 * len);
  pow2_plus (8 * len) 8;
  let pos' = pos `SZ.sub` 1sz;
  let last = S.op_Array_Access x pos';
  let n = ih x #pm #v pos';
  let blast = UIntType?.from_byte u last;
  UIntType?.add u blast (u.mul256 n)
}

// attribute for use with delta_attr
noextract
noeq
type must_reduce = | MustReduce_dummy_do_not_use

[@must_reduce]
noextract
let rec mk_be_to_n
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot})
: Tot (be_to_n_t u len)
  (decreases len)
= if len = 0
  then be_to_n_0 u
  else if len = 1
  then be_to_n_1 u
  else be_to_n_S (mk_be_to_n u (len - 1))

// Writing from right to left: pos should be the position one past the end of the writing zone

inline_for_extraction
noextract
let n_to_be_t
  (#t: Type0)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat { len <= tot })
: Tot Type
= (n: t) ->
  (x: S.slice U8.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  (pos: SZ.t) ->
  stt unit
    (pts_to x v ** pure (
      len <= SZ.v pos /\
      SZ.v pos <= Seq.length v /\
      u.v n < pow2 (8 * len)
    ))
    (fun _ -> exists* v' . pts_to x v' ** pure (
      len <= SZ.v pos /\
      SZ.v pos <= Seq.length v /\
      u.v n < pow2 (8 * len) /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v pos - len) `Seq.equal` Seq.slice (v) 0 (SZ.v pos - len) /\
      Seq.slice v' (SZ.v pos - len) (SZ.v pos) `Seq.equal` n_to_be len (u.v n) /\
      Seq.slice v' (SZ.v pos) (Seq.length v') `Seq.equal` Seq.slice v (SZ.v pos) (Seq.length v)
    ))

inline_for_extraction
noextract
fn n_to_be_0
  (#t: Type0)
  (#tot: nat)
  (u: uinttype t tot)
: (n_to_be_t #t #tot u 0)
= (n: t)
  (x: S.slice U8.t)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_be_to_n (Seq.slice (v) 0 0);
  ()
}

inline_for_extraction
noextract
fn n_to_be_1
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot { tot > 0 })
: (n_to_be_t #t #tot u 1)
= (n: t)
  (x: S.slice U8.t)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_n_to_be 1 (u.v n);
  E.reveal_n_to_be 0 (u.v n / pow2 8);
  let n' = u.to_byte n;
  S.op_Array_Assignment x (pos `SZ.sub` 1sz) n'
}

inline_for_extraction
noextract
fn n_to_be_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat {len + 1 <= tot})
  (ih: n_to_be_t #t #tot u len)
: (n_to_be_t #t #tot u (len + 1))
= (n: t)
  (x: S.slice U8.t)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  Seq.lemma_split (Seq.slice v (SZ.v pos - 1) (Seq.length v)) 1;
  reveal_n_to_be (len + 1) (u.v n);
  let lo = u.to_byte n;
  let hi = u.div256 n;
  let pos' = pos `SZ.sub` 1sz;
  with v1 . assert (pts_to x v1);
  Seq.lemma_split (Seq.slice v1 (SZ.v pos - 1) (Seq.length v1)) 1;
  let _ = ih hi x pos';
  S.op_Array_Assignment x pos' lo;
  with v2 . assert (pts_to x v2);
  Seq.lemma_split (Seq.slice v2 (SZ.v pos - 1) (Seq.length v2)) 1;
}

[@must_reduce]
noextract
let rec mk_n_to_be
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot})
: Tot (n_to_be_t u len)
  (decreases len)
= if len = 0
  then n_to_be_0 u
  else if len = 1
  then n_to_be_1 u
  else n_to_be_S (mk_n_to_be u (len - 1))
