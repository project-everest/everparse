module LowParse.Pulse.ArrayPtr.Endianness
#lang-pulse
(* ArrayPtr counterparts of the reader direction of LowParse.Pulse.Endianness.

   These are byte-for-byte the same proofs: the specifications only ever talk
   about the ghost byte sequence [v], never about the container. The point of
   the duplication is extraction, not verification. A [Pulse.Lib.Slice.slice]
   is a two-field record, so [Slice.op_Array_Access] is a real function that
   KaRaMeL monomorphizes and emits as a symbol, whereas
   [Pulse.Lib.ArrayPtr.op_Array_Access] is mapped directly to [EBufRead] by
   Pulse extraction and compiles to a plain [b[i]]. *)

open Pulse.Lib.Pervasives
include LowParse.Spec.Endianness

open FStar.Math.Lemmas
open FStar.Mul

module U8 = FStar.UInt8
module E = LowParse.Endianness
module SZ = FStar.SizeT
module AP = Pulse.Lib.ArrayPtr

(* Reads the [len] bytes at offsets [0, len) of [x], most significant first.
   [x] may be longer than [len]; the trailing bytes are ignored. *)
inline_for_extraction
noextract
let be_to_n_t
  (#t: Type0)
  (#tot: nat)
  (u: uinttype u#0 t tot)
  (len: nat { len <= tot })
: Tot Type
= (x: AP.ptr U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  (pos: SZ.t) ->
  stt t
    (AP.pts_to x #pm v ** pure (
      SZ.v pos == len /\
      len <= Seq.length v
    ))
    (fun res -> AP.pts_to x #pm v ** pure (
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
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_be_to_n (Seq.slice (v) 0 0);
  UIntType?.zero u
}

inline_for_extraction
noextract
fn be_to_n_1
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot { tot > 0 })
: (be_to_n_t #t #tot u 1)
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_be_to_n (Seq.slice (v) 0 1);
  E.reveal_be_to_n (Seq.slice (v) 0 0);
  let last = AP.op_Array_Access x 0sz;
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
= (x: AP.ptr U8.t)
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
  let last = AP.op_Array_Access x pos';
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

(* Reads the [len] bytes at offsets [pos, pos + len) of [x], least significant
   first. *)
inline_for_extraction
noextract
let le_to_n_t
  (#t: Type0)
  (#tot: nat)
  (u: uinttype u#0 t tot)
  (len: nat { len <= tot })
: Tot Type
= (x: AP.ptr U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  (pos: SZ.t) ->
  stt t
    (AP.pts_to x #pm v ** pure (
      SZ.v pos + len <= Seq.length v
    ))
    (fun res -> AP.pts_to x #pm v ** pure (
      SZ.v pos + len <= Seq.length v /\
      u.v res == E.le_to_n (Seq.slice v (SZ.v pos) (SZ.v pos + len))
    ))

inline_for_extraction
noextract
fn le_to_n_0
  (#t: Type0)
  (#tot: nat)
  (u: uinttype t tot)
: le_to_n_t #t #tot u 0
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_le_to_n (Seq.slice v (SZ.v pos) (SZ.v pos));
  UIntType?.zero u
}

inline_for_extraction
noextract
fn le_to_n_1
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot { tot > 0 })
: (le_to_n_t #t #tot u 1)
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  E.reveal_le_to_n (Seq.slice v (SZ.v pos) (SZ.v pos + 1));
  E.reveal_le_to_n (Seq.tail (Seq.slice v (SZ.v pos) (SZ.v pos + 1)));
  let first = AP.op_Array_Access x pos;
  UIntType?.from_byte u first
}

inline_for_extraction
noextract
fn le_to_n_S
  (#t: Type)
  (#tot: nat)
  (#u: uinttype t tot)
  (#len: nat { len + 1 <= tot })
  (ih: le_to_n_t #t #tot u len)
: (le_to_n_t #t #tot u (len + 1))
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (pos: SZ.t)
{
  assert_norm (pow2 8 == 256);
  AP.pts_to_len x;
  E.reveal_le_to_n (Seq.slice v (SZ.v pos) (SZ.v pos + (len + 1)));
  Seq.slice_slice v (SZ.v pos) (SZ.v pos + (len + 1)) 1 (len + 1);
  E.lemma_le_to_n_is_bounded (Seq.slice v (SZ.v pos + 1) (SZ.v pos + 1 + len));
  pow2_le_compat (8 * tot) (8 * (len + 1));
  pow2_le_compat (8 * (len + 1)) (8 * len);
  pow2_plus (8 * len) 8;
  let pos' = pos `SZ.add` 1sz;
  let first = AP.op_Array_Access x pos;
  let n = ih x #pm #v pos';
  let bfirst = UIntType?.from_byte u first;
  UIntType?.add u bfirst (u.mul256 n)
}

[@must_reduce]
noextract
let rec mk_le_to_n
  (#t: Type)
  (#tot: nat)
  (u: uinttype t tot)
  (len: nat {len <= tot})
: Tot (le_to_n_t u len)
  (decreases len)
= if len = 0
  then le_to_n_0 u
  else if len = 1
  then le_to_n_1 u
  else le_to_n_S (mk_le_to_n u (len - 1))
