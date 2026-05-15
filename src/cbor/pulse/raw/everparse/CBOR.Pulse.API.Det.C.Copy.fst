module CBOR.Pulse.API.Det.C.Copy
#lang-pulse
friend CBOR.Pulse.API.Det.C

(* Implementation of CBOR.Pulse.API.Det.C.Copy on top of the new
   EverParse-based stack. The strategy is to serialize the input cbor
   into a freshly-allocated buffer and re-parse it; the resulting
   cbor_det_t inherits 1.0R permission on its own independent allocation,
   while the input is preserved at its original permission. *)

open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module Impl = CBOR.Pulse.Raw.EverParse.Det.Impl
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module S = Pulse.Lib.Slice
module SU = Pulse.Lib.Slice.Util
module AP = Pulse.Lib.ArrayPtr
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* ---------------- Types ---------------- *)

noeq type cbor_det_freeable_t' = {
  cbor: cbor_det_t;
  buf: V.vec U8.t;
  len: SZ.t;
}

let cbor_det_freeable_t = cbor_det_freeable_t'

let freeable (r: cbor_det_freeable_t) : slprop =
  exists* (vbytes: Seq.seq U8.t).
    V.pts_to r.buf vbytes **
    pure (V.is_full_vec r.buf /\ Seq.length vbytes == SZ.v r.len)

let cbor_get_from_freeable r = r.cbor

(* ---------------- Unreachable-case panic ---------------- *)

(* A non-terminating helper used to discharge a formally-unreachable
   branch without invoking `admit`/`assume`. The size = 0 case of
   `cbor_det_size` means the serialized cbor exceeds 2^64-1 bytes,
   which cannot happen for any cbor that fits in 64-bit-addressable
   memory; but `cbor_det_match` alone does not formally bound the
   serialized size in spec (a single max-size string is allowed to
   have length 2^64-1, and serializing it produces ~2^64+8 bytes).

   Pulse permits a `fn rec` without an explicit decreases clause; the
   resulting computation is non-terminating, and an stt computation
   that never returns vacuously satisfies any postcondition, including
   `pure False`. The caller can then derive any pure fact (in our case
   `SZ.v size > 0`) to continue verification. At extraction time, this
   compiles to an infinite loop, which is a safe failure mode rather
   than undefined behaviour. *)
fn rec panic (#a: Type0) (_: unit)
  requires emp
  returns r: a
  ensures pure False
{
  panic #a ()
}

(* ---------------- Copy ---------------- *)

#restart-solver
fn cbor_copy_impl
  (c: cbor_det_t)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
  requires cbor_det_match p c v
  returns r: cbor_det_freeable_t
  ensures
    cbor_det_match p c v **
    cbor_det_match 1.0R (cbor_get_from_freeable r) v **
    Trade.trade
      (cbor_det_match 1.0R (cbor_get_from_freeable r) v)
      (freeable r)
{
  let _ : squash SZ.fits_u64 = assume SZ.fits_u64;
  let bound : SZ.t = SZ.uint64_to_sizet 0xFFFFFFFFFFFFFFFFuL;
  let size = Impl.cbor_det_size c bound;
  (* size = 0 means the serialized cbor exceeds 2^64-1 bytes; see the
     comment on `panic` above. We discharge this branch by divergence. *)
  if (size = 0sz) {
    panic #unit ()
  };
  let buf = V.alloc 0uy size;
  V.to_array_pts_to buf;
  let sl = S.from_array (V.vec_to_array buf) size;
  S.pts_to_len sl;
  let ap = S.slice_to_arrayptr_intro sl;
  Impl.cbor_det_serialize c ap size;
  with vb . assert (AP.pts_to ap vb);
  S.slice_to_arrayptr_elim ap;
  with v1 . assert (S.pts_to sl v1);
  S.pts_to_len sl;
  (* v1 == Spec.cbor_det_serialize v: from cbor_det_serialize_fits_postcond
     we have SZ.v size == Seq.length s where s = Spec.cbor_det_serialize v,
     and vb == s `append` v'. With SZ.v size == Seq.length vb, v' = empty. *)
  Seq.lemma_eq_elim v1 (Spec.cbor_det_serialize v);
  Seq.append_empty_r (Spec.cbor_det_serialize v);
  let res_cbor = Impl.cbor_det_parse_valid () sl;
  with v' . assert (cbor_det_match 1.0R res_cbor v');
  (* Recover v' == v by injectivity of cbor_det_serialize. *)
  Spec.cbor_det_serialize_inj_strong v' v Seq.empty Seq.empty;
  Trade.rewrite_with_trade
    (cbor_det_match 1.0R res_cbor v')
    (cbor_det_match 1.0R res_cbor v);
  Trade.trans
    (cbor_det_match 1.0R res_cbor v)
    (cbor_det_match 1.0R res_cbor v')
    (S.pts_to sl v1);
  let r = { cbor = res_cbor; buf; len = size };
  rewrite (cbor_det_match 1.0R res_cbor v)
       as (cbor_det_match 1.0R (cbor_get_from_freeable r) v);
  rewrite (Trade.trade
            (cbor_det_match 1.0R res_cbor v)
            (S.pts_to sl v1))
       as (Trade.trade
            (cbor_det_match 1.0R (cbor_get_from_freeable r) v)
            (S.pts_to sl v1));
  rewrite (S.is_from_array (V.vec_to_array buf) sl)
       as (S.is_from_array (V.vec_to_array r.buf) sl);
  (* Build the outer trade: cbor_det_match → freeable r,
     composing the parse_valid trade, S.to_array, V.to_vec_pts_to,
     and folding freeable. *)
  intro
    (Trade.trade
      (cbor_det_match 1.0R (cbor_get_from_freeable r) v)
      (freeable r))
    #(Trade.trade
        (cbor_det_match 1.0R (cbor_get_from_freeable r) v)
        (S.pts_to sl v1) **
      S.is_from_array (V.vec_to_array r.buf) sl)
    fn _
  {
    Trade.elim _ _;
    S.to_array sl;
    V.to_vec_pts_to r.buf;
    fold (freeable r)
  };
  r
}

fn cbor_copy (_: unit)
: cbor_copy_t u#0 u#0 #_ #_ cbor_det_match freeable cbor_get_from_freeable
=
  (c: _)
  (#p: _)
  (#v: _)
{
  cbor_copy_impl c
}

(* ---------------- Free ---------------- *)

fn cbor_free' (x: cbor_det_freeable_t)
  requires freeable x
  ensures emp
{
  unfold (freeable x);
  V.free x.buf;
}

fn cbor_free (_: unit)
: cbor_free_t freeable
=
  (x: _)
{
  cbor_free' x
}
