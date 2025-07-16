module CDDL.Pulse.Serialize.Base
#lang-pulse
include CDDL.Pulse.Base
include CDDL.Pulse.Types
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format

let impl_serialize_post
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (s: spec t tgt inj)
    (v: tgt)
    (w: Seq.seq U8.t)
    (res: SZ.t)
: Tot prop
= (SZ.v res > 0 <==> (s.serializable v /\ Seq.length (Cbor.cbor_det_serialize (s.serializer v)) <= Seq.length w)) /\
  (SZ.v res > 0 ==> (
    SZ.v res <= Seq.length w /\
    Seq.slice w 0 (SZ.v res) `Seq.equal` Cbor.cbor_det_serialize (s.serializer v)
  ))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (s: spec t tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
  (c: impl_tgt) ->
  (#v: Ghost.erased tgt) ->
  (out: S.slice U8.t) ->
  stt SZ.t
    (exists* w . r c v ** pts_to out w)
    (fun res -> exists* w .
      r c v ** pts_to out w **
      pure (impl_serialize_post s v w res)
    )

noextract [@@noextract_to "krml"]
let coerce_spec
  (#t: typ)
  (#tgt: Type0)
  (#inj: bool)
  (ps: spec t tgt inj)
  (tgt' : Type0)
  (sq: squash (tgt == tgt'))
: Tot (spec t tgt' inj)
= ps

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_cast_rel
    (#[@@@erasable] t: Ghost.erased typ)
    (#tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable] ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (i: impl_serialize ps r)
    (#tgt': Type0)
    (#impl_tgt': Type0)
    (r': rel impl_tgt' tgt')
    (sq1: squash (tgt == tgt'))
    (sq2: squash (impl_tgt == impl_tgt'))
    (sq3: squash (r' == r))
: impl_serialize #(Ghost.reveal t) #tgt' #(Ghost.reveal inj) (coerce_spec (Ghost.reveal ps) tgt' sq1) #impl_tgt' r'
= 
  (c: _)
  (#v: _)
  (out: _)
{
  Trade.rewrite_with_trade
    (r' c v)
    (r c v); 
  let res = i c out;
  Trade.elim _ _;
  res
}

let impl_serialize_t_eq
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (s: spec t tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
    (impl_tgt2: Type0)
    (ieq: squash (impl_tgt == impl_tgt2))
: Tot (squash (impl_serialize s #impl_tgt r == impl_serialize s #impl_tgt2 (coerce_rel r impl_tgt2 ieq)))
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_always_false
    (#t: Ghost.erased typ)
    (#inj: Ghost.erased bool)
    (s: Ghost.erased (spec t (squash False) inj))
: impl_serialize #_ #_ #_ s #_ (rel_always_false (squash False) (squash False))
= (c: _)
  (#v: _)
  (out: _)
{
  0sz
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_ext
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize ps r)
    (#[@@@erasable]t': Ghost.erased typ)
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (spec t' tgt inj'))
    ([@@@erasable]sq: squash (
      (Ghost.reveal inj == true \/ Ghost.reveal inj' == true) /\
      typ_equiv t' t /\
      (forall (x: cbor) . Ghost.reveal t' x ==> ((Ghost.reveal ps'.parser x <: tgt) == Ghost.reveal ps.parser x))
    ))
: impl_serialize #(Ghost.reveal t') #tgt #inj' (Ghost.reveal ps') #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
{
  i c out
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_bij
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize ps r)
    (#[@@@erasable]tgt' : Type0)
    ([@@@erasable]f12: Ghost.erased (tgt -> tgt'))
    ([@@@erasable]f21: Ghost.erased (tgt' -> tgt))
    ([@@@erasable]fprf_21_12: (x: tgt) -> squash (Ghost.reveal f21 (Ghost.reveal f12 x) == x))
    ([@@@erasable]fprf_12_21: (x: tgt') -> squash (Ghost.reveal f12 (Ghost.reveal f21 x) == x))
    (#impl_tgt' : Type0)
    (g12: (impl_tgt -> impl_tgt'))
    (g21: (impl_tgt' -> impl_tgt))
    ([@@@erasable]gprf_21_12: (x: impl_tgt) -> squash (g21 (g12 x) == x))
    ([@@@erasable]gprf_12_21: (x: impl_tgt') -> squash (g12 (g21 x) == x))
: impl_serialize #t #tgt' #inj (spec_inj ps f12 f21 fprf_21_12 fprf_12_21) #impl_tgt' (rel_fun r g21 f21)
=
    (c: _)
    (#v: _)
    (out: _)
{
  let c' = g21 c;
  Trade.rewrite_with_trade
    (rel_fun r g21 f21 c v)
    (r c' (Ghost.reveal f21 v));
  let res = i c' #(Ghost.reveal f21 v) out; // FIXME: WHY WHY WHY the explicit here?
  Trade.elim _ _;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_choice
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize ps1 r1)
    (#[@@@erasable]t2: Ghost.erased typ)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize ps2 r2)
    ([@@@erasable]sq: squash (
      typ_disjoint t1 t2
    ))
: impl_serialize #_ #_ #_ (spec_choice ps1 ps2) #_ (rel_either r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
{
  rel_either_cases r1 r2 c v;
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade
        (rel_either r1 r2 c v)
        (r1 c1 (Inl?.v v));
      let res = i1 c1 out;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade
        (rel_either r1 r2 c v)
        (r2 c2 (Inr?.v v));
      let res = i2 c2 out;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_either_left
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize ps1 r2)
: impl_serialize #_ #_ #_ (ps1) #_ (rel_either_left r1 r2)
=
    (c: _)
    (#v: _)
    (out: _)
{
  match c {
    norewrite
    Inl c1 -> {
      Trade.rewrite_with_trade
        (rel_either_left r1 r2 c v)
        (r1 c1 v);
      let res = i1 c1 out;
      Trade.elim _ _;
      res
    }
    norewrite
    Inr c2 -> {
      Trade.rewrite_with_trade
        (rel_either_left r1 r2 c v)
        (r2 c2 v);
      let res = i2 c2 out;
      Trade.elim _ _;
      res
    }
  }
}
