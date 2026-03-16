module CDDL.Pulse.Serialize.Gen.Base
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

let bare_cbor_parser = (x: Seq.seq U8.t) -> Pure (option (cbor & nat))
  (requires True)
  (ensures (fun res -> match res with
  | None -> True
  | Some (_, n) -> 0 < n /\ n <= Seq.length x
  ))

let cbor_parse_prefix_prop'
  (p: bare_cbor_parser)
  (x y: Seq.seq U8.t)
: Tot prop
= match p x with
  | Some (_, n) -> (Seq.length y >= n /\ Seq.slice x 0 n == Seq.slice y 0 n) ==> p x == p y
  | _ -> True

let cbor_parse_prefix_prop
  (p: bare_cbor_parser)
: Tot prop
= forall x y . cbor_parse_prefix_prop' p x y

let cbor_parser = (p: bare_cbor_parser { cbor_parse_prefix_prop p})

let cbor_max_length_prop (p: bare_cbor_parser) (f: Cbor.cbor -> option nat) : Tot prop =
  forall x y (n: nat) . (Some? (f x) /\ p y == Some (x, n)) ==> n <= Some?.v (f x)

let cbor_max_length (p: bare_cbor_parser) = (f: (Cbor.cbor -> option nat) { cbor_max_length_prop p f })

let cbor_min_length_prop (p: bare_cbor_parser) (f: Cbor.cbor -> nat) : Tot prop =
  forall x y (n: nat) . p y == Some (x, n) ==> n >= f x

let cbor_min_length (p: bare_cbor_parser) = (f: (Cbor.cbor -> nat) { cbor_min_length_prop p f})

(* Instance 0: underspecified serialization *)
let cbor_max_length_underspec (p: bare_cbor_parser) : Tot (cbor_max_length p) = fun _ -> None
let cbor_min_length_underspec (p: bare_cbor_parser) : Tot (cbor_min_length p) = fun _ -> 0

(* Instance 1: deterministic encoding *)
let cbor_det_parse_prefix
  ()
: Lemma (cbor_parse_prefix_prop Cbor.cbor_det_parse)
= let prf
    (x y: Seq.seq U8.t)
  : Lemma
    (cbor_parse_prefix_prop' Cbor.cbor_det_parse x y)
  = Classical.move_requires (Cbor.cbor_det_parse_prefix x) y
  in
  Classical.forall_intro_2 prf

let cbor_det_parse : cbor_parser =
  cbor_det_parse_prefix ();
  Cbor.cbor_det_parse

let cbor_det_parse_equiv (s: Seq.seq U8.t) (v: Cbor.cbor) (len: nat) : Lemma
  (cbor_det_parse s == Some (v, len) <==> (len <= Seq.length s /\ Seq.slice s 0 len == Cbor.cbor_det_serialize v))
= if cbor_det_parse s = Some (v, len)
  then ()
  else if len <= Seq.length s && Seq.slice s 0 len = Cbor.cbor_det_serialize v
  then begin
    Cbor.cbor_det_serialize_parse v;
    Cbor.cbor_det_parse_prefix (Cbor.cbor_det_serialize v) s
  end
  else ()

let cbor_det_max_length : cbor_max_length cbor_det_parse = fun x -> Some (Seq.length (Cbor.cbor_det_serialize x))
let cbor_det_min_length : cbor_min_length cbor_det_parse = fun x -> Seq.length (Cbor.cbor_det_serialize x)

let impl_serialize_post
    (#p: cbor_parser)
    (overflows_low: cbor_min_length p)
    (fits_high: cbor_max_length p)
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (s: spec t tgt inj)
    (v: tgt)
    (w: Seq.seq U8.t)
    (res: SZ.t)
: Tot prop
= ((s.serializable v /\ Some? (fits_high (s.serializer v)) /\ Some?.v (fits_high (s.serializer v)) <= (Seq.length w)) ==> SZ.v res > 0) /\
  ((s.serializable v /\ overflows_low (s.serializer v) > (Seq.length w)) ==> SZ.v res == 0) /\
  (SZ.v res > 0 ==> (
    s.serializable v /\
    SZ.v res <= Seq.length w /\
    p (Seq.slice w 0 (SZ.v res)) == Some (s.serializer v, SZ.v res)
  ))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize
    (#p: cbor_parser)
    (overflows_low: cbor_min_length p)
    (fits_high: cbor_max_length p)
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
      pure (impl_serialize_post overflows_low fits_high s v w res)
    )

let cbor_max_length_is_weaker_than
  (#p: cbor_parser)
  (f2: cbor_max_length p)
  (f1: cbor_max_length p)
: Tot prop
= forall x . Some? (f2 x) ==> (Some? (f1 x) /\ Some?.v (f1 x) <= Some?.v (f2 x))

let cbor_min_length_is_weaker_than
  (#p: cbor_parser)
  (f2: cbor_min_length p)
  (f1: cbor_min_length p)
: Tot prop
= forall x . f2 x <= f1 x

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_weaken
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize overflows_low fits_high ps r)
    ([@@@erasable]overflows_low': Ghost.erased (cbor_min_length p))
    ([@@@erasable]fits_high': Ghost.erased (cbor_max_length p))
    ([@@@erasable]sq: squash (
      overflows_low' `cbor_min_length_is_weaker_than` overflows_low /\
      fits_high' `cbor_max_length_is_weaker_than` fits_high
    ))
: impl_serialize #p overflows_low' fits_high' #(Ghost.reveal t) #tgt #inj (Ghost.reveal ps) #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
{
  i c out
}

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
    (#p: Ghost.erased cbor_parser)
    (#[@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#[@@@erasable] t: Ghost.erased typ)
    (#tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable] ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#r: rel impl_tgt tgt)
    (i: impl_serialize overflows_low fits_high ps r)
    (#tgt': Type0)
    (#impl_tgt': Type0)
    (r': rel impl_tgt' tgt')
    (sq1: squash (tgt == tgt'))
    (sq2: squash (impl_tgt == impl_tgt'))
    (sq3: squash (r' == r))
: impl_serialize #p overflows_low fits_high #(Ghost.reveal t) #tgt' #(Ghost.reveal inj) (coerce_spec (Ghost.reveal ps) tgt' sq1) #impl_tgt' r'
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
    (#p: cbor_parser)
    (overflows_low: (cbor_min_length p))
    (fits_high: (cbor_max_length p))
    (#t: typ)
    (#tgt: Type0)
    (#inj: bool)
    (s: spec t tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
    (impl_tgt2: Type0)
    (ieq: squash (impl_tgt == impl_tgt2))
: Tot (squash (impl_serialize overflows_low fits_high s #impl_tgt r == impl_serialize overflows_low fits_high s #impl_tgt2 (coerce_rel r impl_tgt2 ieq)))
= ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_always_false
    (#p: Ghost.erased cbor_parser)
    ([@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    ([@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#t: Ghost.erased typ)
    (#inj: Ghost.erased bool)
    (s: Ghost.erased (spec t (squash False) inj))
: impl_serialize #p overflows_low fits_high #_ #_ #_ s #_ (rel_always_false (squash False) (squash False))
= (c: _)
  (#v: _)
  (out: _)
{
  0sz
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_ext
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize overflows_low fits_high ps r)
    (#[@@@erasable]t': Ghost.erased typ)
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (spec t' tgt inj'))
    ([@@@erasable]sq: squash (
      (Ghost.reveal inj == true \/ Ghost.reveal inj' == true) /\
      typ_equiv t' t /\
      (forall (x: cbor) . Ghost.reveal t' x ==> ((Ghost.reveal ps'.parser x <: tgt) == Ghost.reveal ps.parser x))
    ))
: impl_serialize #p overflows_low fits_high #(Ghost.reveal t') #tgt #inj' (Ghost.reveal ps') #impl_tgt r
=
    (c: _)
    (#v: _)
    (out: _)
{
  i c out
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_bij
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize overflows_low fits_high ps r)
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
: impl_serialize #p overflows_low fits_high #t #tgt' #inj (spec_inj ps f12 f21 fprf_21_12 fprf_12_21) #impl_tgt' (rel_fun r g21 f21)
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
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize overflows_low fits_high ps1 r1)
    (#[@@@erasable]t2: Ghost.erased typ)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize overflows_low fits_high ps2 r2)
    ([@@@erasable]sq: squash (
      typ_disjoint t1 t2
    ))
: impl_serialize #p overflows_low fits_high #_ #_ #_ (spec_choice ps1 ps2) #_ (rel_either r1 r2)
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
    (#[@@@erasable]p: Ghost.erased cbor_parser)
    (#[@@@erasable]overflows_low: Ghost.erased (cbor_min_length p))
    (#[@@@erasable]fits_high: Ghost.erased (cbor_max_length p))
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize overflows_low fits_high ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize overflows_low fits_high ps1 r2)
: impl_serialize #p overflows_low fits_high #_ #_ #_ (ps1) #_ (rel_either_left r1 r2)
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
