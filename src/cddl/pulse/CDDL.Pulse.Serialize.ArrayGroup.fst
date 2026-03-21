module CDDL.Pulse.Serialize.ArrayGroup
#lang-pulse
include CDDL.Pulse.Serialize.Base
include CDDL.Pulse.Parse.ArrayGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module Gen = CDDL.Pulse.Serialize.Gen.ArrayGroup

(* Bridge lemma: non-Gen pre implies Gen pre *)
let impl_serialize_array_group_pre_to_gen
  (count: U64.t) (size: SZ.t) (l: list Cbor.cbor) (w: Seq.seq U8.t)
: Lemma
  (requires impl_serialize_array_group_pre count size l w)
  (ensures Gen.impl_serialize_array_group_pre Gen.cbor_det_parse count size l w)
  [SMTPat (impl_serialize_array_group_pre count size l w)]
= Gen.cbor_det_parse_list_serialize_list_equiv (U64.v count) (Seq.slice w 0 (SZ.v size)) l (SZ.v size)

(* Bridge lemma: Gen pre implies non-Gen pre *)
let impl_serialize_array_group_pre_from_gen
  (count: U64.t) (size: SZ.t) (l: list Cbor.cbor) (w: Seq.seq U8.t)
: Lemma
  (requires Gen.impl_serialize_array_group_pre Gen.cbor_det_parse count size l w)
  (ensures impl_serialize_array_group_pre count size l w)
  [SMTPat (Gen.impl_serialize_array_group_pre Gen.cbor_det_parse count size l w)]
= Gen.cbor_det_parse_list_serialize_list_equiv (U64.v count) (Seq.slice w 0 (SZ.v size)) l (SZ.v size)

(* Bridge lemma: Gen post implies non-Gen pre + post (for intro) *)
let rec cbor_det_max_length_is_serialize_list_length
  (l: list Cbor.cbor)
: Lemma
  (ensures Gen.cbor_array_max_length Gen.cbor_det_max_length l == Some (Seq.length (Cbor.cbor_det_serialize_list l)))
  (decreases l)
= match l with
  | [] -> Cbor.cbor_det_serialize_list_nil ()
  | a :: q ->
    cbor_det_max_length_is_serialize_list_length q;
    Cbor.cbor_det_serialize_list_cons a q

let rec cbor_det_min_length_is_serialize_list_length
  (l: list Cbor.cbor)
: Lemma
  (ensures Gen.cbor_array_min_length Gen.cbor_det_min_length l == Seq.length (Cbor.cbor_det_serialize_list l))
  (decreases l)
= match l with
  | [] -> Cbor.cbor_det_serialize_list_nil ()
  | a :: q ->
    cbor_det_min_length_is_serialize_list_length q;
    Cbor.cbor_det_serialize_list_cons a q

let impl_serialize_array_group_post_gen_to_local
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (count0: U64.t) (size0: SZ.t)
  (count': U64.t) (size': SZ.t)
  (l: list Cbor.cbor)
  (v: tgt)
  (w0: Seq.seq U8.t) (w: Seq.seq U8.t) (res: bool)
: Lemma
  (requires
    impl_serialize_array_group_pre count0 size0 l w0 /\
    Seq.length w == Seq.length w0 /\
    Gen.impl_serialize_array_group_post Gen.cbor_det_min_length Gen.cbor_det_max_length count' size' size0 l s v w0 w res)
  (ensures
    impl_serialize_array_group_pre count0 size0 l w /\
    impl_serialize_array_group_post count' size' l s v w res)
  [SMTPat (Gen.impl_serialize_array_group_post Gen.cbor_det_min_length Gen.cbor_det_max_length count' size' size0 l s v w0 w res);
   SMTPat (impl_serialize_array_group_pre count0 size0 l w0)]
= if s.ag_serializable v then begin
    cbor_det_max_length_is_serialize_list_length (s.ag_serializer v);
    cbor_det_min_length_is_serialize_list_length (s.ag_serializer v);
    Cbor.cbor_det_serialize_list_append l (s.ag_serializer v);
    cbor_det_max_length_is_serialize_list_length (List.Tot.append l (s.ag_serializer v));
    if res then
      Gen.cbor_det_parse_list_serialize_list_equiv (U64.v count') (Seq.slice w 0 (SZ.v size')) (List.Tot.append l (s.ag_serializer v)) (SZ.v size')
  end

(* Bridge lemma: non-Gen pre + post implies Gen post (for elim) *)
let impl_serialize_array_group_post_local_to_gen
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (count0: U64.t) (size0: SZ.t)
  (count': U64.t) (size': SZ.t)
  (l: list Cbor.cbor)
  (v: tgt)
  (w: Seq.seq U8.t) (res: bool)
: Lemma
  (requires
    impl_serialize_array_group_pre count0 size0 l w /\
    impl_serialize_array_group_post count' size' l s v w res)
  (ensures
    Gen.impl_serialize_array_group_post Gen.cbor_det_min_length Gen.cbor_det_max_length count' size' size0 l s v w w res)
  [SMTPat (impl_serialize_array_group_post count' size' l s v w res);
   SMTPat (impl_serialize_array_group_pre count0 size0 l w)]
= if s.ag_serializable v then begin
    cbor_det_max_length_is_serialize_list_length (s.ag_serializer v);
    cbor_det_min_length_is_serialize_list_length (s.ag_serializer v);
    Cbor.cbor_det_serialize_list_append l (s.ag_serializer v);
    cbor_det_max_length_is_serialize_list_length (List.Tot.append l (s.ag_serializer v));
    if res then
      Gen.cbor_det_parse_list_serialize_list_equiv (U64.v count') (Seq.slice w 0 (SZ.v size')) (List.Tot.append l (s.ag_serializer v)) (SZ.v size')
  end

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_intro'
    (#[@@@erasable] t: Ghost.erased (array_group None))
    (#[@@@erasable] tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable] r: rel impl_tgt tgt)
    (i: Gen.impl_serialize_array_group Gen.cbor_det_min_length Gen.cbor_det_max_length s r)
:  impl_serialize_array_group s r
=
  (c: _)
  (#v: _)
  (#count0: _)
  (#size0: _)
  (out: _)
  (out_count: _)
  (out_size: _)
  (l: _)
{
  S.pts_to_len out;
  let res = i c out out_count out_size l;
  S.pts_to_len out;
  res
}

let impl_serialize_array_group_intro = impl_serialize_array_group_intro'

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_array_group_elim'
    (#[@@@erasable] t: Ghost.erased (array_group None))
    (#[@@@erasable] tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_array_group s r)
: Gen.impl_serialize_array_group Gen.cbor_det_min_length Gen.cbor_det_max_length s r
=
  (c: _)
  (#v: _)
  (out: _)
  (out_count: _)
  (out_size: _)
  (#w0: _)
  (#size_before: _)
  (l: _)
{
  S.pts_to_len out;
  let res = i c out out_count out_size l;
  S.pts_to_len out;
  res
}

let impl_serialize_array_group_elim = impl_serialize_array_group_elim'

let impl_serialize_array cbor_det_serialize_array i =
  impl_serialize_intro (Gen.impl_det_serialize_array cbor_det_serialize_array (impl_serialize_array_group_elim i))

let impl_serialize_array_group_ext i ps' sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_ext (impl_serialize_array_group_elim i) ps' sq)

let impl_serialize_array_group_bij i f12 f21 fprf_21_12 fprf_12_21 g12 g21 gprf_21_12 gprf_12_21 =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_bij (impl_serialize_array_group_elim i) f12 f21 fprf_21_12 fprf_12_21 g12 g21 gprf_21_12 gprf_12_21)

let impl_serialize_array_group_item i =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_item (impl_serialize_elim i))

let impl_serialize_array_group_concat i1 i2 sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_concat (impl_serialize_array_group_elim i1) (impl_serialize_array_group_elim i2) sq)

let impl_serialize_array_group_choice i1 i2 sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_choice (impl_serialize_array_group_elim i1) (impl_serialize_array_group_elim i2) sq)

let impl_serialize_array_group_choice' i1 i2 sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_choice' (impl_serialize_array_group_elim i1) (impl_serialize_array_group_elim i2) sq)

let impl_serialize_array_group_zero_or_one i1 sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_zero_or_one (impl_serialize_array_group_elim i1) sq)

let impl_serialize_array_group_zero_or_more is_empty length share gather truncate i1 sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_zero_or_more is_empty length share gather truncate (impl_serialize_array_group_elim i1) sq)

let impl_serialize_array_group_one_or_more is_empty length share gather truncate i1 sq =
  impl_serialize_array_group_intro (Gen.impl_serialize_array_group_one_or_more is_empty length share gather truncate (impl_serialize_array_group_elim i1) sq)
