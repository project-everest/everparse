module CDDL.Pulse.Serialize.ArrayGroup
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

let impl_serialize_array_group_pre
  (count: U64.t)
  (size: SZ.t)
  (l: list Cbor.cbor)
  (w: Seq.seq U8.t)
: Tot prop
= List.Tot.length l == U64.v count /\
  SZ.v size <= Seq.length w /\
  Seq.slice w 0 (SZ.v size) `Seq.equal` Cbor.cbor_det_serialize_list l

let impl_serialize_array_group_post
  (count: U64.t)
  (size: SZ.t)
  (l: list Cbor.cbor)
  (#t: array_group None)
  (#tgt: Type0)
  (#inj: bool)
  (s: ag_spec t tgt inj)
  (v: tgt)
  (w: Seq.seq U8.t)
  (res: bool)
: Tot prop
= (res == true <==> (
    s.ag_serializable v /\
    FStar.UInt.fits (List.Tot.length l + List.Tot.length (s.ag_serializer v)) 64 /\
    Seq.length (Cbor.cbor_det_serialize_list (List.Tot.append l (s.ag_serializer v))) <= Seq.length w
  )) /\
  (res == true ==> (
    impl_serialize_array_group_pre count size (List.Tot.append l (s.ag_serializer v)) w
  ))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_array_group
    (#t: array_group None)
    (#tgt: Type0)
    (#inj: bool)
    (s: ag_spec t tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
  (c: impl_tgt) ->
  (#v: Ghost.erased tgt) ->
  (out: S.slice U8.t) ->
  (out_count: R.ref U64.t) ->
  (out_size: R.ref SZ.t) ->
  (l: Ghost.erased (list Cbor.cbor)) ->
  stt bool
    (exists* w count size . r c v ** pts_to out w ** pts_to out_count count ** pts_to out_size size **
      pure (impl_serialize_array_group_pre count size l w)
    )
    (fun res -> exists* w count' size' . r c v ** pts_to out w ** pts_to out_count count' ** pts_to out_size size' ** pure (
      impl_serialize_array_group_post count' size' l s v w res
    ))

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array
   (cbor_det_serialize_array: cbor_det_serialize_array_t)
    (# [@@@erasable] t: Ghost.erased (array_group None))
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_array_group s r)
: impl_serialize #_ #_ #_ (spec_array_group s) #_ r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_ext
    (#[@@@erasable]t: Ghost.erased (array_group None))
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (ag_spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_array_group ps r)
    (#[@@@erasable]t': Ghost.erased (array_group None))
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (ag_spec t' tgt inj'))
    ([@@@erasable]sq: squash (
      (Ghost.reveal inj == true \/ Ghost.reveal inj' == true) /\
      array_group_equiv t' t /\
      (forall (x: list cbor) . array_group_parser_spec_refinement (Ghost.reveal t') x ==> ((ps'.ag_parser x <: tgt) == ps.ag_parser x))
    ))
: impl_serialize_array_group #(Ghost.reveal t') #tgt #inj' (Ghost.reveal ps') #impl_tgt r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_item
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (spec t tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize ps r)
: impl_serialize_array_group #_ #_ #_ (ag_spec_item ps) #_ r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_array_group_concat
    (#[@@@erasable]t1: Ghost.erased (array_group None))
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (ag_spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_array_group ps1 r1)
    (#[@@@erasable]t2: Ghost.erased (array_group None))
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (ag_spec t2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_array_group ps2 r2)
    (sq: squash (
      array_group_concat_unique_weak t1 t2
    ))
: impl_serialize_array_group #_ #_ #_ (ag_spec_concat ps1 ps2) #_ (rel_pair r1 r2)
