module CDDL.Pulse.Serialize.MapGroup
include CDDL.Pulse.Serialize.Base
open CDDL.Pulse.Serialize.Misc // for literals
include CDDL.Pulse.Parse.MapGroup
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

let impl_serialize_map_group_pre
  (count: U64.t)
  (size: SZ.t)
  (l: cbor_map)
  (w: Seq.seq U8.t)
: Tot prop
= cbor_map_length l == U64.v count /\
  SZ.v size <= Seq.length w /\
  Seq.slice w 0 (SZ.v size) `Seq.equal` Cbor.cbor_det_serialize_map l

let impl_serialize_map_group_valid
  (l: cbor_map)
  (#t: det_map_group)
  (#fp: typ)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (v: tgt)
  (len: nat)
: Tot bool
=   s.mg_serializable v &&
    cbor_map_disjoint_tot l (s.mg_serializer v) &&
    FStar.UInt.fits (cbor_map_length l + cbor_map_length (s.mg_serializer v)) 64 &&
    Seq.length (Cbor.cbor_det_serialize_map (cbor_map_union l (s.mg_serializer v))) <= len

let impl_serialize_map_group_post
  (count: U64.t)
  (size: SZ.t)
  (l: cbor_map)
  (#t: det_map_group)
  (#fp: typ)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (v: tgt)
  (w: Seq.seq U8.t)
  (res: bool)
: Tot prop
= (res == true <==> impl_serialize_map_group_valid l s v (Seq.length w)) /\
  (res == true ==> (
    impl_serialize_map_group_pre count size (cbor_map_union l (s.mg_serializer v)) w
  ))

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_group
    (#t: det_map_group)
    (#fp: typ)
    (#tgt: Type0)
    (#inj: bool)
    (s: mg_spec t fp tgt inj)
    (#impl_tgt: Type0)
    (r: rel impl_tgt tgt)
=
  (c: impl_tgt) ->
  (#v: Ghost.erased tgt) ->
  (out: S.slice U8.t) ->
  (out_count: R.ref U64.t) ->
  (out_size: R.ref SZ.t) ->
  (l: Ghost.erased (cbor_map)) ->
  stt bool
    (exists* w count size . r c v ** pts_to out w ** pts_to out_count count ** pts_to out_size size **
      pure (impl_serialize_map_group_pre count size l w)
    )
    (fun res -> exists* w count' size' . r c v ** pts_to out w ** pts_to out_count count' ** pts_to out_size size' ** pure (
      impl_serialize_map_group_post count' size' l s v w res
    ))

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map
   (cbor_det_serialize_map: cbor_det_serialize_map_t)
    (# [@@@erasable] t: Ghost.erased det_map_group)
    (# [@@@erasable] fp: Ghost.erased typ)
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_map_group s r)
    (sq: squash (map_group_footprint t fp))
: impl_serialize #_ #_ #_ (spec_map_group s) #_ r
