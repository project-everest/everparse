module CDDL.Pulse.Serialize.Gen.MapGroup.Ext
include CDDL.Pulse.Serialize.Gen.MapGroup.Base
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
module EqTest = CDDL.Spec.EqTest

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_ext
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t: Ghost.erased (det_map_group))
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group p minl maxl ps r)
    (#[@@@erasable]t': Ghost.erased (det_map_group))
    (# [@@@erasable] fp': Ghost.erased map_constraint)
    (#[@@@erasable] inj': Ghost.erased bool)
    ([@@@erasable]ps': Ghost.erased (mg_spec t' fp' tgt inj'))
    ([@@@erasable]sq: squash (
      t' == t /\
      (forall (x: tgt) . (Ghost.reveal ps').mg_serializable x <==> (Ghost.reveal ps).mg_serializable x) /\
      (forall (x: tgt) . (Ghost.reveal ps').mg_serializable x ==> (
        (Ghost.reveal ps).mg_serializable x /\
        (Ghost.reveal ps').mg_serializer x `cbor_map_equal` (Ghost.reveal ps).mg_serializer x
      )) /\
      (forall (x: tgt) . (Ghost.reveal ps').mg_size x == (Ghost.reveal ps).mg_size x)
    ))
: impl_serialize_map_group p minl maxl #(Ghost.reveal t') #(Ghost.reveal fp') #tgt #inj' (Ghost.reveal ps') #impl_tgt r

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_ext'
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t: Ghost.erased (det_map_group))
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable]ps: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable]r: rel impl_tgt tgt)
    (i: impl_serialize_map_group p minl maxl ps r)
    ([@@@erasable] fp': Ghost.erased map_constraint)
    (sq: squash (
      map_constraint_equiv fp fp'
    ))
: impl_serialize_map_group p minl maxl #(Ghost.reveal t) #(Ghost.reveal fp') #tgt #inj (mg_spec_ext ps fp' ps.mg_size ps.mg_serializable) #impl_tgt r
