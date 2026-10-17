module CDDL.Pulse.Serialize.Gen.MapGroup.Choice
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
val impl_serialize_map_group_nop
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (_: unit)
: impl_serialize_map_group p minl maxl mg_spec_nop rel_unit

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_choice
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group p minl maxl ps1 r1)
    (#[@@@erasable]t2: Ghost.erased det_map_group)
    (#[@@@erasable]tgt2: Type0)
    (#[@@@erasable] fp2: Ghost.erased map_constraint)
    (#[@@@erasable] inj2: Ghost.erased bool)
    (#[@@@erasable]ps2: Ghost.erased (mg_spec t2 fp2 tgt2 inj2))
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt2)
    (i2: impl_serialize_map_group p minl maxl ps2 r2)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      map_group_footprint t2 fp2 /\
      map_group_choice_compatible t1 t2
    ))
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ (mg_spec_choice ps1 ps2) #_ (rel_either r1 r2)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_zero_or_one
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group p minl maxl ps1 r1)
    (sq: squash (
      map_group_footprint t1 fp1 /\
      MapGroupFail? (apply_map_group_det t1 cbor_map_empty)
    ))
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ (mg_spec_zero_or_one ps1) #_ (rel_option r1)

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_group_either_left
  (#p: Ghost.erased bare_cbor_map_parser)
  (#minl: Ghost.erased (cbor -> nat))
  (#maxl: Ghost.erased (cbor -> option nat))
    (#[@@@erasable]t1: Ghost.erased det_map_group)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] fp1: Ghost.erased map_constraint)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (mg_spec t1 fp1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize_map_group p minl maxl ps1 r1)
    (#impl_tgt2: Type0)
    (#[@@@erasable]r2: rel impl_tgt2 tgt1)
    (i2: impl_serialize_map_group p minl maxl ps1 r2)
: impl_serialize_map_group p minl maxl #_ #_ #_ #_ ps1 #_ (rel_either_left r1 r2)
