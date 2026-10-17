module CDDL.Pulse.Serialize.Gen.MapGroup.Map
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
val impl_det_serialize_map
   (cbor_det_serialize_map: cbor_det_serialize_map_t)
    (# [@@@erasable] t: Ghost.erased det_map_group)
    (# [@@@erasable] fp: Ghost.erased map_constraint)
    (# [@@@erasable] tgt: Type0)
    (# [@@@erasable] inj: Ghost.erased bool)
    (# [@@@erasable] s: Ghost.erased (mg_spec t fp tgt inj) { map_group_footprint t fp })
    (#impl_tgt: Type0)
    (# [@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_map_group cbor_det_parse_map cbor_det_min_length cbor_det_max_length s r)
: impl_serialize #_ cbor_det_min_length cbor_det_max_length #_ #_ #_ (spec_map_group s) #_ r
