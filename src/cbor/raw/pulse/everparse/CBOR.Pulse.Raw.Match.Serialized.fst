module CBOR.Pulse.Raw.Match.Serialized
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Pulse.VCList

module U64 = FStar.UInt64

let cbor_match_serialized_payload_array
  c p r
= exists* n (r': nlist n raw_data_item) .
    pts_to_serialized (tot_serialize_nlist n serialize_raw_data_item) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_map
  c p r
= exists* n (r' : nlist n (raw_data_item & raw_data_item)) .
    pts_to_serialized (tot_serialize_nlist n (serialize_raw_data_item `tot_serialize_nondep_then` serialize_raw_data_item)) c #p r' **
    pure (r == r')

let cbor_match_serialized_payload_tagged
  c p r
= pts_to_serialized serialize_raw_data_item c #p r
