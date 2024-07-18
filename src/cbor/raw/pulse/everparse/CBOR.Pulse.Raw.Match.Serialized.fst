module CBOR.Pulse.Raw.Match.Serialized
open CBOR.Spec.Raw.Format
open CBOR.Pulse.Raw.Format
open LowParse.Pulse.VCList

module U64 = FStar.UInt64

let cbor_match_serialized_payload_array
  c p r
= exists* r' .
    pts_to_serialized (tot_serialize_nlist (U64.v c.cbor_serialized_header.value)  serialize_raw_data_item) c.cbor_serialized_payload #(p `perm_mul` c.cbor_serialized_perm) r' **
    pure (r == r')

let cbor_match_serialized_payload_map
  c p r
= exists* r' .
    pts_to_serialized (tot_serialize_nlist (U64.v c.cbor_serialized_header.value)  (serialize_raw_data_item `tot_serialize_nondep_then` serialize_raw_data_item)) c.cbor_serialized_payload #(p `perm_mul` c.cbor_serialized_perm) r' **
    pure (r == r')

let cbor_match_serialized_payload_tagged
  c p r
= pts_to_serialized serialize_raw_data_item c.cbor_serialized_payload #(p `perm_mul` c.cbor_serialized_perm) r
