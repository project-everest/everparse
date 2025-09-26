module CDDL.Pulse.AST.Base
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

module AST = CDDL.Spec.AST.Base

inline_for_extraction
[@@AST.base_attr]
noeq
type cbor_impl
  (#t #t2 #t_arr #t_map: Type0)
  (vmatch: (perm -> t -> cbor -> slprop))
  (vmatch2: (perm -> t2 -> (cbor & cbor) -> slprop))
  (cbor_array_iterator_match: (perm -> t_arr -> list cbor -> slprop))
  (cbor_map_iterator_match: (perm -> t_map -> list (cbor & cbor) -> slprop))
= {
  cbor_share: share_t vmatch;
  cbor_gather: gather_t vmatch;
  cbor_get_major_type: get_major_type_t vmatch;
  cbor_destr_int64: read_uint64_t vmatch;
  cbor_get_string: get_string_t vmatch;
  cbor_destr_simple: read_simple_value_t vmatch;
  cbor_get_tagged_tag: get_tagged_tag_t vmatch;
  cbor_get_tagged_payload: get_tagged_payload_t vmatch;
  cbor_det_parse: cbor_det_parse_t vmatch; // TODO: support mixtures where non-deterministic CBOR objects contain .det-cbor deterministically serialized CBOR objects
  cbor_array_iterator_init: array_iterator_start_t vmatch cbor_array_iterator_match;
  cbor_array_iterator_is_done: array_iterator_is_empty_t cbor_array_iterator_match;
  cbor_array_iterator_length: array_iterator_length_t cbor_array_iterator_match;
  cbor_array_iterator_next: array_iterator_next_t vmatch cbor_array_iterator_match;
  cbor_array_iterator_truncate: array_iterator_truncate_t cbor_array_iterator_match;
  cbor_array_iterator_share: share_t cbor_array_iterator_match;
  cbor_array_iterator_gather: gather_t cbor_array_iterator_match;
  cbor_get_map_length: get_map_length_t vmatch;
  cbor_map_get: map_get_t vmatch;
  cbor_mk_int64: mk_int64_t vmatch;
  cbor_elim_int64: elim_int64_t vmatch;
  cbor_mk_simple: mk_simple_t vmatch;
  cbor_elim_simple: elim_simple_t vmatch;
  cbor_mk_string: mk_string_t vmatch;
  cbor_map_iterator_init: map_iterator_start_t vmatch cbor_map_iterator_match;
  cbor_map_iterator_is_empty: map_iterator_is_empty_t cbor_map_iterator_match;
  cbor_map_iterator_next: map_iterator_next_t vmatch2 cbor_map_iterator_match;
  cbor_map_iterator_share: share_t cbor_map_iterator_match;
  cbor_map_iterator_gather: gather_t cbor_map_iterator_match;
  cbor_mk_map_entry: mk_map_entry_t vmatch vmatch2;
  cbor_map_entry_key: map_entry_key_t vmatch2 vmatch;
  cbor_map_entry_value: map_entry_value_t vmatch2 vmatch;
  cbor_map_entry_share: share_t vmatch2;
  cbor_map_entry_gather: gather_t vmatch2;
  cbor_impl_utf8_correct: impl_utf8_correct_t;
  cbor_det_serialize: cbor_det_serialize_t vmatch;
  cbor_det_serialize_string: cbor_det_serialize_string_t;
  cbor_det_serialize_tag: cbor_det_serialize_tag_t;
  cbor_det_serialize_array: cbor_det_serialize_array_t;
  cbor_det_serialize_map_insert: cbor_det_serialize_map_insert_t;
  cbor_det_serialize_map: cbor_det_serialize_map_t;
}

