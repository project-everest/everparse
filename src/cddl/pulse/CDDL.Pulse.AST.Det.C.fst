module CDDL.Pulse.AST.Det.C
include CDDL.Pulse.AST.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
include CBOR.Pulse.API.Det.C.Slice
open CDDL.Spec.AST.Base
module AST = CDDL.Spec.AST.Base

[@@AST.sem_attr]
let cbor_det_impl : cbor_impl cbor_det_match cbor_det_map_entry_match cbor_det_array_iterator_match cbor_det_map_iterator_match
= {
  cbor_get_major_type = cbor_det_major_type ();
  cbor_destr_int64 = cbor_det_read_uint64 ();
  cbor_get_string = cbor_det_get_string_as_slice ();
  cbor_destr_simple = cbor_det_read_simple_value ();
  cbor_get_tagged_tag = cbor_det_get_tagged_tag ();
  cbor_get_tagged_payload = cbor_det_get_tagged_payload ();
  cbor_det_parse = cbor_det_parse_full (); // TODO: support mixtures where non-deterministic CBOR objects contain .det-cbor deterministically serialized CBOR objects
  cbor_array_iterator_init = cbor_det_array_iterator_start ();
  cbor_array_iterator_is_done = cbor_det_array_iterator_is_empty ();
  cbor_array_iterator_next = cbor_det_array_iterator_next ();
  cbor_get_map_length = cbor_det_get_map_length ();
  cbor_map_get = cbor_det_map_get_gen ();
  cbor_mk_int64 = cbor_det_mk_int64 ();
  cbor_elim_int64 = cbor_det_elim_int64 ();
  cbor_mk_simple = cbor_det_mk_simple_value ();
  cbor_elim_simple = cbor_det_elim_simple ();
  cbor_mk_string = cbor_det_mk_string ();
  cbor_map_iterator_init = cbor_det_map_iterator_start ();
  cbor_map_iterator_is_empty = cbor_det_map_iterator_is_empty ();
  cbor_map_iterator_next = cbor_det_map_iterator_next ();
  cbor_map_entry_key = cbor_det_map_entry_key ();
  cbor_map_entry_value = cbor_det_map_entry_value ();
}