module CBORTest.C
#lang-pulse
open CBOR.Spec.Constants
open Pulse.Lib.Pervasives
module Base = CBORTest.Base
module Cbor = CBOR.Pulse.API.Det.C.Slice
module CborBase = CBOR.Pulse.API.Base

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_string_from_array () =
  Cbor.mk_string_from_array (Cbor.mk_string_from_slice (Cbor.cbor_det_mk_string_from_arrayptr ()))

fn main
  (_: unit)
requires emp
returns res: Base.res_t
ensures emp
{
  Base.main
    Cbor.cbor_det_match
    Cbor.cbor_det_map_entry_match
    (Cbor.cbor_det_major_type ())
    (Cbor.cbor_det_equal ())
    (Cbor.cbor_det_parse_full ())
    (Cbor.cbor_det_serialize_full ())
    (cbor_det_mk_string_from_array ())
    (Cbor.cbor_det_mk_array_from_array ())
    (Cbor.cbor_det_get_array_length ())
    (Cbor.cbor_det_get_array_item ())
    (Cbor.cbor_det_mk_tagged ())
    (Cbor.cbor_det_mk_int64 ())
    (Cbor.cbor_det_elim_int64 ())
    (Cbor.cbor_det_read_uint64 ())
    (Cbor.cbor_det_mk_map_from_array)
    (CborBase.map_get_as_option (Cbor.cbor_det_map_get ()))
    (Cbor.cbor_det_mk_map_entry ())
}
