module CBOR.SteelST.Raw
include CBOR.Spec

// A "raw" API to parse and serialize CBOR objects without a data type

module DummyArray = CBOR.SteelST.Array // for dependencies only

let validate_raw_data_item = CBOR.SteelST.Validate.validate_raw_data_item
let jump_raw_data_item = CBOR.SteelST.Validate.jump_raw_data_item
let jump_header = CBOR.SteelST.Validate.jump_header

let validate_canonical_cbor_data_item = CBOR.SteelST.Map.validate_canonical_cbor_data_item

let read_major_type #va = CBOR.SteelST.Validate.read_major_type #va
let read_argument_as_uint64 #va = CBOR.SteelST.Validate.read_argument_as_uint64 #va
let read_int64 #va = CBOR.SteelST.Read.read_int64 #va
let read_simple_value #va = CBOR.SteelST.Read.read_simple_value #va
let focus_string #va = CBOR.SteelST.Read.focus_string #va

let write_simple_value = CBOR.SteelST.Write.write_simple_value
let write_int64 = CBOR.SteelST.Write.write_int64
let finalize_raw_data_item_string = CBOR.SteelST.Write.finalize_raw_data_item_string

let l2r_write_uint64_header = CBOR.SteelST.Write.l2r_write_uint64_header
