module CBOR.SteelST.Raw
include CBOR.Spec.Format

// A "raw" API to parse and serialize CBOR objects without a data type

module DummyArray = CBOR.SteelST.Raw.Array // for dependencies only

let validate_raw_data_item = CBOR.SteelST.Raw.Validate.validate_raw_data_item
let jump_raw_data_item = CBOR.SteelST.Raw.Validate.jump_raw_data_item
let jump_header = CBOR.SteelST.Raw.Validate.jump_header

let validate_canonical_cbor_data_item = CBOR.SteelST.Raw.Map.validate_canonical_cbor_data_item

let read_major_type #va = CBOR.SteelST.Raw.Validate.read_major_type #va
let read_argument_as_uint64 #va = CBOR.SteelST.Raw.Validate.read_argument_as_uint64 #va
let read_int64 #va = CBOR.SteelST.Raw.Read.read_int64 #va
let read_simple_value #va = CBOR.SteelST.Raw.Read.read_simple_value #va
let focus_string #va = CBOR.SteelST.Raw.Read.focus_string #va

let write_simple_value = CBOR.SteelST.Raw.Write.write_simple_value
let write_int64 = CBOR.SteelST.Raw.Write.write_int64
let finalize_raw_data_item_string = CBOR.SteelST.Raw.Write.finalize_raw_data_item_string
