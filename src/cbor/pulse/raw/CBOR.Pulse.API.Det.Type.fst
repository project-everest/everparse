module CBOR.Pulse.API.Det.Type
module Raw = CBOR.Pulse.Raw.Type

let cbor_det_t = Raw.cbor_raw
let cbor_det_map_entry_t = Raw.cbor_map_entry
let cbor_det_array_iterator_t = CBOR.Pulse.Raw.Read.cbor_array_iterator
let cbor_det_map_iterator_t = CBOR.Pulse.Raw.Read.cbor_map_iterator

let dummy_cbor_det_t _ = Raw.CBOR_Case_Simple 0uy
