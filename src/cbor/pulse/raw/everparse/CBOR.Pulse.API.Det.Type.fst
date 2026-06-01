module CBOR.Pulse.API.Det.Type
module Raw = CBOR.Pulse.Raw.EverParse.Type
module I = LowParse.PulseParse.Iterator.Type

let cbor_det_t = Raw.cbor_raw
let cbor_det_map_entry_t = Raw.cbor_map_entry Raw.cbor_raw
let cbor_det_array_iterator_t = I.iterator Raw.cbor_raw
let cbor_det_map_iterator_t = I.iterator (Raw.cbor_map_entry Raw.cbor_raw)
