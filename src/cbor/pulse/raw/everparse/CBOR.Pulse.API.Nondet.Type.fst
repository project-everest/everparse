module CBOR.Pulse.API.Nondet.Type
module Raw = CBOR.Pulse.Raw.EverParse.Type
module I = LowParse.PulseParse.Iterator.Type

let cbor_nondet_t = Raw.cbor_raw

let cbor_nondet_array_iterator_t = I.iterator Raw.cbor_raw

let cbor_nondet_map_iterator_t = I.iterator (Raw.cbor_map_entry Raw.cbor_raw)

let cbor_nondet_map_entry_t = Raw.cbor_map_entry Raw.cbor_raw

let cbor_nondet_array_append_cell_t = I.mixed_list Raw.cbor_raw
