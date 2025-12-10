module CBOR.Pulse.API.Nondet.Type
open CBOR.Pulse.Raw.Match

type cbor_nondet_t = cbor_raw

let cbor_nondet_array_iterator_t = CBOR.Pulse.Raw.Read.cbor_array_iterator

let cbor_nondet_map_iterator_t = CBOR.Pulse.Raw.Read.cbor_map_iterator

let cbor_nondet_map_entry_t = cbor_map_entry
