module CBOR.Pulse.API.Det.Dummy

module T = CBOR.Pulse.API.Det.Type

inline_for_extraction
val dummy_cbor_det_t (_: unit) : T.cbor_det_t

inline_for_extraction
val dummy_cbor_det_array_append_cell (_: unit) : T.cbor_det_array_append_cell_t

inline_for_extraction
val dummy_cbor_det_map_entry_insert_cell (_: unit) : T.cbor_det_map_entry_insert_cell_t

inline_for_extraction
val dummy_cbor_det_map_entry (_: unit) : T.cbor_det_map_entry_t
