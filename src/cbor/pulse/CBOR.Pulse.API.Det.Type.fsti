module CBOR.Pulse.API.Det.Type

val cbor_det_t: Type0

val cbor_det_map_entry_t: Type0

val cbor_det_array_iterator_t: Type0

val cbor_det_map_iterator_t: Type0

(* Abstract type of the scratch cells the application must pre-allocate
   (as references) to call cbor_det_array_append. A fixed number (two) of
   such references is required per append. The type is kept abstract; use
   CBOR.Pulse.API.Det.Dummy.dummy_cbor_det_array_append_cell to initialize
   the references. *)
val cbor_det_array_append_cell_t: Type0

(* Abstract type of the scratch cells the application must pre-allocate
   (as references) to call cbor_det_map_entry_insert. A fixed number (four)
   of such references is required per insertion (plus one cbor_det_map_entry_t
   reference). The type is kept abstract; use
   CBOR.Pulse.API.Det.Dummy.dummy_cbor_det_map_entry_insert_cell to initialize
   the references. *)
val cbor_det_map_entry_insert_cell_t: Type0
