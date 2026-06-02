module CBOR.Pulse.API.Nondet.Type

val cbor_nondet_t: Type0

val cbor_nondet_array_iterator_t: Type0

val cbor_nondet_map_iterator_t: Type0

val cbor_nondet_map_entry_t: Type0

(* Abstract type of the scratch cells the application must pre-allocate
   (as references) to call cbor_nondet_array_append. A fixed number (two) of
   such references is required per append. The type is kept abstract; use
   CBOR.Pulse.API.Nondet.Dummy.dummy_cbor_nondet_array_append_cell to
   initialize the references. *)
val cbor_nondet_array_append_cell_t: Type0
