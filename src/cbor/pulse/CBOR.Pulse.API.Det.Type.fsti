module CBOR.Pulse.API.Det.Type

[@@CAbstractStruct]
val cbor_det_t: Type0
[@@CAbstractStruct]
val cbor_det_map_entry_t: Type0
[@@CAbstractStruct]
val cbor_det_array_iterator_t: Type0
[@@CAbstractStruct]
val cbor_det_map_iterator_t: Type0

inline_for_extraction noextract [@@noextract_to "krml"]
val dummy_cbor_det_t (_: unit) : cbor_det_t
