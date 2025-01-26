module CBOR.Pulse.API.Det.C.Copy
include CBOR.Pulse.API.Det.C
open Pulse.Lib.Pervasives

[@@CAbstractStruct]
val freeable_cbor_det_t: Type0

val freeable: freeable_cbor_det_t -> slprop

val get_cbor_from_freeable: freeable_cbor_det_t -> cbor_det_t

val cbor_copy () : cbor_copy_t cbor_det_match freeable get_cbor_from_freeable

val cbor_free () : cbor_free_t freeable
