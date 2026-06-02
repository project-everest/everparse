module CBOR.Pulse.API.Det.Dummy

(* The dummy placeholder value used by the Det C and Rust APIs lives here
   rather than in CBOR.Pulse.API.Det.Type so that the Type bundle, which is
   extracted into the CBORDetType header, stays header-only (no .c file).
   It is `friend`ed to Det.Type to construct the abstract `cbor_det_t`. It is
   `inline_for_extraction` so it is inlined at every call site, but it is also
   emitted as a standalone definition (inline_for_extraction does not suppress
   extraction). That standalone body is bundled into CBORDet.c (not the Type
   bundle) and exported under the unqualified name `dummy_cbor_det_t` via
   `-no-prefix CBOR.Pulse.API.Det.Dummy` in the krml extraction Makefiles,
   matching the symbol baseline EverParse exposes. *)

friend CBOR.Pulse.API.Det.Type

module Raw = CBOR.Pulse.Raw.EverParse.Type
module T = CBOR.Pulse.API.Det.Type
module IT = LowParse.PulseParse.Iterator.Type

inline_for_extraction
let dummy_cbor_det_t (_: unit) : T.cbor_det_t = Raw.CBOR_Case_Simple 0uy

inline_for_extraction
let dummy_cbor_det_array_append_cell (_: unit) : T.cbor_det_array_append_cell_t =
  IT.Base IT.Empty
