module CBOR.Pulse.API.Det.Dummy

(* The dummy placeholder value used by the Det C and Rust APIs lives here
   rather than in CBOR.Pulse.API.Det.Type so that the Type bundle, which is
   extracted into the CBORDetType header, stays header-only (no .c file).
   It is `friend`ed to Det.Type to construct the abstract `cbor_det_t`, and
   `inline_for_extraction` so it is inlined at every call site and never
   emitted as a standalone definition. *)

friend CBOR.Pulse.API.Det.Type

module Raw = CBOR.Pulse.Raw.EverParse.Type
module T = CBOR.Pulse.API.Det.Type

inline_for_extraction
let dummy_cbor_det_t (_: unit) : T.cbor_det_t = Raw.CBOR_Case_Simple 0uy
