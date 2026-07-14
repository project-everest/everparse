module CBOR.Pulse.API.Det.Dummy

(* The dummy placeholder value used by the Det C and Rust APIs lives here
   rather than in CBOR.Pulse.API.Det.Type so that the Type bundle, which is
   extracted into the CBORDetType header, stays header-only (no .c file).
   It is `friend`ed to Det.Type to construct the abstract `cbor_det_t`, and is
   exported under the unqualified name `dummy_cbor_det_t` via
   `-no-prefix CBOR.Pulse.API.Det.Dummy` in the krml extraction Makefiles,
   matching the symbol baseline EverParse exposes. *)

friend CBOR.Pulse.API.Det.Type

module Raw = CBOR.Pulse.Raw.Type
module T = CBOR.Pulse.API.Det.Type

let dummy_cbor_det_t _ = Raw.CBOR_Case_Simple 0uy
