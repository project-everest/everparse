module CBOR.Pulse.API.Nondet.Dummy

(* The dummy placeholder values used by the Nondet C and Rust APIs live here
   rather than in CBOR.Pulse.API.Nondet.Type so that the Type bundle, which is
   extracted into the CBORNondetType header, stays header-only (no .c file).
   It is `friend`ed to Nondet.Type to construct the abstract `cbor_nondet_t`.
   It is `inline_for_extraction` so it is inlined at every call site, but it is
   also emitted as a standalone definition (inline_for_extraction does not
   suppress extraction). That standalone body is bundled into CBORNondet.c (not
   the Type bundle) and exported under the unqualified name via
   `-no-prefix CBOR.Pulse.API.Nondet.Dummy` in the krml extraction Makefiles. *)

friend CBOR.Pulse.API.Nondet.Type

module Raw = CBOR.Pulse.Raw.EverParse.Type
module T = CBOR.Pulse.API.Nondet.Type
module IT = LowParse.PulseParse.Iterator.Type

inline_for_extraction
let dummy_cbor_nondet_t (_: unit) : T.cbor_nondet_t = Raw.CBOR_Case_Simple 0uy

inline_for_extraction
let dummy_cbor_nondet_array_append_cell (_: unit) : T.cbor_nondet_array_append_cell_t =
  IT.Base IT.Empty
