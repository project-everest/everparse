This package contains the supplementary material for ACM CCS 2025 submission.

Section 2.2:
- the Pulse implementation combinators are in `src/lowparse/pulse`
- the recursive combinator specification is in `src/lowparse/LowParse.Spec.Recursive.fst*`
- in particular, the validator and jumper for the recursive format is in `src/lowparse/pulse/LowParse.Pulse.Recursive.fst`

Section 3.2:
- the CBOR raw data type is defined in `src/cbor/spec/raw/CBOR.Spec.Raw.Base.fst`
- the CBOR raw data parser and serializer specifications are defined in `src/cbor/spec/raw/everparse/CBOR.Spec.Raw.EverParse.fst`
- the CBOR raw data validator, jumper implementation, accessors, and the CBOR header value reader and writer, as well as the validator and jumper for the deterministic format, are defined in `src/cbor/pulse/raw/everparse/CBOR.Pulse.Raw.EverParse.Format.fst`
- the low-level datatype for CBOR raw data is defined in `src/cbor/pulse/raw/CBOR.Pulse.Raw.Type.fst`
- the separation logic relation for CBOR raw data is defined in `src/cbor/pulse/raw/CBOR.Pulse.Raw.Match.fst`
- the CBOR raw data serializer implementations are defined in `src/cbor/pulse/raw/everparse/CBOR.Pulse.Raw.Format.Serialize.fst`

Section 3.3:
- The validity and equivalence predicates are defined in `src/cbor/spec/raw/CBOR.Spec.Raw.Valid.fst*`
- The deterministic encoding is defined in `src/cbor/spec/raw/CBOR.Spec.Raw.Optimal.fst`
- Theorem 3.1 is `unpack_pack` and `pack_unpack` in `src/cbor/spec/raw/CBOR.Spec.Raw.DataModel.fst`.
- Theorem 3.2 is `cbor_compare_correct` in `src/cbor/spec/raw/everparse/CBOR.Spec.Raw.Format.fst`
- The verified defensive C API specifications are defined at `src/cbor/pulse/CBOR.Pulse.API.Base.fst` and `src/cbor/pulse/CBOR.Pulse.API.Det.C.fsti`, and similarly for Rust.
- The code extracts to C at `src/cbor/pulse/det/c`, and to Rust at `src/cbor/pulse/det/rust`

Section 4.1:
- The CDDL semantics is defined as a set of combinators in `src/cddl/spec/CDDL.Spec.Base.fst`, `CDDL.Spec.Misc.fst`, `CDDL.Spec.ArrayGroup.fst`,  `CDDL.Spec.MapGroup.Base.fst` and `CDDL.Spec.MapGroup.fst`.
- Theorem 4.1 is `map_group_zero_or_more_choice` and ancillary lemmas in `src/cddl/spec/CDDL.Spec.MapGroup.Base.fsti`
- The CDDL AST is defined in `src/cddl/spec/CDDL.Spec.AST.Base.fst`
- Theorem 4.2 is `elab_map_group_sem` in `CDDL.Spec.AST.Base.fst`: it returns a `det_map_group`
- The CDDL elaborator is defined as `mk_wf_typ` in `src/cddl/spec/CDDL.Spec.AST.Elab.fst`
- Theorem 4.3 is the postcondition of `impl_bundle_wf_type` in `src/cddl/pulse/CDDL.Pulse.AST.Bundle.fst`

Section 4.2:
- The CDDL validator implementation combinators are defined in `src/cddl/pulse/CDDL.Pulse.Base.fst`, `CDDL.Pulse.Misc.fst`, `CDDL.Pulse.ArrayGroup.fst` and `CDDL.Pulse.MapGroup.fst`
- The CDDL parser implementation combinators are defined in `src/cddl/pulse/CDDL.Pulse.Parse.*`
- The CDDL sserializer implementation combinators are defined in `src/cddl/pulse/CDDL.Pulse.Serialize.*`
- The CDDL code generator is defined as `impl_bundle_wf_type` in `src/cddl/pulse/CDDL.Pulse.AST.Bundle.fst`

Section 5.2:
- The unverified interoperability tests are in the directory `src/cose/interop`.  The interesting file is `common.c`, which uses the generated C API.
- The verified signature creation and verification code is in `src/cose/verifiedinterop`.  The main file is `CommonPulse.fst`.

Appendix A:
- The arithmetic example is in `tests/pulse`
