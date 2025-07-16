This EverParse branch contains a verified implementation of CBOR and COSE signing, as well as a verified parser and serializer generator from CDDL descriptions.

A Dockerfile is included to rebuild everything, including Everest dependencies, F*, etc. To build it, just run `docker build -t evercbor .`

Then, you can experiment with `docker run -i -t evercbor` ; there, you can use the following Makefile rules:
* `make cbor-test` tests the CBOR library
* `make cbor-verify` entirely reverifies the CBOR library. (This may take 1 hour.)
* `make cose-test` tests the COSE library
* `make cddl-test` tests the CDDL library
* `make cbor-snapshot` regenerates the CBOR library. This rule is incompatible with `cbor-test`
* `make cose-snapshot` rebuilds the COSE library. This rule is incompatible with `cddl-test`

If you are interested in the proofs, you can read [our
paper](https://doi.org/10.48550/arXiv.2505.17335). Below is the
matching between the paper and the proofs.

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

Section 5.1:
- Record benchmark: CDDL description in `BenchFlat.cddl`, driver code in `Test_BenchFlat.cpp`.
- Map benchmark: CDDL description in `BenchMap.cddl`, driver code in `Test_BenchMap.cpp`.
- Array benchmark: CDDL description in `src/cddl/unit-tests/BenchArray.cddl`. The driver `Test_BenchArray.c` serializes and parses with our tool. `Test_BenchArray__Interop1.c` serializes with our tool and parses with QCBOR. `Test_BenchArray__Interop2.c` serialized with QCBOR and parses with our tool. Finall, `Test_BenchArray__Interop3.cpp` tests against TinyCBOR.

Section 5.2:
- The COSE specification is at `src/cose/cose.cddl`
- The verified C code obtained after extracting COSE is at `src/cose/c/`
- The unverified interoperability tests with OpenSSL are in the directory `src/cose/interop`.  The interesting file is `common.c`, which uses the generated C API.
- The verified signature creation and verification code using HACL* EverCrypt is in `src/cose/verifiedinterop`.  The main file is `CBOR.EverCrypt.fst`.
- The verified Rust code obtained after extracting COSE is at `src/cose/rust/`. It can be built (resp. tested) by running `cargo build` (resp. `cargo test`) from that directory.

Appendix A:
- The arithmetic example is in `tests/pulse`

Appendix C:
- The DPE CDDL specifications are in `src/cddl/test/dpe.cddl`
- The verified Pulse code formatting objects to and from byte arrays is in `src/cddl/test/dpe/`
- The in-memory profile DPE API is in `src/cddl/test/DPESlice.fsti`, adapt from Ebner et al. 2025 to be standalone
- The main API implementing the CBOR profile is in `src/cddl/test/dpe/DPEMain.fst`