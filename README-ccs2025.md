This is the artifact for ACM CCS 2025 B accepted paper #1288: "Secure Parsing and Serializing with Separation Logic Applied to CBOR, CDDL and COSE."

Since this artifact is single-blind, we are using public names for our work: SEPARSE becomes PulseParse; VERCOR becomes EverCBOR; VERCDL becomes EverCDDL.

Three Docker images are included in this artifact:

* `evercbor-ccs2025-test`, an image with everything (including tests) built
* `evercbor-ccs2025-build`, an image with EverCBOR, EverCDDL and EverCOSE verified, extracted and built, but tests not built
* `evercbor-ccs2025-deps`, an image with only dependencies built, and EverCBOR, EverCDDL and EverCOSE not verified, extracted, built or tested

To load an image (say `evercbor-ccs2025-test`) and open a container into it:
1. Download `evercbor-ccs2025.tar.gz` from the Zenodo record. This archive contains all three images.
2. Run `zcat evercbor-ccs2025.tar.gz | docker load`
3. Run `docker run -i -t evercbor-ccs2025-test`

From the `evercbor-ccs2025-deps` image:
* to verify PulseParse from Section 2, run `make pulseparse`
* to verify, extract and build EverCBOR from Section 3, run `make cbor`
* to verify EverCDDL from Section 4, run `make cddl`
* to verify, extract and build EverCOSE from Section 5.2, run `make cose`
* to verify extract and build all of the above, run `make`

At this point, you have reached the state of the `evercbor-ccs2025-build` image.

From the `evercbor-ccs2025-build` image:
* to run CBOR benchmark tests from Section 5.1 (which use CDDL), run `make cddl-unit-tests`
* to test EverCOSE from Section 5.2, run `make cose-test`
* to verify the arithmetic example from Appendix A, run `make pulseparse-test`
* to verify and extract the DPE example from Appendix C, run `make cddl-dpe`
* there are other CBOR and CDDL tests not described in the paper, which you can run with `make cbor-test` and `make cddl-other-tests` respectively.
* to test all of the above, run `make test`

At this point, you have reached the state of the `evercbor-ccs2025-test` image.

More details about the source code follow.

Section 2.2:
- the PulseParse implementation combinators are in `/src/lowparse/pulse`
- the recursive combinator specification is in `/src/lowparse/pulse/LowParse.Spec.Recursive.fst*`
- the validator and jumper for the recursive format is in `/src/lowparse/pulse/LowParse.Pulse.Recursive.fst`

Section 3.2: in directory `/src/cbor`
- the CBOR raw data type is defined in `spec/raw/CBOR.Spec.Raw.Base.fst`
- the CBOR raw data parser and serializer specifications are defined in `spec/raw/everparse/CBOR.Spec.Raw.EverParse.fst`
- the CBOR raw data validator, jumper implementation, accessors, and the CBOR header value reader and writer, as well as the validator and jumper for the deterministic format, are defined in `pulse/raw/everparse/CBOR.Pulse.Raw.EverParse.Format.fst`
- the low-level datatype for CBOR raw data is defined in `pulse/raw/CBOR.Pulse.Raw.Type.fst`
- the separation logic relation for CBOR raw data is defined in `pulse/raw/CBOR.Pulse.Raw.Match.fst`
- the CBOR raw data serializer implementations are defined in `pulse/raw/everparse/CBOR.Pulse.Raw.Format.Serialize.fst`

Section 3.3: in directory `/src/cbor`
- The validity and equivalence predicates are defined in `spec/raw/CBOR.Spec.Raw.Valid.fst*`
- The deterministic encoding is defined in `spec/raw/CBOR.Spec.Raw.Optimal.fst`
- Theorem 3.1 is `unpack_pack` and `pack_unpack` in `spec/raw/CBOR.Spec.Raw.DataModel.fst`.
- Theorem 3.2 is `cbor_compare_correct` in `spec/raw/everparse/CBOR.Spec.Raw.Format.fst`
- The verified defensive C API specifications are defined at `pulse/CBOR.Pulse.API.Base.fst` and `pulse/CBOR.Pulse.API.Det.C.fsti`, and similarly for Rust.
- The code extracts to C at `pulse/det/c`, and to Rust at `pulse/det/rust`

Section 4.1: in directory `/src/cddl/spec` (except otherwise mentioned)
- The CDDL semantics is defined as a set of combinators in `CDDL.Spec.Base.fst`, `CDDL.Spec.Misc.fst`, `CDDL.Spec.ArrayGroup.fst`,  `CDDL.Spec.MapGroup.Base.fst` and `CDDL.Spec.MapGroup.fst`.
- Theorem 4.1 is `map_group_zero_or_more_choice` and ancillary lemmas in `CDDL.Spec.MapGroup.Base.fsti`
- The CDDL AST is defined in `CDDL.Spec.AST.Base.fst`
- Theorem 4.2 is `elab_map_group_sem` in `CDDL.Spec.AST.Base.fst`: it returns a `det_map_group`
- The CDDL elaborator is defined as `mk_wf_typ` in `CDDL.Spec.AST.Elab.fst`
- Theorem 4.3 is the postcondition of `impl_bundle_wf_type` in `/src/cddl/pulse/CDDL.Pulse.AST.Bundle.fst`

Section 4.2: in directory `/src/cddl/pulse`
- The CDDL validator implementation combinators are defined in `CDDL.Pulse.Base.fst`, `CDDL.Pulse.Misc.fst`, `CDDL.Pulse.ArrayGroup.fst` and `CDDL.Pulse.MapGroup.fst`
- The CDDL parser implementation combinators are defined in `CDDL.Pulse.Parse.*`
- The CDDL sserializer implementation combinators are defined in `CDDL.Pulse.Serialize.*`
- The CDDL code generator is defined as `impl_bundle_wf_type` in `CDDL.Pulse.AST.Bundle.fst`

Section 5.1: in directory `/src/cddl/tests/unit`
- Record benchmark: CDDL description in `BenchFlat.cddl`, driver code in `Test_BenchFlat.cpp`.
- Map benchmark: CDDL description in `BenchMap.cddl`, driver code in `Test_BenchMap.cpp`.
- Array benchmark: CDDL description in `BenchArray.cddl`. The driver `Test_BenchArray.c` serializes and parses with our tool. `Test_BenchArray__Interop1.c` serializes with our tool and parses with QCBOR. `Test_BenchArray__Interop2.c` serialized with QCBOR and parses with our tool. Finall, `Test_BenchArray__Interop3.cpp` tests against TinyCBOR.

Section 5.2: in directory `/src/cose`
- The COSE specification is at `cose.cddl`
- The verified C code obtained after extracting COSE is in the `c` subdirectory
- The unverified interoperability tests with OpenSSL are in subdirectory `interop`.  The interesting file is `common.c`, which uses the generated C API.
- The verified signature creation and verification code using HACL* EverCrypt is in subdirectory `verifiedinterop`.  The main file is `COSE.EverCrypt.fst`. It extracts to `/src/cose/c/COSE_EverCrypt.c`
- The verified Rust code obtained after extracting COSE is in the `rust` subdirectory. It can be built (resp. tested) by running `cargo build` (resp. `cargo test`) from that directory.

Appendix A:
- The arithmetic example is in `/tests/pulse`

Appendix C: in directory `/src/cddl/tests/dpe`
- The DPE CDDL specifications are in `dpe.cddl`
- The verified Pulse code formatting objects to and from byte arrays is in the `dpe` subdirectory
- The in-memory profile DPE API is in `dpe/DPESlice.fsti`, adapted from Ebner et al. PLDI 2025 to be standalone
- The main API implementing the CBOR profile is in `dpe/DPEMain.fst`
