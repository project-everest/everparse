This is the artifact for ACM CCS 2025 B accepted paper #1288: "Secure
Parsing and Serializing with Separation Logic Applied to CBOR, CDDL
and COSE," by Tahina Ramananandro, Gabriel Ebner, Guido Martínez and
Nikhil Swamy.

This artifact showcases:

* PulseParse, our new separation logic framework for verified parsing
  and serialization

* EverCBOR, our new formally verified CBOR library

* EverCDDL our new formally verified CDDL parser and serializer
  generator
  
* EverCOSE, our new formally verified implementation of (so far the
  signing and verification part of) COSE.

# Contents of this artifact

This artifact contains 2 files:

* `README-ccs2025.md`: this file, containing usage instructions

* `evercbor-ccs2025.tar.gz`: **do not manually extract the contents of
  this file!** It actually contains 3 Docker images in standard OCI
  (Open Container Initiative) format:

  + `evercbor-ccs2025-test`, an image with everything (including
    tests) built
	
  + `evercbor-ccs2025-build`, an image with EverCBOR, EverCDDL and
    EverCOSE verified, extracted and built, but tests not built
	
  + `evercbor-ccs2025-deps`, an image with only dependencies built,
    and EverCBOR, EverCDDL and EverCOSE not verified, extracted, built
    or tested

# Prerequisites

The Docker images of this artifact only work for the Linux/amd64
platform. Thus:

* On Linux, you need `docker` and `gunzip`

* On MacOS, you need Rosetta, `docker` and `gunzip`.
  
* On Windows, you need WSL2 (Windows Subsystem for Linux, version
  2.x), with a Linux containing `docker` and `gunzip`. From now on in
  this file, we treat WSL2 in the same way as Linux.

We have tested our artifact with Docker 28.0.2, with 8 parallel
threads and 16 GB RAM (by running `make -j 8` inside
`docker run --memory=16G`)

# Loading the images and opening a container

Before being able to open containers based on the images of this
artifact, you first need to load the images into your system. The
following instructions will load the 3 images all at once:

1. Download `evercbor-ccs2025.tar.gz` from the Zenodo record.

2. Run `gunzip -c evercbor-ccs2025.tar.gz | docker load`

3. Run `docker image list --no-trunc 'evercbor-ccs2025-*'`
   (do not forget the single quotes)

4. Check the output of this command against the sha256 image IDs
   listed in the description of the Zenodo record.

Then, to open a container based on (say) the `evercbor-ccs2025-deps`
image:

* on Linux, run `docker run -i -t evercbor-ccs2025-deps`

* on MacOS, run
  `docker run --platform=linux/amd64 -i -t evercbor-ccs2025-deps`

# Testing

There are several ways to test our artifact, which can be performed
independently of each other and in any order.

## Try out EverCBOR by yourself

NOTE: As mentioned in the paper, EverCBOR only supports the
deterministic encoding subset of CBOR without floating-points:
integers encoded in least size, and map entries sorted by the
lexicographic ordering of their byte serialization.

1. Open a container based on the `evercbor-ccs2025-build` or
   `evercbor-ccs2025-test` image.
   
2. Run `cd /mnt/everparse/src/cbor/pulse/det/c/example`

   This directory contains a demonstration C program, `main.c`, with
   comments explaining the EverCBOR API. You can adapt it as you wish.
   
3. To compile and run this program, run `make`. This will produce an
   executable, `CBORDetTest.exe`, and run it.

Alternatively, you can also test the Rust implementation, located in
`/mnt/everparse/src/cbor/pulse/det/rust`, where `tests/example.rs`
contains a fully documented Rust demonstration program, which you can
adapt as you wish. You can then run `cargo test` to compile and test
this program. You can also run `cargo doc` to produce the
documentation of EverCBOR's Rust API.

## Try out EverCDDL by yourself

1. Open a container based on the `evercbor-ccs2025-build` or
   `evercbor-ccs2025-test` image.
   
2. Run `cd /mnt/everparse/src/cddl/tests/demo`

   This directory contains a demonstration CDDL specification,
   `test.cddl`, which you can modify as you wish. In particular, you
   can copy parts of the standard postlude from
   `/mnt/everparse/src/cddl/spec/postlude.cddl`
   
3. Run `cddl.exe test.cddl` to automatically generate a C file
   containing validators, parsers and serializers formally verified
   with respect to the CDDL specification in `test.cddl` . EverCDDL
   will automatically compile the generated C file into a `.o` object
   file.

   You can run `cddl.exe --help` for more options (such as
   producing Rust code instead of C, retaining the generated F* code
   for use with a verified client, etc.)

NOTE: The CDDL elaboration in Section 4.1 of the paper mentions a
limitation mandating cuts on
`?(18 : tstr), *(uint => any)` . We lifted this limitation
in the artifact: we have extended the implementation of EverCDDL to
annotate tables with key-value footprints (instead of just keys),
represented as Boolean formulae where atoms are pairs of key-value
types. This allows us to support extensibility patterns such as
`?(18 => tstr), *(uint => any)`, where the table
`*(uint => any)` can accept an entry with
key 18, provided its value is not an unsigned integer.
We will mention that improvement in the final version of our paper.

## Verify and build EverCBOR, EverCDDL and EverCOSE

From a container based on the `evercbor-ccs2025-deps` image:

* to verify PulseParse from Section 2, run `make pulseparse`
* to verify, extract and build EverCBOR from Section 3, run `make cbor`
* to verify EverCDDL from Section 4, run `make cddl`
* to verify, extract and build EverCOSE from Section 5.2, run `make cose`
* to verify extract and build all of the above, run `make`

At this point, you have reached the state of the `evercbor-ccs2025-build` image.

## Verify, build and run the benchmarks

From a container based on the `evercbor-ccs2025-build` image:

* to run CBOR benchmark tests from Section 5.1 (which use CDDL), run `make cddl-unit-tests`
* to test EverCOSE from Section 5.2, run `make cose-test`
* to verify the arithmetic example from Appendix A, run `make pulseparse-test`
* to verify and extract the DPE example from Appendix C, run `make cddl-dpe`
* there are other CBOR and CDDL tests not described in the paper, which you can run with `make cbor-test` and `make cddl-other-tests` respectively.
* to test all of the above, run `make test`

At this point, you have reached the state of the `evercbor-ccs2025-test` image.

# Browsing the contents to match the artifact with the paper

If you want to read our verified implementation, you can actually use
a Web version of Visual Studio Code, which can be set up automatically
using the following instructions:

1. On Linux, run `docker run -p 8080:8080 -i -t evercbor-ccs2025-test`

   On MacOS, run `docker run --platform=linux/amd64 -p 8080:8080 -i -t evercbor-ccs2025-test`

2. In the container, run `./start-code-server.sh`

3. On your host computer, open a Web browser and go to `http://localhost:8080`

This will open a Web-based instance of Visual Studio Code, where you
can browse the contents of the artifact in the container. For
instance, if you open a F* file (file name extension `.fst` or
`.fsti`), move to some location within this file, and then hit the
keystroke `CTRL+.` , then Visual Studio Code will have
F* verify the contents of the file down to that point. A green bar on
the left-hand-side will show which parts of the code F* has
verified. For more information, the container includes the manual of the
Visual Studio Code extension for F* in `fstar-vscode-assistant.md`

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
- The CDDL serializer implementation combinators are defined in `CDDL.Pulse.Serialize.*`
- The CDDL code generator is defined as `impl_bundle_wf_type` in `CDDL.Pulse.AST.Bundle.fst`

Section 5.1: in directory `/src/cddl/tests/unit`
- Record benchmark: CDDL description in `BenchFlat.cddl`, driver code in `Test_BenchFlat.cpp`.
- Map benchmark: CDDL description in `BenchMap.cddl`, driver code in `Test_BenchMap.cpp`.
- Array benchmark: CDDL description in `BenchArray.cddl`. The driver `Test_BenchArray.c` serializes and parses with our tool. `Test_BenchArray__Interop1.c` serializes with our tool and parses with QCBOR. `Test_BenchArray__Interop2.c` serialized with QCBOR and parses with our tool. Finally, `Test_BenchArray__Interop3.cpp` tests against TinyCBOR.

Section 5.2: in directory `/src/cose`
- The COSE specification is at `cose-sign.cddl` and `cose-encrypt.cddl`
- The verified C code obtained after extracting COSE signing and verification is in the `c` subdirectory
- The verified C code obtained after extracting COSE encryption and MAC formats is in the `encrypt` subdirectory
- The unverified signing and verification interoperability tests with OpenSSL are in subdirectory `interop`.  The interesting file is `common.c`, which uses the generated C API.
- The verified signature creation and verification code using HACL* EverCrypt is in subdirectory `verifiedinterop`.  The main file is `COSE.EverCrypt.fst`. It extracts to `/src/cose/c/COSE_EverCrypt.c`
- The verified Rust code obtained after extracting COSE signing and verification is in the `rust` subdirectory. It can be built (resp. tested) by running `cargo build` (resp. `cargo test`) from that directory.

Appendix A:
- The arithmetic example is in `/tests/pulse`

Appendix C: in directory `/src/cddl/tests/dpe`
- The DPE CDDL specifications are in `dpe.cddl`
- The verified Pulse code formatting objects to and from byte arrays is in the `dpe` subdirectory
- The in-memory profile DPE API is in `dpe/DPESlice.fsti`, adapted from Ebner et al. PLDI 2025 to be standalone
- The main API implementing the CBOR profile is in `dpe/DPEMain.fst`
