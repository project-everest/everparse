# EverParse

EverParse is a framework for generating verified secure parsers from DSL format specification languages.
It consists of LowParse, a verified combinator library (in `src/lowparse`), and QuackyDucky, an untrusted message format specification language compiler.

For more information, you can read:
* The [EverParse project website and user manual](https://project-everest.github.io/everparse), also available in the `doc` subdirectory of this repository as `*.rst` reStructuredText files.
* our [CBOR/CDDL/COSE paper draft](https://doi.org/10.48550/arXiv.2505.17335) (see `README-cbor.md` for matchings between our paper and the code. The paper has just been accepted to ACM CCS 2025.)
* our [Microsoft Research blog post](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/)
* our [PLDI 2022 paper](https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/)
* our [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

## CBOR, CDDL and COSE

This section is focused on build and usage instructions. For more details on the proofs, see `README-cbor.md`

### Docker image

A `Dockerfile` is available for you to build CBOR, CDDL and COSE in a Docker image
with `docker build -t evercddl .` and use them in a Docker container
with `docker run -i -t evercddl`

A pre-built Docker image is [available on GitHub Packages](https://github.com/project-everest/everparse/pkgs/container/evercbor)

The *Use* sections of the instructions below apply to the pre-built
Docker image as well as when building by hand.

### CBOR

EverParse presents EverCBOR, our formally verified implementation of CBOR.

NOTE: Currently, we only support the deterministic subset of CBOR. Full support of CBOR is coming soon.

The following instructions work without F*.

#### Build and test

EverCBOR is already built in the Docker image. If you are not using that image, you can:

* build the C and Rust CBOR library: run `make cbor`

* test the C and Rust CBOR library: run `make cbor-test-unverified`

#### Use

* C:

  + The generated C source files for CBOR are in
    `src/cbor/pulse/det/c`, which also contains some tests in the
    `test` subdirectory. There, the header file is `CBORDet.h`. The
    object file is `CBORDet.o`, which you can link with your
    application.
  
  + A fully documented example is in
    `src/cbor/pulse/det/c/example`. There, `main.c` documents the C
    API; its `Makefile` shows how to compile and link against CBORDet.
  
* Rust:

  + The generated Rust source files for CBOR are in
    `src/cbor/pulse/det/rust` , where you can use `cargo build` and
    `cargo test` ; the crate is called `cborrs`.

  + The generated HTML documentation of `cborrs` is at
    `https://project-everest.github.io/everparse/evercbor-rust/cborrs/`

### COSE

EverParse presents EverCOSign, our formally verified implementation of COSE signing.

NOTE: Support for encryption is in progress.

The following instructions work without F*.

#### Build and test

EverCOSign is already built in the Docker image. If you are not using that image, you can:

* build the C and Rust COSE library: run `make cose`

* test the C and Rust COSE library: run `make cose-extracted-test`

#### Use

* The generated C source files for COSE are in `src/cose/c` :
  + `COSE_Format.c` contains the verified parsers and serializers for COSE
  + `COSE_EverCrypt.c` is a verified implementation of sign1 and verify1 with COSE_Format and HACL* EverCrypt
  + `COSE_OpenSSL.c` is a handwritten implementation of sign1 and verify1 with OpenSSL, unverified except for parsing and serializing, calling into COSE_Format
* To use the corresponding include files, you need to add `src/cbor/pulse/det/c` to the include path of your C compiler.
* Interop tests for the C library are in `src/cose/interop` (OpenSSL) and `src/cose/verifiedinterop/test` (HACL* EverCrypt)
* The generated Rust source files for COSE are in `src/cose/rust`, where you can use `cargo build` and `cargo test` ; the crate is called `evercosign`

### CDDL

EverParse presents EverCDDL, our formally verified implementation of CDDL.

NOTE: We finally support table extensibility patterns such as `(? 18
=> int, * int => any)`.

#### Build

EverCDDL is already built in the Docker image. If you are not using that image, you can build EverCDDL as follows:

1. Install opam 2.x, which you can install following the [official instructions](https://opam.ocaml.org/doc/Install.html). You do not need to install OCaml, though.

2. Run `make cddl` . This will build EverCDDL using a local
   opam switch, so this will not impact your existing opam switches if
   any.

#### Use

The EverCDDL code generator is compiled as an executable,
`bin/cddl.exe`

If you have a CDDL data format description, say `mydesc.cddl`, you can
automatically compile it into C parsers and serializers, with
`bin/cddl.exe src/cddl/spec/postlude.cddl mydesc.cddl` (where
`src/cddl/spec/postlude.cddl` is a subset of the official postlude
from RFC 8610). The generated C code links against EverCBOR.

If you want to generate Rust code instead, use the `--rust`
option. Right now, contrary to C, the generated Rust code is
standalone and does not need a separate installation of EverCBOR.

More options are available, use `--help` for more details.

## Download

We publish binary packages for EverParse as GitHub releases: https://github.com/project-everest/everparse/releases

NOTE: These binary packages do not contain CBOR, CDDL or COSE.

## Build from source

Full build instructions, including how to install dependencies, are available at https://project-everest.github.io/everparse/build.html, or equivalently in `doc/build.rst` in this repository.

## Using QuackyDucky

### Example format description files

[Complete TLS 1.3 message format of miTLS](https://github.com/project-everest/mitls-fstar/blob/dev/src/parsers/Parsers.rfc)

[Bitcoin blocks and transactions](https://github.com/project-everest/everparse/blob/master/tests/bitcoin.rfc)

### Building
`make`

### Running
`./bin/qd.exe -help`
