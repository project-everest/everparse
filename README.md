# EverParse

EverParse is a framework for generating verified secure parsers from DSL format specification languages.
It consists of LowParse, a verified combinator library (in `src/lowparse`), and QuackyDucky, an untrusted message format specification language compiler.

For more information, you can read:
* The [EverParse project website and user manual](https://project-everest.github.io/everparse), also available in the `doc` subdirectory of this repository as `*.rst` reStructuredText files.
* our [Microsoft Research blog post](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/)
* our [PLDI 2022 paper](https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/)
* our [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

## CBOR and COSE

The following instructions work without F*. For more details on the proofs, see `README-ccs2025.md`

### CBOR

To build the C and Rust CBOR library, run `make cbor`

To test the C and Rust CBOR library, run `make cbor-test-unverified`

* The generated C source files for CBOR are in `src/cbor/pulse/det/c`, which also contains some tests in the `test` subdirectory
* The generated Rust source files for CBOR are in `src/cbor/pulse/det/rust` , where you can use `cargo build` and `cargo test` ; the crate is called `cborrs`

### COSE

To build the C and Rust COSE library, run `make cose`

To test the C and Rust COSE library, run `make cose-extracted-test`

* The generated C source files for COSE are in `src/cose/c`
* Interop tests for the C library are in `src/cose/interop`
* The generated Rust source files for COSE are in `src/cose/rust`, where you can use `cargo build` and `cargo test` ; the crate is called `evercosign`

### CDDL

The CDDL verified parser generator requires F*. Usage instructions coming soon.

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
