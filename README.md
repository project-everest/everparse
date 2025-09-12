# EverParse

EverParse is a framework for generating verified secure parsers from DSL format specification languages.
It consists of several components:

* LowParse, a verified combinator library written in F\*, Low\* and Pulse
* 3D: A frontend for EverParse to enable specifying data formats in an
  style resembling type definitions in the C programming language, but
  with data dependencies. We have used it to generate message
  validation code for use within several low-level C programs.
* QuackyDucky: A frontend for EverParse that accepts data formats in a
  style common to many RFCs. We have used it to generate message
  processing code for several networking protocols, including TLS and
  QUIC.
* EverCBOR, a standalone verified C/Rust implementation of CBOR
* EverCOSign, a standalone verified C/Rust implementation of COSE signing and verification
* EverCDDL, a frontend for EverParse that accepts data formats for
  CBOR objects in CDDL, and generates verified C or Rust data types,
  parsers and serializers.

For more information, you can read:
* The [EverParse project website and user manual](https://project-everest.github.io/everparse), also available in the `doc` subdirectory of this repository as `*.rst` reStructuredText files.
* our [CBOR/CDDL/COSE paper draft](https://doi.org/10.48550/arXiv.2505.17335) (see `README-cbor.md` for matchings between our paper and the code. The paper has just been accepted to ACM CCS 2025.)
  + `README-cbor.md` connects the paper with the F\* proofs
* our [Microsoft Research blog post](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/)
* our [PLDI 2022 paper](https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/)
* our [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

# Binary packages

Ready-to-use standalone native binary packages for Linux, Windows and
MacOS are available as [GitHub
releases](https://github.com/project-everest/everparse/releases)

The contents of the EverParse binary package depends on the
platform.

|                      | Linux | MacOS | Windows |
|----------------------|-------|-------|---------|
| 3D, QuackyDucky      |  Yes  |  Yes  |  Yes    |
| EverCBOR, EverCDDL   |  Yes  |  Yes  |  No     |
| EverCOSign           |  Yes  |  No   |  No     |

NOTE: Versions 2025.06.05 and earlier only contain 3D and QuackyDucky,
and are not available on MacOS.

# Docker images

Pre-built Docker Linux images containing everything are [available on
GitHub
Packages](https://github.com/project-everest/everparse/pkgs/container/everparse). You
can run an interactive shell container based on those images using
`docker run -i -t`

Those images are Linux/amd64 only, so on MacOS, you need to install
Rosetta and use `docker run --platform=linux/amd64`

A `Dockerfile` is available for you to build all of EverParse in a
Docker image with `docker build -t everparse .` and use them in a
Docker container with `docker run -i -t everparse` . On MacOS, you may
need to install Rosetta and use `docker build --platform=linux/amd64`

NOTE: Docker images and `Dockerfile` are not available for versions
2025.06.05 and earlier.

# Usage

## 3D

See the [3D user manual](https://project-everest.github.io/everparse/3d.html).

## EverCDDL

EverParse presents EverCDDL, our formally verified implementation of CDDL.

NOTE: We finally support table extensibility patterns such as `(? 18
=> int, * int => any)`.

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

## QuackyDucky

Run `./bin/qd.exe -help` to get instructions on how to run QuackyDucky.

NOTE: Contrary to 3D or EverCDDL, QuackyDucky only produces F\* files
from data format descriptions. You need to run F\* and Karamel by hand
to verify the produced files and extract C code:

* The binary package contains F\* and Karamel respectively at `bin/fstar.exe` and `bin/krml`

* The Docker image contains F\* and Karamel respectively at `opt/FStar/out/bin/fstar.exe` and `opt/karamel/krml`

TODO: integrate [documentation and example by Samuel Chassot](https://github.com/project-everest/everparse/pull/86)

### Example format description files

[Complete TLS 1.3 message format of miTLS](https://github.com/project-everest/mitls-fstar/blob/dev/src/parsers/Parsers.rfc)

[Bitcoin blocks and transactions](https://github.com/project-everest/everparse/blob/master/tests/bitcoin.rfc)

## EverCBOR

EverParse presents EverCBOR, our formally verified implementation of CBOR.

NOTE: Currently, we only support the deterministic subset of CBOR. Full support of CBOR is coming soon.

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

## EverCOSign

EverParse presents EverCOSign, our formally verified implementation of COSE signing.

NOTE: Support for encryption is in progress.

* The generated C source files for COSE are in `src/cose/c` :
  + `COSE_Format.c` contains the verified parsers and serializers for COSE
  + `COSE_EverCrypt.c` is a verified implementation of sign1 and verify1 with COSE_Format and HACL* EverCrypt
  + `COSE_OpenSSL.c` is a handwritten implementation of sign1 and verify1 with OpenSSL, unverified except for parsing and serializing, calling into COSE_Format
* To use the corresponding include files, you need to add `src/cbor/pulse/det/c` to the include path of your C compiler.
* Interop tests for the C library are in `src/cose/interop` (OpenSSL) and `src/cose/verifiedinterop/test` (HACL* EverCrypt)
* The generated Rust source files for COSE are in `src/cose/rust`, where you can use `cargo build` and `cargo test` ; the crate is called `evercosign`

# Building from source

## Prerequisites

* On Windows, you need WSL2 (Windows Subsystem for Linux, version 2.x)
  with Ubuntu 24.04. Then, you will get Linux executables, not
  Windows. From now on, please follow Ubuntu 24.04 instructions below,
  which also apply to Windows+WSL2.

* On Ubuntu 24.04 (and Windows+WSL2), EverParse depends on:

  + [Rust](https://www.rust-lang.org/tools/install) (for EverCBOR and EverCOSign)
  
  + A few system packages that can be installed with:
  
	`sudo apt-get install --no-install-recommends ca-certificates curl git pkg-config libffi-dev libgmp-dev libsqlite3-dev libssl-dev time opam`

	(`opam` is not needed by EverCBOR and EverCOSign. `libssl-dev` is needed only by EverCOSign.)

	For testing, you can install additional packages with:

	`sudo apt-get install --no-install-recommends cmake python3-pip python3-venv`

* On MacOS, EverParse depends on:

  + [Rust](https://www.rust-lang.org/tools/install) (for EverCBOR and EverCOSign)
  
  + A few Homebrew packages that can be installed with:

	`brew install bash gnu-getopt make gnu-time coreutils opam gmp libffi pkgconf sqlite`
	
	(`opam` is not needed by EverCBOR and EverCOSign.)
	
	In particular, among these packages is GNU Make. Then, in all
	build instructions below, replace `make` with `gmake`

## Build everything

Just run `make` (`gmake` on MacOS)

In addition to EverParse, this command will also automatically build
all dependencies including opam packages, F\*, Karamel and Pulse.

This will take around 1 hour with `-j8`. However, you do not need to
build everything at once: EverParse is composed of several components
that you can build individually as you need.

## EverCBOR

EverCBOR does not need opam.

* To build the C and Rust CBOR library: run `make -f nofstar.Makefile cbor`

* To test the C and Rust CBOR library: run `make -f nofstar.Makefile cbor-test-unverified`

## EverCOSign

EverCOSign does not need opam, but needs OpenSSL headers.

* to build the C and Rust COSE library: run `make -f nofstar.Makefile cose`

* to test the C and Rust COSE library: run `make -f nofstar.Makefile cose-extracted-test`

## EverCDDL

Run `make cddl`

## 3D

Run `make 3d`

## QuackyDucky

Run `make quackyducky`

# Advanced

## Writing F\* proofs

If you want to write F\* proofs against the EverParse libraries and/or
the F\* files generated by EverParse, or to contribute to EverParse,
you can do it either from the source repository, or from within a
Docker image. The following instructions allow you to properly setup
[Visual Studio Code](https://code.visualstudio.com/) with the
[F\* VSCode Assistant extension](https://github.com/FStarLang/fstar-vscode-assistant).

In all cases, you can copy the contents of `src/package/EverParse.fst.config.json`
into your configuration file at the root of your workspace directory, to give
the extension access to the EverParse proofs. This file refers to an
environment variable, `EVERPARSE_HOME`, which contains the full path to
the EverParse clone (`/mnt/everparse` in the Docker image), as set up by
the instructions below.

### From the source repository

You can run a custom Bash shell with `./shell.sh`

This script will locally install EverParse dependencies and open a new
Bash shell with appropriately populated environment variables for
opam, OCaml, F\*, etc.

Alternatively, if you are already in a Bash shell session, you can also
directly populate its environment with `make deps && eval "$(make -s env)"`

Then, from this shell, you can call Visual Studio Code and install the
F\* VSCode Assistant extension to edit the F\* files present in the
EverParse repository with full F\* editing features.

NOTE: On Windows+WSL2, you also need to install the [WSL extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl), needed to make the Linux paths in the environment variables work.

### From a Docker image

When you start a container from a Docker image for EverParse, its
shell is already configured with the proper environment.

Then, you can run [Code Server](https://coder.com/docs/code-server) from a container, which
allows you to run a web version of Visual Studio Code on your host
accessing the F\* files in the container:

1. Start a container with `docker run -i -t -p 8080:8080`

   You can add more options to set up a [bind mount](https://docs.docker.com/engine/storage/bind-mounts/) to access folders on your host machine.

2. From within the container, run `./start-code-server.sh`

3. On your host machine, open a Web browser and go to `http://localhost:8080`

   This opens a web-based session of Visual Studio Code, accessing the
   files in the container. The F\* VSCode Assistant extension is
   already installed for you.

## Using an existing opam root, F\*, etc.

If you want to use existing dependencies instead of letting EverParse
locally install them, you can populate the following environment
variables:

* `EVERPARSE_USE_OPAMROOT=1` instructs EverParse to use the current
  opam installation (the value of `OPAMROOT` if set, otherwise
  `$HOME/.opam`) instead of creating a local install

* If you want to use your own F\*, set `FSTAR_EXE` to the full path of
  your `fstar.exe` executable.
  
  NOTE: If you want to use EverCDDL, you cannot use a F\* binary
  package because EverCDDL has a F\* plugin that needs to be compiled
  with the very same OCaml environment as the one used to compile
  F\*. This is why setting `FSTAR_EXE` will automatically set
  `EVERPARSE_USE_OPAMROOT=1`.
  
* If you want to use your own Karamel, set `KRML_HOME` to the full
  path of your clone of the Karamel repository. This requires
  `FSTAR_EXE` to be set.

* If you want to use your own Pulse, set `PULSE_HOME` to the full path
  of the directory where Pulse was compiled (in most cases, the `out/`
  subdirectory of the Pulse clone.) This requires `FSTAR_EXE` to be
  set.
