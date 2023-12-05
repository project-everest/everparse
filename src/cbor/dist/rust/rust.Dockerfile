# This Dockerfile MUST be run from the parent directory

FROM rust:latest

WORKDIR /usr/src/cbor-extern
RUN apt-get update
RUN apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang
RUN rustup component add rustfmt
RUN cargo install bindgen-cli
ADD out/CBOR.h CBOR.h
ADD rust/bindings.h bindings.h
ADD rust/krmllib.h krmllib.h
RUN bindgen -o CBOR_Extern.rs --allowlist-file ./CBOR.h bindings.h
