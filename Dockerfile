# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-24.04-ocaml-$ocaml_version AS base

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang libgmp-dev pkg-config \
  libssl-dev \
  cmake \
  python-is-python3 \
  python3-pip \
  python3-venv \
  time \
  wget

# Automatically set up Rust environment
SHELL ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/bin/bash", "-c"]

# Bring in the contents
ADD --chown=opam:opam ./ /mnt/everparse/
WORKDIR /mnt/everparse
RUN git clean -ffdx || true
RUN { git submodule init && git submodule update && git submodule foreach --recursive git clean -ffdx ; } || true

FROM base AS deps

ARG CI_THREADS
RUN sudo apt-get update && env OPAMNODEPEXTS=0 make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" deps

# Automatically set up Rust environment
ENTRYPOINT ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/mnt/everparse/opt/shell.sh", "-c"]
CMD ["/bin/bash", "-i"]
SHELL ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/mnt/everparse/opt/shell.sh", "-c"]

FROM deps AS build

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" all

FROM build AS test

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" test
