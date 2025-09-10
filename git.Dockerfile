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
ARG CACHE_BUST
RUN sudo mkdir /mnt/everparse && sudo chown opam:opam /mnt/everparse
ARG CI_REPO=project-everest/everparse
ARG CI_BRANCH=master
RUN git clone --recurse-submodules --branch $CI_BRANCH https://github.com/$CI_REPO /mnt/everparse && echo $CACHE_BUST
WORKDIR /mnt/everparse

# For the release process: check if the current hash matches the hash being released
ARG CI_HASH
RUN if [[ -n "$CI_HASH" ]] ; then [[ "$CI_HASH" = "$(git rev-parse HEAD)" ]] ; fi

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
