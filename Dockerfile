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

# Set up code-server
RUN wget https://github.com/coder/code-server/releases/download/v4.103.2/code-server_4.103.2_amd64.deb \
 && sudo dpkg -i code-server*.deb \
 && rm code-server*.deb
RUN wget https://github.com/FStarLang/fstar-vscode-assistant/releases/download/v0.19.2/fstar-vscode-assistant-0.19.2.vsix \
 && code-server --install-extension fstar-vscode-assistant-*.vsix \
 && rm fstar-vscode-assistant-*.vsix

# Bring in the contents
ADD --chown=opam:opam ./ /mnt/everparse/
WORKDIR /mnt/everparse
RUN git clean -ffdx || true

FROM base AS deps

ARG CI_THREADS
RUN sudo apt-get update && env OPAMYES=1 make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" -C opt && make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" lowparse

# Automatically set up Rust environment
ENTRYPOINT ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/mnt/everparse/opt/shell.sh", "-c"]
CMD ["/bin/bash", "-i"]
SHELL ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/mnt/everparse/opt/shell.sh", "-c"]

FROM deps AS build

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" all

FROM build AS test

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" test
