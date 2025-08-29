# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-24.04-ocaml-$ocaml_version AS base

SHELL ["/bin/bash", "--login", "-c"]

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

# Set up Rust environment
RUN echo "source $HOME/.cargo/env" >> $(if test -f $HOME/.bash_profile ; then echo $HOME/.bash_profile ; else echo $HOME/.profile ; fi)

# Set up code-server
RUN wget https://github.com/coder/code-server/releases/download/v4.103.2/code-server_4.103.2_amd64.deb \
 && sudo dpkg -i code-server*.deb \
 && rm code-server*.deb
RUN wget https://github.com/FStarLang/fstar-vscode-assistant/releases/download/v0.19.2/fstar-vscode-assistant-0.19.2.vsix \
 && code-server --install-extension fstar-vscode-assistant-*.vsix \
 && rm fstar-vscode-assistant-*.vsix

# Bring in the contents
ARG CACHE_BUST
RUN sudo mkdir /mnt/everparse && sudo chown opam:opam /mnt/everparse
ARG CI_BRANCH=_taramana_ccs2025
RUN git clone --recurse-submodules --branch $CI_BRANCH https://github.com/project-everest/everparse /mnt/everparse && echo $CACHE_BUST
WORKDIR /mnt/everparse

FROM base AS deps

ARG CI_THREADS
RUN sudo apt-get update && env OPAMYES=1 make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" -C opt && make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" lowparse

ENTRYPOINT ["/mnt/everparse/opt/shell.sh", "--login", "-c"]
CMD ["/bin/bash"]
SHELL ["/mnt/everparse/opt/shell.sh", "--login", "-c"]

FROM deps AS build

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" all

FROM build AS test

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" test
