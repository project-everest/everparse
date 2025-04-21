# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang libgmp-dev pkg-config
RUN . "$HOME/.cargo/env" && rustup component add rustfmt && cargo install bindgen-cli

# Install other dependencies
RUN sudo apt-get install --yes \
  python-is-python3 \
  wget

# Bring in the contents
ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# Build and publish the release
ARG CI_THREADS=24
RUN  . "$HOME/.cargo/env" && eval $(opam env) && bash src/package/install-deps.sh && make -j $CI_THREADS -C opt && env OTHERFLAGS='--admit_smt_queries true' make -j $CI_THREADS cbor cddl
