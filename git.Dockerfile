# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-24.04-ocaml-$ocaml_version

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends llvm-dev libclang-dev clang libgmp-dev pkg-config
RUN . "$HOME/.cargo/env" && rustup component add rustfmt && cargo install bindgen-cli

# Install other dependencies
RUN sudo apt-get install --yes \
  libssl-dev \
  cmake \
  python-is-python3 \
  python3-pip \
  python3-venv \
  time \
  wget

# Bring in the contents
ARG CACHE_BUST
RUN sudo mkdir /mnt/everparse && sudo chown opam:opam /mnt/everparse
RUN git clone https://github.com/project-everest/everparse /mnt/everparse && echo $CACHE_BUST
WORKDIR /mnt/everparse

# Build and publish the release
ARG CI_THREADS=24
RUN sudo apt-get update && . "$HOME/.cargo/env" && env OPAMYES=1 make _opam && eval $(opam env) && make -j $CI_THREADS -C opt && env OTHERFLAGS='--admit_smt_queries true' make -j $CI_THREADS all cbor-test cddl-test cose-test

ENTRYPOINT ["/mnt/everparse/opt/shell.sh", "--login", "-c"]
CMD ["/bin/bash"]
