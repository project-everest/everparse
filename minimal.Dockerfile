# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

# install rust
RUN sudo mkdir /mnt/rustup && sudo chown opam:opam /mnt/rustup
RUN sudo mkdir /mnt/cargo && sudo chown opam:opam /mnt/cargo
ENV RUSTUP_HOME=/mnt/rustup
ENV CARGO_HOME=/mnt/cargo
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH=$CARGO_HOME/bin:$PATH

# Bring in the contents
ADD --chown=opam:opam ./ /mnt/everparse/
WORKDIR /mnt/everparse

# Build EverCDDL
RUN sudo apt-get update && ./build-evercddl.sh

ENTRYPOINT ["/mnt/everparse/opt/shell.sh", "-c"]
CMD ["/bin/bash"]
