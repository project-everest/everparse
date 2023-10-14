# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends \
    jq \
    wget \
    python-is-python3 \
    && true

# Dependencies (F*, Karamel and opam packages)
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
ENV STEEL_HOME=$HOME/steel
RUN eval $(opam env) && .docker/build/install-deps.sh

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master

RUN eval $(opam env) && OTHERFLAGS="--admit_smt_queries true" make -j $EVEREST_THREADS package-noversion

WORKDIR $HOME
ENV EVERPARSE_HOME=$HOME/everparse
