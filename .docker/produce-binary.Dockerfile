# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends \
    jq \
    wget \
    python-is-python3 \
    libgmp-dev pkg-config \
    && true

# Dependencies (F*, Karamel and opam packages)
# NOTE: $PULSE_HOME is now $PULSE_REPO/out, cf. FStarLang/pulse#246
ENV FSTAR_DIR=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
ENV PULSE_REPO=$HOME/pulse
ENV PULSE_HOME=$PULSE_REPO/out
RUN eval $(opam env) && .docker/build/install-deps.sh --skip-build --skip-z3
ENV FSTAR_EXE=$FSTAR_DIR/bin/fstar.exe

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master

RUN eval $(opam env) && OTHERFLAGS="--admit_smt_queries true" make -f package.Makefile -j $CI_THREADS package-noversion

WORKDIR $HOME
ENV EVERPARSE_HOME=$HOME/everparse
