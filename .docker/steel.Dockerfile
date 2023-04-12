# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends jq

# Dependencies (F*, Karamel and opam packages)
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
ENV FSTAR_BRANCH=john_ml_steel_c
RUN eval $(opam env) && .docker/build/install-deps.sh
# Compile SteelC extraction plugin
RUN eval $(opam env) && make -j 24 -C $FSTAR_HOME/examples/steel/arraystructs/my_fstar

# CI proper
ARG CI_THREADS=24

ENV STEEL_C=1
RUN eval $(opam env) && make -j $CI_THREADS steel-unit-test

WORKDIR $HOME
ENV EVERPARSE_HOME=$HOME/everparse
