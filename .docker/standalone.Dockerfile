# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ADD --chown=opam:opam ./ everparse/
WORKDIR everparse

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get install -y --no-install-recommends jq

# Dependencies (F*, Karamel and opam packages)
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN eval $(opam env) && .docker/build/install-deps.sh

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master

RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH
