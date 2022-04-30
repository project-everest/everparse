# This Dockerfile should be run from the root Karamel directory

ARG FSTAR_BRANCH=master
FROM fstar:local-branch-$FSTAR_BRANCH

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# Dependencies (opam packages)
RUN eval $(opam env) && .docker/build/install-other-deps.sh

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-hierarchic.sh $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV KRML_HOME $HOME/everparse/karamel
ENV EVERPARSE_HOME $HOME/everparse
