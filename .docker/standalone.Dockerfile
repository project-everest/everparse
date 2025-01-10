# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends \
    jq \
    wget \
    && true

# Dependencies (F*, Karamel and opam packages)
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN eval $(opam env) && .docker/build/install-deps.sh
ENV FSTAR_EXE=$FSTAR_HOME/bin/fstar.exe

# CI dependencies: sphinx (for the docs)
# sudo pip3 because of https://bugs.launchpad.net/ubuntu/+source/bash/+bug/1588562
# --break-system-packages because of PEP 668
# jinja2==3.0.0 because of https://github.com/mkdocs/mkdocs/issues/2799
# alabaster==0.7.13 because of https://alabaster.readthedocs.io/en/latest/changelog.html (0.7.14 breaks old Sphinx versions.)
RUN sudo apt-get install --yes --no-install-recommends python3-pip python3-setuptools python3-distutils
RUN sudo pip3 install --break-system-packages pytz tzdata sphinx==1.7.2 jinja2==3.0.0 alabaster==0.7.13 sphinx_rtd_theme || sudo pip3 install pytz tzdata sphinx==1.7.2 jinja2==3.0.0 alabaster==0.7.13 sphinx_rtd_theme

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master

RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV EVERPARSE_HOME=$HOME/everparse
