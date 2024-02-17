# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-22.04-ocaml-$ocaml_version

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# CI dependencies: jq (to identify F* branch)
# libicu (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends \
    jq \
    wget \
    libicu70 \
    && true

# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN wget -nv https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT && \
    echo 'export PATH=$PATH:$DOTNET_ROOT:$DOTNET_ROOT/tools' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile && \
    rm -f dotnet-sdk*.tar.gz

# Dependencies (F*, Karamel and opam packages)
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN eval $(opam env) && .docker/build/install-deps.sh

# CI dependencies: sphinx (for the docs)
# sudo pip3 because of https://bugs.launchpad.net/ubuntu/+source/bash/+bug/1588562
# jinja2==3.0.0 because of https://github.com/mkdocs/mkdocs/issues/2799
# alabaster==0.7.13 because of https://alabaster.readthedocs.io/en/latest/changelog.html (0.7.14 breaks old Sphinx versions.)
RUN sudo apt-get install --yes --no-install-recommends python3-pip python3-setuptools python3-distutils
RUN sudo pip3 install sphinx==1.7.2 jinja2==3.0.0 alabaster==0.7.13 sphinx_rtd_theme

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master

RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-standalone.sh $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV EVERPARSE_HOME=$HOME/everparse
