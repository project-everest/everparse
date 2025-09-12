# This Dockerfile should be run from the root EverParse directory

FROM ubuntu:24.04 AS base

# For the `deps` and `build` layers
# sudo for the Docker image
RUN apt-get update && apt-get install --yes --no-install-recommends \
  ca-certificates \
  curl \
  git \
  pkg-config \
  libffi-dev \
  libgmp-dev \
  libsqlite3-dev \
  libssl-dev \
  time \
  opam \
  sudo

# Create a new user and give them sudo rights
RUN useradd -d /home/test test
RUN echo 'test ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/test
RUN chown test:test /home/test
USER test
ENV HOME=/home/test
WORKDIR $HOME

# install rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Automatically set up Rust environment
SHELL ["/usr/bin/env", "BASH_ENV=/home/test/.cargo/env", "/bin/bash", "-c"]

# Set up code-server
RUN curl -L --output code-server.deb https://github.com/coder/code-server/releases/download/v4.103.2/code-server_4.103.2_amd64.deb \
 && sudo dpkg -i code-server.deb \
 && rm code-server.deb
RUN curl -L --output fstar-vscode-assistant.vsix https://github.com/FStarLang/fstar-vscode-assistant/releases/download/v0.19.2/fstar-vscode-assistant-0.19.2.vsix \
 && code-server --install-extension fstar-vscode-assistant.vsix \
 && rm fstar-vscode-assistant.vsix

# Bring in the contents
ARG CACHE_BUST
RUN sudo mkdir /mnt/everparse && sudo chown test:test /mnt/everparse
ARG CI_REPO=project-everest/everparse
ARG CI_BRANCH=master
RUN git clone --recurse-submodules --branch $CI_BRANCH https://github.com/$CI_REPO /mnt/everparse && echo $CACHE_BUST
WORKDIR /mnt/everparse

# For the release process: check if the current hash matches the hash being released
ARG CI_HASH
RUN if [[ -n "$CI_HASH" ]] ; then [[ "$CI_HASH" = "$(git rev-parse HEAD)" ]] ; fi

FROM base AS deps

ARG CI_THREADS
RUN sudo apt-get update && make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" deps
RUN cp src/package/start-code-server.sh .

# Automatically set up Rust environment
ENTRYPOINT ["/usr/bin/env", "BASH_ENV=/home/test/.cargo/env", "/mnt/everparse/shell.sh", "-c"]
CMD ["/bin/bash", "-i"]
SHELL ["/usr/bin/env", "BASH_ENV=/home/test/.cargo/env", "/mnt/everparse/shell.sh", "-c"]

FROM deps AS build

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" all

# For the `test` layer
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    cmake \
    python3-pip \
    python3-venv

FROM build AS test

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" test
