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
  libicu74 \
  libsqlite3-dev \
  libssl-dev \
  time \
  opam \
  sudo \
  && rm -rf /var/lib/apt/lists/*

# For the `test` layer
RUN apt-get update && sudo apt-get install --yes --no-install-recommends \
    cmake \
    clang \
    python3-pip \
    python3-venv \
    && rm -rf /var/lib/apt/lists/*

# Create a new user and give them sudo rights
RUN useradd -d /home/test test
RUN echo 'test ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/test
RUN chown test:test /home/test
USER test
ENV HOME=/home/test
WORKDIR $HOME

# install rust
# `--profile minimal` skips rust-docs, rustfmt and clippy, none of which the
# build uses; `cargo doc` only needs rustdoc, which ships with rustc.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal

# Automatically set up Rust environment
SHELL ["/usr/bin/env", "BASH_ENV=/home/test/.cargo/env", "/bin/bash", "-c"]

# Install the .NET SDK, to build and run the standalone hash checker
# (src/3d/hashchk). The version must satisfy src/3d/hashchk/global.json,
# which requires .NET 10.0.100 or higher.
ARG DOTNET_SDK_VERSION=10.0.401
RUN curl -fsSL https://dot.net/v1/dotnet-install.sh -o dotnet-install.sh \
 && bash dotnet-install.sh --version $DOTNET_SDK_VERSION --install-dir $HOME/.dotnet \
 && rm dotnet-install.sh
ENV PATH=/home/test/.dotnet:$PATH
ENV DOTNET_CLI_TELEMETRY_OPTOUT=1
ENV DOTNET_NOLOGO=1
ENV DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1

# Bring in the contents
ADD --chown=test:test ./ /mnt/everparse/
WORKDIR /mnt/everparse
RUN git clean -ffdx || true
RUN { git submodule init && git submodule update && git submodule foreach --recursive git clean -ffdx ; } || true

FROM base AS deps

ARG CI_THREADS
# The prune must happen in the same RUN as the build: `--target deps` keeps
# every layer, so anything deleted in a later layer is still shipped.
RUN make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" -f deps.Makefile \
 && ./.github/prune-deps.sh
RUN cp src/package/start-code-server.sh .

# Automatically set up Rust environment
ENTRYPOINT ["/usr/bin/env", "BASH_ENV=/home/test/.cargo/env", "/mnt/everparse/shell.sh", "-c"]
CMD ["/bin/bash", "-i"]
SHELL ["/usr/bin/env", "BASH_ENV=/home/test/.cargo/env", "/mnt/everparse/shell.sh", "-c"]

FROM deps AS build

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" all

FROM build AS test

RUN OTHERFLAGS='--admit_smt_queries true' make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" test

# Set up code-server. This lives in the last stage on purpose: it is only for
# interactive use of the developer image, and CI (which builds `--target deps`)
# would otherwise pay for it in every cached image.
RUN curl -L --output code-server.deb https://github.com/coder/code-server/releases/download/v4.103.2/code-server_4.103.2_amd64.deb \
 && sudo dpkg -i code-server.deb \
 && rm code-server.deb
RUN curl -L --output fstar-vscode-assistant.vsix https://github.com/FStarLang/fstar-vscode-assistant/releases/download/v0.19.2/fstar-vscode-assistant-0.19.2.vsix \
 && code-server --install-extension fstar-vscode-assistant.vsix \
 && rm fstar-vscode-assistant.vsix
