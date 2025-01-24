# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.14
FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version

# Set up git identity
RUN git config --global user.name 'Dzomo, the Everest Yak'
RUN --mount=type=secret,id=DZOMO_EMAIL git config --global user.email $(sudo cat /run/secrets/DZOMO_EMAIL)

# Install GitHub CLI
# From https://github.com/cli/cli/blob/trunk/docs/install_linux.md#debian-ubuntu-linux-raspberry-pi-os-apt
RUN { type -p curl >/dev/null || sudo apt-get install curl -y ; } \
    && curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg \
    && sudo chmod go+r /usr/share/keyrings/githubcli-archive-keyring.gpg \
    && echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null \
    && sudo apt-get update \
    && sudo apt-get install gh -y

# Bring in the contents
ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# Install other dependencies
RUN sudo apt-get install --yes \
  python-is-python3 \
  wget

# Build and publish the release
ARG CI_THREADS=24
ARG EVERPARSE_RELEASE_ORG=project-everest
ARG EVERPARSE_RELEASE_REPO=everparse
ARG EVERPARSE_TEST_RELEASE=
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && GH_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) EVERPARSE_RELEASE_ORG=$EVERPARSE_RELEASE_ORG EVERPARSE_RELEASE_REPO=$EVERPARSE_RELEASE_REPO EVERPARSE_TEST_RELEASE=$EVERPARSE_TEST_RELEASE make -j $CI_THREADS release
