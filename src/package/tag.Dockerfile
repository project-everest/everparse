ARG CI_REPO=project-everest/everparse
ARG CI_BRANCH
FROM ghcr.io/$CI_REPO:$CI_BRANCH

# Automatically set up Rust environment
ENTRYPOINT ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/mnt/everparse/opt/shell.sh", "-c"]
CMD ["/bin/bash", "-i"]
SHELL ["/usr/bin/env", "BASH_ENV=/home/opam/.cargo/env", "/mnt/everparse/opt/shell.sh", "-c"]

# For the release process: check if the current hash matches the hash being released
ARG CI_HASH
RUN [[ "$CI_HASH" = "$(git rev-parse HEAD)" ]]

# For the release process: if a tag is provided, use it to label the current commit
ARG CI_TAG
RUN git tag "$CI_TAG"
