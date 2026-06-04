# fstarpkg.Dockerfile
#
# Build and test EverParse against a F* *binary package* (fstar*.tar.gz, as
# published at https://github.com/FStarLang/fstar-nightly), instead of building
# F*, Karamel and Pulse from source. The binary package ships fstar.exe, the
# krml (Karamel) executable, the compiled Pulse libraries and the Z3 versions
# F* needs.
#
# The build context must be the EverParse root directory, and must contain the
# F* binary package tarball. By default the Linux x86_64 package is used
# (fstar-Linux-x86_64.tar.gz); override it with:
#     --build-arg FSTAR_PACKAGE=<name>.tar.gz
# The tarball is deliberately NOT committed to git (see .gitignore).
#
# Usage, from the EverParse root directory:
#     docker build -f fstarpkg.Dockerfile -t everparse-fstarpkg .
#
# `make lowparse` is run *without* ADMIT, so it actually invokes Z3 and thus
# checks that the Z3 bundled in the F* binary package is found and usable. The
# rest of the test suite is then run with ADMIT=1, to skip SMT and keep the
# build time reasonable.

FROM ubuntu:24.04 AS base
ENV DEBIAN_FRONTEND=noninteractive

# System dependencies from README.md (Ubuntu 24.04 "Prerequisites"), plus the
# additional packages needed to run the test suite (cmake, clang, python3-*).
# make/gcc/g++ are needed to build the C parts and the local OCaml compiler.
RUN apt-get update && apt-get install --yes --no-install-recommends \
      ca-certificates curl git pkg-config libffi-dev libgmp-dev \
      libsqlite3-dev libssl-dev time opam \
      make gcc g++ cmake clang python3-pip python3-venv \
 && rm -rf /var/lib/apt/lists/*

# Rust, for EverCBOR and EverCOSign.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
ENV PATH=/root/.cargo/bin:$PATH

# opam's bwrap sandbox cannot run inside an unprivileged `docker build`, so
# disable it. `opam init` reads ~/.opamrc for its default configuration.
RUN printf 'wrap-build-commands: []\nwrap-install-commands: []\nwrap-remove-commands: []\n' \
      > /root/.opamrc

# The F* binary package tarball. COPY (not ADD) so it is not auto-extracted,
# to a path outside the source tree so the `git clean` below cannot remove it.
ARG FSTAR_PACKAGE=fstar-Linux-x86_64.tar.gz
COPY ${FSTAR_PACKAGE} /opt/fstar-package.tar.gz

# The EverParse source tree, reduced to a pristine git checkout so that no host
# build artifacts (opt/opam, opt/FStar, config.Makefile, fstpkg, *.done stamps,
# the F* tarball copied above, ...) leak into the image.
ADD ./ /mnt/everparse/
WORKDIR /mnt/everparse
RUN git config --global --add safe.directory /mnt/everparse \
 && git clean -ffdx

# Configure EverParse to use the F* binary package: this extracts the tarball
# under opt/fstar-bin-package/ and points FSTAR_EXE/KRML_EXE at it.
RUN ./configure --fstar-bin-package-tar=/opt/fstar-package.tar.gz \
 && cat config.Makefile

FROM base AS deps

# Build EverParse's dependencies: a local opam root with everparse-deps, the
# F* application library (fstar.lib) from the package, and krmllib. With the
# binary package there is no F* source build and no Z3 download.
RUN make -j"$(nproc)" -f deps.Makefile

FROM deps AS test

# `make lowparse` runs Z3 (no ADMIT), checking the package's Z3 is usable;
# the rest of the suite runs with ADMIT=1 to skip SMT.
RUN make -j"$(nproc)" -k lowparse && ADMIT=1 make -j"$(nproc)" -k test
