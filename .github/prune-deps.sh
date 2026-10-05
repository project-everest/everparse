#!/usr/bin/env bash
set -e

# Delete the intermediate build artifacts of the prebuilt dependencies in opt/.
#
# This must run in the *same* Docker RUN as the build that produced them,
# otherwise the fat layer stays in the image and only gets whited out.
#
# What has to survive is everything that EverParse's own build reaches for:
#
#   * opt/FStar/out -> stage3/out, whose lib/fstar/{ulib,ulib.checked} are in
#     turn symlinks to opt/FStar/ulib and opt/FStar/stage2/ulib.checked, and
#     whose lib/fstar/pulse/{common,pulse}.checked are symlinks to
#     opt/FStar/pulse/build/lib.{common,pulse}.checked;
#   * opt/karamel/out and opt/karamel/{krmllib,include,misc};
#   * the opam switch.
#
# Everything else below is scaffolding that only the dependency build needs.

cd "$(dirname "$0")/.."
opt=${EVERPARSE_OPT_PATH:-$PWD/opt}

du -sh "$opt" || true

# F*: the stage0/stage1/stage2 bootstrap chain and the dune build trees.
rm -rf "$opt"/FStar/stage0
rm -rf "$opt"/FStar/stage1
rm -rf "$opt"/FStar/stage2/dune \
       "$opt"/FStar/stage2/fstarc.checked \
       "$opt"/FStar/stage2/fstarc.ml \
       "$opt"/FStar/stage2/out
rm -rf "$opt"/FStar/stage3/dune
# Pulse: keep only the two checked-file directories that the install symlinks to.
find "$opt"/FStar/pulse/build -mindepth 1 -maxdepth 1 \
     ! -name lib.common.checked ! -name lib.pulse.checked \
     -exec rm -rf {} +
rm -rf "$opt"/FStar/.git

# karamel: the dune build tree.
rm -rf "$opt"/karamel/_build
rm -rf "$opt"/karamel/.git

# opam: package sources, download cache and the repository metadata are only
# needed to *install* packages, not to use them.
rm -rf "$opt"/opam/*/.opam-switch/sources
rm -rf "$opt"/opam/download-cache
rm -rf "$opt"/opam/repo

# All those rm -rf bumped the mtime of opt/ and of its subdirectories, which
# makes the dependency stamps look out of date.  That matters immediately: the
# image's ENTRYPOINT sources env.sh, which runs `make -f deps.Makefile`, so a
# plain `docker run` would try to rebuild the dependencies -- and fail, since
# the scaffolding it needs is exactly what we just deleted.
#
# Backdating the stamps is not enough on its own: downstream jobs overwrite
# /mnt/everparse with a fresh checkout, which gives opt/hashes.Makefile a brand
# new mtime again.  So also drop a marker that tells deps.Makefile the
# dependencies are prebuilt and must never be remade.
touch "$opt"/.prebuilt
./.github/mark-deps-up-to-date.sh > /dev/null

du -sh "$opt"
