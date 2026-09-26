#!/usr/bin/env bash
# Run make in a CI container built from the `deps` Docker image.
#
# That image already contains a complete build of opt/ (opam, F*, karamel,
# z3).  Downstream jobs overwrite /mnt/everparse with a tarball of a fresh
# checkout, which gives every tracked file -- including opt/hashes.Makefile
# and the F*/karamel submodule contents -- a brand new mtime.  Make then
# considers opt/FStar.done and friends out of date and re-enters the F*
# build.  That used to be a quarter-second no-op, but it now re-runs the
# Custard extraction of the Pulse plugin, which is slow and memory hungry
# enough to get the job OOM-killed.
#
# .github/mark-deps-up-to-date.sh puts the timestamps back in order, but
# rather than rely on that alone, tell make outright never to remake the
# dependency stamps, and never to remake anything on account of them.  This
# cannot mask a stale image, because the image is keyed on the contents of
# opt/hashes.Makefile and Dockerfile.

set -eu

opt="$(cd opt && pwd)"

args=()
for f in \
    "$opt/hashes.Makefile" \
    "$opt/FStar/Makefile" \
    "$opt/karamel/Makefile" \
    "$opt/opam/opam-init/init.sh" \
    "$opt/opam.done" \
    "$opt/FStar.done" \
    "$opt/karamel.done" \
    "$opt/z3" \
    ; do
    args+=(--old-file="$f")
done

set -x
exec make "${args[@]}" "$@"
