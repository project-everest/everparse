#!/usr/bin/env bash
# Tell make that the dependencies in opt/ (opam, F*, karamel) are already built.
#
# The container image produced by the `deps` job contains a complete build of
# opt/, but it is built from a sparse checkout.  Downstream jobs overwrite
# /mnt/everparse with a tarball of a full, fresh checkout, so every tracked
# file -- in particular opt/hashes.Makefile -- gets a brand new mtime.  That
# makes opt/FStar/Makefile, and hence opt/FStar.done, look out of date, and
# every job re-enters the F* build.  That used to be a quarter-second no-op,
# but now it re-runs the Custard extraction of the Pulse plugin, which is slow
# and memory hungry enough to get the job OOM-killed.
#
# So: backdate everything the dependency stamps are computed from, then mark
# the stamps themselves as fresh.  This cannot mask a stale image, because the
# image is keyed on the contents of opt/hashes.Makefile and Dockerfile.

set -eu

old='2000-01-01 00:00:00'

touch -c -d "$old" \
      opt/hashes.Makefile \
      opt/FStar opt/FStar/Makefile \
      opt/karamel opt/karamel/Makefile \
      opt/opam opt/opam/opam-init/init.sh \
      opt/fstar-deps.opam opt/everparse-deps.opam

touch opam-env.Makefile \
      opt/opam.done opt/FStar.done opt/karamel.done opt/z3

# Report what make makes of the result, so that a regression here is easy to
# diagnose from the job log.
echo '--- make -f deps.Makefile -n --debug=b deps ---'
make -f deps.Makefile -n --debug=b deps || true
