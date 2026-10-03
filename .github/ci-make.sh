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

# The prebuilt binaries this image exists to provide.  Checked before the
# build and, if the build fails, again afterwards -- because the interesting
# failure is one where they were there and then were not.
#
# That has been seen once: a run in which `fstar.exe --dep` completed
# normally, make re-executed itself to read the generated .depend, and every
# invocation after that died with "not found".  The container was otherwise
# healthy and a sibling job sharing the same image passed, so the binary went
# away underneath a live build.  Forty lines of ENOENT from make do not say
# that; this does.
deps=("$opt/FStar/out/bin/fstar.exe" "$opt/karamel/out/bin/krml")

check_deps () {
    local missing=0 f
    for f in "${deps[@]}"; do
        test -x "$f" || { echo "ci-make: missing or not executable: $f" >&2
                          ls -ld --full-time "$f" >&2 || true
                          missing=1 ; }
    done
    return $missing
}

if ! check_deps; then
    echo "ci-make: the deps image is incomplete; not starting the build." >&2
    exit 1
fi

set -x
make "${args[@]}" "$@" && status=0 || status=$?
{ set +x ; } 2>/dev/null

if test $status -ne 0 && ! check_deps; then
    echo "ci-make: a prebuilt dependency disappeared during the build." >&2
    echo "ci-make: it was present before make started, so this is not a stale" >&2
    echo "ci-make: or incomplete image -- retry the job." >&2
fi

exit $status
