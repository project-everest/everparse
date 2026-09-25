#!/bin/sh
# Run the Low*/Pulse differential test over one sub-directory test.
#
#   ./run_subdir.sh <output-dir>[=<pulse-output-dir>] <iters>
#
# e.g. ./run_subdir.sh ifdefs/obj 20000
#      ./run_subdir.sh output_types/interpret.out=output_types/TPoint.out
#
# The two test trees mirror each other, so one relative path usually names
# both the Low* output under src/3d/tests and the Pulse output under
# share/everparse/tests/3d; the `=` form is for the few that diverge. The set
# of entrypoints is read from the Pulse side, so pairing a narrow Pulse
# directory against a wider Low* one tests just that subset.
#
# Exits non-zero if the backends disagree.
set -e

REL="$1"
ITERS="${2:-20000}"
LO_REL="${REL%%=*}"
PU_REL="${REL#*=}"
HERE=$(cd "$(dirname "$0")" && pwd)
: "${EVERPARSE_HOME:=$(cd "$HERE/../../../.." && pwd)}"
: "${CC:=cc}"
: "${PYTHON:=python3}"

LO_ROOT="$EVERPARSE_HOME/src/3d/tests"
PU_ROOT="$EVERPARSE_HOME/share/everparse/tests/3d"
LO="$LO_ROOT/$LO_REL"
PU="$PU_ROOT/$PU_REL"
TAG=$(echo "$PU_REL" | tr '/.' '__')
WORK="$HERE/sub/$TAG"

if [ ! -d "$LO" ] || [ ! -d "$PU" ]; then
  echo "pulse-diff: $PU_REL: not built in both trees, skipping" >&2
  exit 0
fi

# The test's own sources: a hand-written main, and the error callbacks that
# main installs. The generated driver supplies both itself, so those files
# must be left out; everything else (external-typedef implementations, for
# instance) has to be linked in.
support() {
  root="$1"
  for f in "$root"/*.c "$root"/src/*.c; do
    [ -e "$f" ] || continue
    grep -qE '\<main[[:space:]]*\(|EverParseError[[:space:]]*\(' "$f" || echo "$f"
  done
}

# Likewise inside the output directory: Z3TestGen drops a testcases.c there
# which has its own main and its own copies of the probe externs.
#
# A batch directory may also hold several independent tests that were never
# meant to be linked together -- output_types/interpret.out has two modules
# that each define SetOpointDerefX. So when the Pulse side names a subset of
# the modules, drop the other wrapper modules' files here. Anything that is
# not a wrapper module (a dependency module such as modules/obj's AA.c) is
# always kept.
WANTED=$(cd "$PU" && ls *Wrapper.h 2>/dev/null | sed 's/Wrapper\.h$//' | tr '\n' ' ')
generated() {
  others=$(cd "$1" && ls *Wrapper.h 2>/dev/null | sed 's/Wrapper\.h$//' | tr '\n' ' ')
  for f in "$1"/*.c; do
    [ -e "$f" ] || continue
    grep -qE '\<main[[:space:]]*\(' "$f" && continue
    b=$(basename "$f")
    drop=
    for m in $others; do
      case " $WANTED " in *" $m "*) continue;; esac
      case "$b" in "$m".c|"$m"_*.c|"$m"Wrapper.c) drop=1;; esac
    done
    [ -n "$drop" ] || echo "$f"
  done
}

SUBROOT_LO=$LO_ROOT/$(dirname "$LO_REL")
SUBROOT_PU=$PU_ROOT/$(dirname "$PU_REL")

CFLAGS="-O1 -g -std=c11 -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE"
CFLAGS="$CFLAGS -Wno-unknown-warning-option -Wno-ignored-qualifiers"
CFLAGS="$CFLAGS -Wno-unused-parameter -Wno-type-limits"

rm -rf "$WORK"
mkdir -p "$WORK"

# Entrypoints come from the Pulse side, so that a narrow Pulse directory
# paired with a wider Low* one tests exactly the Pulse subset.
"$PYTHON" "$HERE/gen_diff.py" "$PU" "$WORK/driver.c"

# EverParse.h is not copied into every output directory, so fall back to the
# batch output of the corresponding tree, which always has one.
$CC $CFLAGS -I "$HERE" -I "$LO" -I "$SUBROOT_LO" -I "$SUBROOT_LO/src" \
    -I "$EVERPARSE_HOME/src/3d" -I "$EVERPARSE_HOME/src/3d/prelude/buffer" \
    -I "$LO_ROOT/out.batch" \
    -o "$WORK/lo" "$WORK/driver.c" "$HERE/harness.c" \
    $(generated "$LO") $(support "$SUBROOT_LO")

$CC $CFLAGS -I "$HERE" -I "$PU" -I "$SUBROOT_PU" -I "$SUBROOT_PU/src" \
    -I "$PU_ROOT" -I "$EVERPARSE_HOME/src/3d" -I "$PU_ROOT/out.pulse" \
    -o "$WORK/pu" "$WORK/driver.c" "$HERE/harness.c" \
    $(generated "$PU") $(support "$SUBROOT_PU")

# Fuzz with both, replay the union through both. Some tests print from their
# error-handler macro; that goes to stderr and is not part of the comparison.
"$WORK/lo" fuzz "$WORK/corpus_lo.bin" "$ITERS" 2>/dev/null
"$WORK/pu" fuzz "$WORK/corpus_pu.bin" "$ITERS" 2>/dev/null
cat "$WORK/corpus_lo.bin" "$WORK/corpus_pu.bin" >"$WORK/corpus.bin"
"$WORK/lo" replay "$WORK/corpus.bin" >"$WORK/trace_lo.txt" 2>/dev/null
"$WORK/pu" replay "$WORK/corpus.bin" >"$WORK/trace_pu.txt" 2>/dev/null

if diff -q "$WORK/trace_lo.txt" "$WORK/trace_pu.txt" >/dev/null; then
  echo "pulse-diff: $PU_REL: $(wc -l <"$WORK/trace_lo.txt") cases, Low* and Pulse identical"
else
  echo "pulse-diff: $PU_REL: FAIL, Low* and Pulse disagree"
  diff "$WORK/trace_lo.txt" "$WORK/trace_pu.txt" | head -40
  exit 1
fi
