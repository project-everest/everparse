#!/usr/bin/env bash
# Ask GitHub Copilot CLI to write the body of the nightly pull request.
#
# Usage: copilot-pr-description.sh <base sha> <head sha> <output file>
#
# Run from the top of a full checkout of <head sha>.  Writes <output file>
# only if Copilot produced something; the caller is expected to fall back to
# `gh pr create --fill-verbose` if the file is missing or empty, so a failure
# here must never fail the job.
#
# Copilot writes the file itself rather than having its stdout captured: in
# prompt mode the response can carry commentary around the answer, and a
# stray "Here is the description:" would end up in the pull request.

set -u

base="${1:?usage: $0 <base sha> <head sha> <output file>}"
head="${2:?usage: $0 <base sha> <head sha> <output file>}"
out="${3:?usage: $0 <base sha> <head sha> <output file>}"

timeout_s="${COPILOT_FIX_TIMEOUT:-1800}"

if test -z "${COPILOT_GITHUB_TOKEN:-}" ; then
    echo "copilot-pr-description: COPILOT_GITHUB_TOKEN is not set; skipping." >&2
    exit 0
fi

if ! command -v copilot > /dev/null ; then
    echo "copilot-pr-description: the copilot CLI is not installed; skipping." >&2
    exit 0
fi

rm -f "$out"

prompt=$(cat <<EOF
Write the body of a pull request for this repository, EverParse, into the
file $out.

The pull request comes from the nightly job. That job advances
opt/hashes.Makefile to the newest F*, karamel and z3, regenerates the 3D
documentation and the CBOR and COSE snapshots against them, and, if the
upgrade broke the build or the test suite, may also contain repairs that
GitHub Copilot CLI made to get it passing again.

The changes are the commits $base..$head. Read them with git log and git
diff. The regenerated snapshots can be enormous and are extracted C and Rust;
summarize them, do not read them whole. Spend your effort on the hand-written
sources instead: those are what a reviewer has to judge.

Cover, in this order, and only where there is something to say:

- which dependency versions moved, and to what
- what had to change in the EverParse sources to accommodate them, and why;
  if a proof was repaired, say what broke and what the repair was
- which snapshots or docs were regenerated, and whether that is a mechanical
  consequence of the above or evidence of a real change in behaviour
- anything a reviewer should look at closely, in particular a repair that
  weakens a proof or a specification

Rules:

- GitHub-flavoured Markdown. No title and no top-level heading: the title is
  supplied separately.
- Be specific and short. Name the files and the lemmas. Do not pad the
  description with a summary of what the nightly job does in general, and do
  not invent a change you have not seen in the diff.
- If the only changes are a dependency bump and mechanically regenerated
  snapshots, say exactly that in a couple of lines and stop.
- Write $out and nothing else. Do not commit, do not push, do not create or
  comment on a pull request, and do not modify the working tree.
EOF
)

timeout "$timeout_s" copilot \
    --prompt "$prompt" \
    --allow-all \
    --disable-builtin-mcps \
    --no-color
status=$?

if test $status -ne 0 ; then
    echo "copilot-pr-description: copilot exited with $status; falling back." >&2
    rm -f "$out"
    exit 0
fi

if ! test -s "$out" ; then
    echo "copilot-pr-description: copilot wrote no description; falling back." >&2
    rm -f "$out"
    exit 0
fi

echo "copilot-pr-description: wrote $out:"
cat "$out"
