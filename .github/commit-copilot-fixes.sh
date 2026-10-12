#!/usr/bin/env bash
# Commit and push whatever .github/ci-make-with-copilot.sh left in the working
# tree, if anything.
#
# A no-op on a clean tree, which is the normal case: the fix path only runs
# when a make command failed.
#
# Usage: commit-copilot-fixes.sh <commit message>
#
# Run from the top of the host checkout.  opt/ is excluded on purpose -- the
# submodules there are pinned by opt/hashes.Makefile, and a stray
# modification to one of them is not something to carry into the PR.

set -eu

message="${1:?usage: $0 <commit message>}"

git add -A -- . ':(exclude)opt'

if git diff --staged --quiet ; then
    echo "commit-copilot-fixes: nothing to commit."
    exit 0
fi

git --no-pager diff --staged --stat
git commit -m "$message"
git push
