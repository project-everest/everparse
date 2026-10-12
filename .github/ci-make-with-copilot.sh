#!/usr/bin/env bash
# Run a make target in the CI container; if it fails, ask GitHub Copilot CLI
# to fix it, then try again.
#
# The nightly job advances opt/hashes.Makefile to the newest F*, karamel and
# z3 before building, so a failure here is almost always a proof or an API
# that the upgrade broke.  Those are exactly the failures a coding agent can
# make a reasonable attempt at, and a nightly run that repairs itself is worth
# more than one that reports a red X at 22:00 on a Sunday.
#
# Usage: ci-make-with-copilot.sh <make argument>...
#
# Environment:
#   container              the CI container to build in (required)
#   EVERPARSE_SRC          the host checkout, synced into the container
#                          (default: everparse)
#   COPILOT_FIX_ATTEMPTS   how many times to let Copilot try (default: 3;
#                          0 disables it, restoring plain `make` behaviour)
#   COPILOT_GITHUB_TOKEN   Copilot credentials; if unset, no fix is attempted
#
# Copilot edits the *host* checkout, not the container: the host checkout is
# the one with a .git, so it is the one whose changes can be reviewed, diffed
# and pushed.  Only the files it actually touched are copied into the
# container between attempts -- re-uploading the whole tree would give every
# file a new mtime and send make back through the entire build.

set -u -o pipefail

: "${container:?ci-make-with-copilot: \$container is not set}"
src="${EVERPARSE_SRC:-everparse}"
attempts="${COPILOT_FIX_ATTEMPTS:-3}"

test $# -gt 0 || { echo "usage: $0 <make argument>..." >&2 ; exit 2 ; }

# Outside $src on purpose: anything inside it would show up as an untracked
# file and get committed with the fix.
logdir="${RUNNER_TEMP:-/tmp}/ci-make-logs"
mkdir -p "$logdir"
log="$logdir/$(date +%s)-$$.log"

quoted=$(printf '%q ' "$@")

run_make () {
    echo "ci-make-with-copilot: make $*"
    docker exec "$container" /usr/bin/env BASH_ENV=/home/test/.cargo/env \
           /bin/bash -c "bash .github/ci-make.sh $quoted" 2>&1 | tee "$log"
}

# Copy whatever Copilot changed into the container, and delete there whatever
# it deleted here.  Everything is relative to the top of $src, which is also
# the container's working directory.
#
# Returns 0 if something was synced, 2 if Copilot changed nothing, 1 on error.
sync_to_container () {
    local -a changed deleted
    local -a spec=(-- . ':(exclude)opt')
    mapfile -d '' -t deleted < <(git -C "$src" diff -z --name-only --diff-filter=D HEAD "${spec[@]}")
    mapfile -d '' -t changed < <(
        git -C "$src" diff -z --name-only --diff-filter=d HEAD "${spec[@]}"
        git -C "$src" ls-files -z --others --exclude-standard "${spec[@]}"
    )

    if test "${#changed[@]}" -eq 0 && test "${#deleted[@]}" -eq 0 ; then
        return 2
    fi

    if test "${#changed[@]}" -gt 0 ; then
        printf 'ci-make-with-copilot: uploading %s\n' "${changed[@]}"
        ( cd "$src" && printf '%s\0' "${changed[@]}" |
              tar -c --null -T - ) |
            docker exec -i "$container" tar -x --overwrite || return 1
    fi
    if test "${#deleted[@]}" -gt 0 ; then
        printf 'ci-make-with-copilot: deleting %s\n' "${deleted[@]}"
        docker exec "$container" rm -f -- "${deleted[@]}" || return 1
    fi
    return 0
}

copilot_prompt () {
    cat <<EOF
You are repairing the EverParse nightly CI build.

The command \`make $*\` just failed. It ran inside the Docker container
"$container", where this repository is checked out at /mnt/everparse and F*,
karamel and z3 are already built under /mnt/everparse/opt.

The full build log is at $log. It may be long; search it rather than reading
it whole. The failing command is near the end.

This job runs right after opt/hashes.Makefile was advanced to the newest F*,
karamel and z3, so the most likely cause is an upstream change: a proof that
no longer goes through, a renamed or removed lemma, a changed signature, a
new warning turned error, or a tactic that now behaves differently.

Investigate and fix it, subject to these rules:

- Edit files in the current working directory, which is the host checkout.
  Those edits -- and only those -- are copied into the container before the
  build is retried. Editing /mnt/everparse directly inside the container has
  no lasting effect and will be overwritten.
- You may run anything you like inside the container to investigate, for
  example:
      docker exec $container /usr/bin/env BASH_ENV=/home/test/.cargo/env \\
          /bin/bash -c "bash .github/ci-make.sh <target>"
  Note that a build there can take a long time; prefer checking a single
  file over re-running the whole target.
- Do not edit anything under opt/. Those are prebuilt dependencies, and
  changing opt/hashes.Makefile would defeat the purpose of this job.
- Do not weaken the specification to make the proof go through: no
  \`admit\`, \`assume\`, \`magic\`, \`--admit_smt_queries true\`, and no deleting
  or commenting out a lemma or a test. Adding a hint, an intermediate
  assertion, a fuel/ifuel adjustment or an explicit instantiation is fine.
- Do not run git commit, git push, or any other git command that writes to
  the repository. The workflow commits your changes itself.
- Do not leave scratch files behind; everything still in the working tree
  at the end gets committed.

If you cannot find a fix you are confident in, change nothing and say so.
EOF
}

if run_make "$@" ; then
    exit 0
fi

echo "ci-make-with-copilot: make $* failed." >&2

if test "$attempts" -le 0 ; then
    exit 1
fi

if test -z "${COPILOT_GITHUB_TOKEN:-}" ; then
    echo "ci-make-with-copilot: COPILOT_GITHUB_TOKEN is not set; not attempting a fix." >&2
    exit 1
fi

if ! command -v copilot > /dev/null ; then
    echo "ci-make-with-copilot: the copilot CLI is not installed; not attempting a fix." >&2
    exit 1
fi

for attempt in $(seq 1 "$attempts") ; do
    echo "::group::Copilot fix attempt $attempt of $attempts for: make $*"

    copilot \
        --prompt "$(copilot_prompt "$@")" \
        --allow-all \
        --no-color \
        -C "$src"
    status=$?
    echo "::endgroup::"

    if test $status -ne 0 ; then
        echo "ci-make-with-copilot: copilot exited with $status; giving up." >&2
        exit 1
    fi

    sync_to_container
    status=$?
    if test $status -eq 2 ; then
        # Copilot could not see a fix.  Spending another attempt on it is
        # cheap compared to the build, and the next one may do better.
        echo "ci-make-with-copilot: Copilot changed nothing on attempt $attempt." >&2
        continue
    fi
    if test $status -ne 0 ; then
        echo "ci-make-with-copilot: could not copy the fix into the container." >&2
        exit 1
    fi

    if run_make "$@" ; then
        echo "ci-make-with-copilot: fixed by Copilot on attempt $attempt."
        exit 0
    fi

    echo "ci-make-with-copilot: make $* still fails after attempt $attempt." >&2
done

echo "ci-make-with-copilot: still failing after $attempts Copilot attempt(s)." >&2
exit 1
