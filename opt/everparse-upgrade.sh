#!/bin/bash

# Create a Bash script, expecting some "user@hostname" in the DEST
# environment variable, having this prompt in a comment, and doing the
# following:
#
# 1. Create a directory, `/tmp/everparseNNNN`, where NNNN is a timestamp
#    (YYYYMMDDhhnnss), and enter it.
#
# 2. Create a clone of EverParse from the `fstar2` branch of
#    `git@github.com:project-everest/everparse` into the `everparse`
#    subdirectory.
#
# 3. Use `ssh` to create, on $DEST, a directory with the same path and
#    name as in Step 1.
#
# 4. Use `ssh` to create, on $DEST, in the
#    `/tmp/everparseNNNN/everparse.git` subdirectory, an empty bare
#    repository (no working copy.)
#
# 5. In the `everparse` subdirectory, push the current `fstar2` branch
#    to `$DEST:/tmp/everparseNNNN/everparse.git`
#
# 6. Use `ssh` to create, on $DEST, in the
#    `/tmp/everparseNNNN/everparse` subdirectory, a clone of EverParse
#    from the `fstar2` branch of the `everparse.git` clone created on
#    $DEST at Step 4 and pushed at Step 5.
#
# 7. Use `ssh` to run, on $DEST, in the `/tmp/everparseNNNN/everparse`
#    subdirectory, GitHub Copilot CLI (`copilot`) with the
#    `--yolo --alt-screen --autopilot` options, telling Copilot to use
#    the prompt located in `/tmp/everparseNNNN/everparse/opt/upgrade.md`
#    on $DEST.
#
#    Run the command in such a way that the remote command collects its
#    output to a file (on $DEST), `/tmp/everparseNNNN/output.txt`, and
#    so that the `ssh` process exits without waiting for the remote
#    command to complete.
#
# 8. In the `everparse` subdirectory, sleep for 10 minutes and try
#    fast-forward pulling from the `fstar2` branch of
#    `$DEST:/tmp/everparseNNNN/everparse.git` . Repeat this "sleep and
#    pull", even if the fast-forward pull fails because of networking
#    issues, for a maximum of 24 hours, until pulling has modified the
#    clone or fails because the pull is not fast-forward.
#
# 9. If Step 8 completed with some changes successfully pulled by
#    fast-forward, then push the changes to the `fstar2` branch of
#    `git@github.com:project-everest/everparse` . If push fails because
#    the tip of `fstar2` has changed on GitHub, do not try to reconcile,
#    and skip this step. If the pull failed because it was not
#    fast-forward, or if the loop timed out, also skip this step.
#
# 10. In all cases, use `scp` to download
#     `/tmp/everparseNNNN/output.txt` from $DEST.

set -euo pipefail

if [ -z "${DEST:-}" ]; then
  echo "Error: DEST environment variable must be set to user@hostname" >&2
  exit 1
fi

# Step 1: Create /tmp/everparseNNNN and enter it
TIMESTAMP=$(date +%Y%m%d%H%M%S)
WORKDIR="/tmp/everparse${TIMESTAMP}"
mkdir -p "$WORKDIR"
cd "$WORKDIR"
echo "Step 1: Created and entered $WORKDIR"

# Step 2: Clone EverParse from fstar2 branch
git clone --branch fstar2 git@github.com:project-everest/everparse everparse
echo "Step 2: Cloned EverParse (fstar2 branch)"

# Step 3: Create same directory on $DEST
ssh "$DEST" "mkdir -p $WORKDIR"
echo "Step 3: Created $WORKDIR on $DEST"

# Step 4: Create empty bare repository on $DEST
ssh "$DEST" "git init --bare $WORKDIR/everparse.git"
echo "Step 4: Created bare repo $WORKDIR/everparse.git on $DEST"

# Step 5: Push fstar2 branch to $DEST bare repo
cd everparse
git remote add dest "$DEST:$WORKDIR/everparse.git"
git push dest fstar2
echo "Step 5: Pushed fstar2 to $DEST:$WORKDIR/everparse.git"

# Step 6: Clone from bare repo on $DEST
ssh "$DEST" "git clone --branch fstar2 $WORKDIR/everparse.git $WORKDIR/everparse"
echo "Step 6: Cloned everparse on $DEST from bare repo"

# Step 7: Run copilot on $DEST in background, collecting output
ssh -nT "$DEST" "cd $WORKDIR/everparse && setsid -f copilot -p 'Use \`opt/upgrade.md\` as your prompt' --yolo --alt-screen --autopilot > $WORKDIR/output.txt 2>&1 < /dev/null"
echo "Step 7: Started copilot on $DEST (background)"

# Step 8: Sleep-and-pull loop for up to 24 hours
HEAD_BEFORE=$(git rev-parse HEAD)
MAX_SECONDS=$((24 * 60 * 60))
ELAPSED=0
SLEEP_INTERVAL=$((10 * 60))
PULL_RESULT="timeout"

while [ "$ELAPSED" -lt "$MAX_SECONDS" ]; do
  sleep "$SLEEP_INTERVAL"
  ELAPSED=$((ELAPSED + SLEEP_INTERVAL))

  PULL_OUTPUT=$(git pull --ff-only dest fstar2 2>&1) && PULL_EXIT=0 || PULL_EXIT=$?

  if [ "$PULL_EXIT" -eq 0 ]; then
    HEAD_AFTER=$(git rev-parse HEAD)
    if [ "$HEAD_BEFORE" != "$HEAD_AFTER" ]; then
      PULL_RESULT="changed"
      echo "Step 8: Fast-forward pull brought new changes"
      break
    fi
  else
    if echo "$PULL_OUTPUT" | grep -qi "not possible to fast-forward\|non-fast-forward"; then
      PULL_RESULT="not-fast-forward"
      echo "Step 8: Pull is not fast-forward, stopping"
      break
    fi
    echo "Step 8: Pull failed (transient), retrying... (${ELAPSED}s elapsed)"
  fi
done

if [ "$PULL_RESULT" = "timeout" ]; then
  echo "Step 8: Loop timed out after 24 hours"
fi

# Step 9: Push to GitHub if changes were pulled successfully
if [ "$PULL_RESULT" = "changed" ]; then
  if git push origin fstar2 2>&1; then
    echo "Step 9: Pushed changes to GitHub"
  else
    echo "Step 9: Push failed (tip of fstar2 changed on GitHub), skipping"
  fi
else
  echo "Step 9: Skipping push (pull result: $PULL_RESULT)"
fi

# Step 10: Download output.txt from $DEST
cd "$WORKDIR"
scp "$DEST:$WORKDIR/output.txt" ./output.txt
echo "Step 10: Downloaded output.txt to $WORKDIR/output.txt"

echo "Done."
