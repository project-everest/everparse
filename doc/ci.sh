#!/bin/bash
set -e
set -x

echo "Preparing to update the docs. We are on branch: $branchname"

# Test if we are on a branch that allows updating the EverParse docs.
if ! {
	[[ "$OS" != "Windows_NT" ]] && {
            [[ "$branchname" == "master" ]] ||
		[[ "$branchname" == "taramana_ci" ]]
	}
    }
then
    echo "Not on the master branch, exiting."
    exit 0
fi

# Check if a GitHub token is provided
if [[ -z "$DZOMO_GITHUB_TOKEN" ]] ; then
    echo "ERROR: Please specify a DZOMO_GITHUB_TOKEN"
    exit 1
fi

# Switch to the script's current directory.
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

# Overwrite the docs
git clone https://"$DZOMO_GITHUB_TOKEN"@github.com/project-everest/project-everest.github.io project-everest-github-io
rm -rf project-everest-github-io/everparse
mkdir project-everest-github-io/everparse
./copy.sh project-everest-github-io/everparse

# Commit the new files if any
cd project-everest-github-io
git add -A everparse
if git diff --exit-code HEAD > /dev/null; then
    echo "No git diff for the doc, not generating a commit"
    exit 0
fi
git add -u
git -c 'user.name=Dzomo, the Everest Yak' -c 'user.email=24394600+dzomo@users.noreply.github.com' commit -m "[CI] Refresh EverParse doc"
git push
