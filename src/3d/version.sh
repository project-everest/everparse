#!/usr/bin/env bash

set -e

everparse_last_version=$(cat "$EVERPARSE_HOME/version.txt")

get_everparse_version() {
    (
	cd $EVERPARSE_HOME
        everparse_this_commit=$(git show --no-patch --format=%h)
        everparse_last_version_commit=$(git show --no-patch --format=%h $everparse_last_version || true)
	if [[ $everparse_this_commit = $everparse_last_version_commit ]]
	then
	    echo $everparse_last_version
	else
	    echo "$everparse_this_commit (unreleased)"
	fi
    )
}

echo module Version > Version.fst
echo "let everparse_version = \"$(get_everparse_version)\"" >> Version.fst
