#!/usr/bin/env bash

set -e

everparse_last_version=$(sed 's!\r!!g' $EVERPARSE_HOME/version.txt)

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

get_fstar_commit() {
    (
	cd $FSTAR_HOME
        git show --no-patch --format=%h
    )
}

get_karamel_commit() {
    (
	cd $KRML_HOME
        git show --no-patch --format=%h
    )
}

echo module Version > Version.fst
echo "let everparse_version = \"$(get_everparse_version)\"" >> Version.fst
echo "let fstar_commit = \"$(get_fstar_commit)\"" >> Version.fst
echo "let karamel_commit = \"$(get_karamel_commit)\"" >> Version.fst
