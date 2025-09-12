#!/usr/bin/env bash

set -e

FSTAR_EXE="${FSTAR_EXE:-fstar.exe}"

get_everparse_version() {
    (
	cd $EVERPARSE_HOME
	if [[ -f "$EVERPARSE_HOME/version.txt" ]] ; then
	    sed 's!\r!!g' $EVERPARSE_HOME/version.txt
	else
	    echo "$(git show --no-patch --format=%h)-unreleased"
	fi
    )
}

get_fstar_commit() {
    (
        $FSTAR_EXE --version | sed -n 's/commit=\(.\{10\}\).*/\1/p'
    )
}

get_karamel_commit() {
    (
	cd $KRML_HOME
        git show --no-patch --format=%h
    )
}

echo module Version
echo "let everparse_version = \"$(get_everparse_version)\""
echo "let fstar_commit = \"$(get_fstar_commit)\""
echo "let karamel_commit = \"$(get_karamel_commit)\""
