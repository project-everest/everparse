#!/usr/bin/env bash
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
if [[ -z "$EVERPARSE_USE_OPAMROOT" ]] ; then
        OPAMROOT="$(pwd)/opam"
elif [[ -z "$OPAMROOT" ]] ; then
	OPAMROOT="$(opam var root)"
fi
root_opam="--root=$OPAMROOT"
opam env "$root_opam" --set-root --shell=sh | grep -v '^PATH=' |
    if [[ "$1" = --shell ]] ; then
	cat
    else
	$SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!'
    fi
if [[ "$1" = --shell ]] ; then
    equal="='"
    epath="'"':"$PATH"'
else
    equal=':='
    epath=':$(PATH)'
fi
echo 'export PATH'$equal"$OPAMROOT/$(opam switch "$root_opam" show)/bin$epath"
