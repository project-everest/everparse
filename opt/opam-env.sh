#!/usr/bin/env bash
unset CDPATH
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
if [[ -z "$OPAMROOT" ]] ; then
    OPAMROOT=$(pwd)/opam
    root_opam=--root=opam
else
    root_opam="--root=$OPAMROOT"
fi
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
