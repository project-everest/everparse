#!/usr/bin/env bash
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
if ! [[ "$EVERPARSE_USE_OPAMROOT" = 1 ]] ; then
        OPAMROOT="$(pwd)/opam"
elif [[ -z "$OPAMROOT" ]] ; then
	OPAMROOT="$(opam var root | $SED 's!\r!!g')"
fi
if [[ "$OS" = Windows_NT ]] ; then
    OPAMROOT="$(cygpath -m "$OPAMROOT")"
fi
root_opam="--root=$OPAMROOT"
opam env "$root_opam" --set-root --shell=sh |
    if [[ "$1" = --shell ]] ; then
        cat
    else
	$SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!' |
	$SED '/^export PATH := /d'
    fi
if [[ "$1" != --shell ]] ; then
    # Recompute from the caller's PATH instead of duplicating a cached snapshot
    # on every make restart. cmd.exe drops PATH entirely above 8191 characters.
    echo 'export PATH := $(shell eval "$$("$(EVERPARSE_OPT_PATH)/opam-env.sh" --shell)" && printf "%s" "$$PATH")'
fi
if [[ "$1" = --shell ]] ; then
    equal="="
    if [[ "$OS" = Windows_NT ]] ; then
	eocamlpath="';'"'"$OCAMLPATH"'
	eopamswitchprefixunix='"$(cygpath -u "$OPAM_SWITCH_PREFIX")"'
	eopamswitchprefixwindows='"$(cygpath -m "$OPAM_SWITCH_PREFIX")"'
    else
	eocamlpath=':"$OCAMLPATH"'
	eopamswitchprefixunix='$OPAM_SWITCH_PREFIX'
    fi
else
    equal=':='
    if [[ "$OS" = Windows_NT ]] ; then
	eopamswitchprefixunix='$(shell cygpath -u "$(OPAM_SWITCH_PREFIX)")'
	eopamswitchprefixwindows='$(shell cygpath -m "$(OPAM_SWITCH_PREFIX)")'
	eocamlpath=';$(OCAMLPATH)'
    else
	eopamswitchprefixunix='$(OPAM_SWITCH_PREFIX)'
	eocamlpath=':$(OCAMLPATH)'
    fi
fi
if [[ "$OS" = Windows_NT ]] ; then
    # Work around an opam bug about `opam var lib`
    echo 'export OCAMLPATH'"$equal$eopamswitchprefixwindows/lib$eocamlpath"
fi
