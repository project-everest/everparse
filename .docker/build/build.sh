#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

function export_home() {
    if command -v cygpath >/dev/null 2>&1; then
        export $1_HOME=$(cygpath -m "$2")
    else
        export $1_HOME="$2"
    fi
}

# By default, kremlin master works against F* stable. Can also be overridden.
function fetch_kremlin() {
    if [ ! -d kremlin ]; then
        git clone https://github.com/FStarLang/kremlin kremlin
    fi

    cd kremlin
    git fetch origin
    local ref=$(if [ -f ../.kremlin_version ]; then cat ../.kremlin_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to KreMLin $ref
    git reset --hard $ref
    cd ..
    export_home KREMLIN "$(pwd)/kremlin"
}

function fetch_and_make_kremlin() {
    fetch_kremlin

    # Default build target is minimal, unless specified otherwise
    local target
    if [[ $1 == "" ]]; then
        target="minimal"
    else
        target="$1"
    fi

    make -C kremlin -j $threads $target ||
        (cd kremlin && git clean -fdx && make -j $threads $target)
    OTHERFLAGS='--admit_smt_queries true' make -C kremlin/kremlib -j $threads
    export PATH="$(pwd)/kremlin:$PATH"
}

# NOTE: LowParse is currently part of miTLS
# By default, mitls-fstar master works against F* stable. Can also be overridden.
function fetch_lowparse() {
    if [ ! -d mitls-fstar ] ; then
        git clone --verbose https://github.com/mitls/mitls-fstar mitls-fstar
    fi
    cd mitls-fstar
    git fetch origin
    local ref=$(if [ -f ../.mitls_version ]; then cat ../.mitls_version | tr -d '\r\n'; else echo origin/master; fi)
    echo "Switching to LowParse (mitls-fstar) $ref"
    git reset --hard $ref
    git clean -fdx
    cd ..
    export_home LOWPARSE "$(pwd)/mitls-fstar/src/lowparse"
}

function fetch_and_make_lowparse() {
    fetch_lowparse &&

    cd lowparse && {
        env OTHERFLAGS='--admit_smt_queries true' make -f Makefile.LowParse -j $threads || {
            git clean -fdx &&
            env OTHERFLAGS='--admit_smt_queries true' make -f Makefile.LowParse -j $threads
        }
    } &&
    cd ..
}

function build_and_test_quackyducky() {
    fetch_and_make_kremlin &&
    fetch_and_make_lowparse &&
    make -j $threads -k test
}

function exec_build() {

    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false >$status_file

    if [ ! -f src/rfc_fstar_compiler.ml ]; then
        echo "I don't seem to be in the right directory, bailing"
        echo Failure >$result_file
        return
    fi

    # Ignore $target for now
    build_and_test_quackyducky && echo -n true >$status_file

    if [[ $(cat $status_file) != "true" ]]; then
        echo "Build failed"
        echo Failure >$result_file
    else
        echo "Build succeeded"
        echo Success >$result_file
    fi
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--print_z3_statistics --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

export_home FSTAR "$(pwd)/FStar"
cd quackyducky
exec_build
cd ..
