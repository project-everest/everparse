#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

function export_home() {
    local home_path=""
    if command -v cygpath >/dev/null 2>&1; then
        home_path=$(cygpath -m "$2")
    else
        home_path="$2"
    fi

    export $1_HOME=$home_path

    # Update .bashrc file
    token=$1_HOME=
    if grep -q "$token" ~/.bashrc; then
        sed -i -E "s|$token.*|$token$home_path|" ~/.bashrc
    else
        echo "export $1_HOME=$home_path" >> ~/.bashrc
    fi
}

# By default, karamel master works against F* stable. Can also be overridden.
function fetch_karamel() {
    if [ ! -d karamel ]; then
        git clone https://github.com/FStarLang/karamel karamel
    fi

    cd karamel
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["karamel_version"]' "$rootPath/.docker/build/config.json" )
    echo Switching to KaRaMeL $ref
    git reset --hard $ref
    cd ..
    export_home KRML "$(pwd)/karamel"
}

function fetch_and_make_karamel() {
    fetch_karamel

    # Default build target is minimal, unless specified otherwise
    local target
    if [[ $1 == "" ]]; then
        target="minimal"
    else
        target="$1"
    fi

    make -C karamel -j $threads $target ||
        (cd karamel && git clean -fdx && make -j $threads $target)
    OTHERFLAGS='--admit_smt_queries true' make -C karamel/krmllib -j $threads
    export PATH="$(pwd)/karamel:$PATH"
}

function fetch_hacl() {
    if [ ! -d hacl-star ]; then
        git clone https://github.com/project-everest/hacl-star hacl-star
    fi

    cd hacl-star
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["hacl_version"]' "$rootPath/.docker/build/config.json" )
    echo Switching to 'HACL*' $ref
    git reset --hard $ref
    cd ..
    export_home HACL "$(pwd)/hacl-star"
}

function fetch_and_make_hacl() {
    fetch_hacl
    make -C hacl-star/dist/gcc-compatible -j $threads
    make -C hacl-star/dist/gcc-compatible install-hacl-star-raw
    (cd hacl-star/bindings/ocaml && dune build @install && dune install)
}

# Nightly build: verify miTLS parsers
# (necessary since miTLS builds check them with "--admit_smt_queries true")
function fetch_mitls() {
    if [ ! -d mitls-fstar ]; then
        git clone https://github.com/project-everest/mitls-fstar mitls-fstar
    fi
    cd mitls-fstar
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["mitls_version"]' "$rootPath/.docker/build/config.json" )
    echo Switching to miTLS $ref
    git reset --hard $ref
    cd ..
    export_home MITLS "$(pwd)/mitls-fstar"
}

function rebuild_doc () {
   if
      [[ "$OS" != "Windows_NT" ]] &&
      [[ "$branchname" == "master" ]]
   then
       git clone git@github.com:project-everest/project-everest.github.io project-everest-github-io &&
       rm -rf project-everest-github-io/everparse &&
       mkdir project-everest-github-io/everparse &&
       doc/ci.sh project-everest-github-io/everparse &&
       pushd project-everest-github-io && {
           git add -A everparse &&
           if ! git diff --exit-code HEAD > /dev/null; then
               git add -u &&
               git commit -m "[CI] Refresh EverParse doc" &&
               git push
           else
               echo No git diff for the doc, not generating a commit
           fi
           errcode=$?
       } &&
       popd &&
       return $errcode
   fi
}

function test_mitls_parsers () {
        fetch_and_make_karamel &&
        OTHERFLAGS='--admit_smt_queries true' make -j $threads quackyducky lowparse &&
        export_home EVERPARSE "$(pwd)" &&
        fetch_mitls &&
        make -j $threads -C $MITLS_HOME/src/parsers verify
}

function nightly_test_quackyducky () {
    test_mitls_parsers
}

function raise () {
    return $1
}

function build_and_test_quackyducky() {
    # Rebuild the EverParse documentation and push it to project-everest.github.io
    rebuild_doc &&
    # Test EverParse proper
    fetch_and_make_karamel &&
    fetch_and_make_hacl &&
    env WITH_STEEL_C_ARRAY=1 make -j $threads -k ci &&
    # Build incrementality test
    pushd tests/sample && {
        {
            echo 'let foo : FStar.UInt32.t = 42ul' >> Data.fsti &&
            echo 'let foo : FStar.UInt32.t = Data.foo' >> Test.fst &&
            make -j $threads &&
            git checkout Test.fst &&
            sed -i 's!payloads!payload!g' Test.rfc &&
            make -j $threads &&
            git checkout Test.rfc
        }
        err=$?
        popd
    } &&
    if [[ "$err" -gt 0 ]] ; then return "$err" ; fi &&
    true
}

function exec_build() {

    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false >$status_file

    if [[ $target == "quackyducky_nightly_test" ]]
    then
        nightly_test_quackyducky
    else
        build_and_test_quackyducky
    fi && { echo -n true >$status_file ; }

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
export OTHERFLAGS="--query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

export_home FSTAR "$(pwd)/FStar"
cd quackyducky
rootPath=$(pwd)
exec_build
cd ..
