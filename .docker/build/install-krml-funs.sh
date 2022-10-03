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
