# By default, karamel master works against F* stable. Can also be overridden.
function fetch_steel() {
    if [ ! -d steel ]; then
        git clone https://github.com/FStarLang/steel steel
    fi

    cd steel
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["steel_version"]' "$rootPath/.docker/build/config.json" )
    echo Switching to Steel $ref
    git reset --hard $ref
    cd ..
    export_home STEEL "$(pwd)/steel"
}

function fetch_and_make_steel() {
    fetch_steel
    OTHERFLAGS='--admit_smt_queries true' make -C steel -j $threads
}
