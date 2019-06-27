#!/bin/bash

if ! [[ "$OS" = "Windows_NT" ]] ; then
    echo This script is only for Windows binary packages
    exit 1
fi

Z3_DIR=$(dirname $(which z3.exe))
if [[ -z "$Z3_DIR" ]] ; then
    echo z3 is missing
    exit 1
fi

LIBGMP10_DLL=$(which libgmp-10.dll)
if [[ -z "$LIBGMP10_DLL" ]] ; then
    echo libgmp-10.dll is missing
    exit 1
fi

mkdir -p package && 
pushd package && {

    # Verify if F* and KReMLin are here
    if [[ -z "$FSTAR_HOME" ]] ; then
        git clone https://github.com/FStarLang/FStar &&
        export FSTAR_HOME=$(cygpath -m $PWD/FStar)
    fi &&
    if [[ -z "$KREMLIN_HOME" ]] ; then
        git clone https://github.com/FStarLang/kremlin &&
        export KREMLIN_HOME=$(cygpath -m $PWD/kremlin)
    fi &&

    # Rebuild everything
    export OTHERFLAGS='--admit_smt_queries true' &&
    make -C "$FSTAR_HOME" "$@" &&
    make -C "$KREMLIN_HOME" "$@" &&
    make -C .. "$@" &&

    # Copy dependencies and Z3
    rm -rf everparse &&
    mkdir -p everparse/bin &&
    cp $LIBGMP10_DLL everparse/bin/ &&
    cp $Z3_DIR/*.exe $Z3_DIR/*.dll $Z3_DIR/*.lib everparse/bin/ &&

    # Copy F*
    cp $FSTAR_HOME/bin/fstar.exe everparse/bin/ &&
    mkdir -p everparse/ulib/ &&
    cp -p $FSTAR_HOME/ulib/*.fst everparse/ulib &&
    cp -p $FSTAR_HOME/ulib/*.fsti everparse/ulib &&
    cp -p $FSTAR_HOME/ulib/*.checked everparse/ulib &&

    # Copy KReMLin
    cp -p $KREMLIN_HOME/Kremlin.native everparse/bin/krml.exe &&
    cp -p -r $KREMLIN_HOME/include everparse/ &&
    cp -p -r $KREMLIN_HOME/kremlib everparse/ &&
    cp -p -r $KREMLIN_HOME/misc everparse/ &&
    cp -p -r $KREMLIN_HOME/runtime everparse/ &&

    # Copy EverParse
    cp ../quackyducky.native everparse/bin/qd.exe &&
    mkdir -p everparse/src &&
    cp -p -r ../src/lowparse everparse/src/ &&

    # Fetch and extract ninja
    NINJA_URL=$(wget -q -nv -O- https://api.github.com/repos/ninja-build/ninja/releases/latest 2>/dev/null | jq -r '.assets[] | select(.browser_download_url | contains("ninja-win")) | .browser_download_url') &&
    wget -O ninja.zip $NINJA_URL &&
    unzip ninja.zip -d everparse/bin/ &&

    # TODO: licenses

    # Reset permissions and build the package
    chmod a+x everparse/bin/*.exe everparse/bin/*.dll &&
    rm -f everparse.zip &&
    zip -r everparse.zip everparse &&
    
    # END try block
    true

    # BEGIN finally block
    ret=$?
    popd &&
    { [[ $ret -eq 0 ]] || exit $ret ; }
}
