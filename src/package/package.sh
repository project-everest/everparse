#!/bin/bash

if ! [[ "$OS" = "Windows_NT" ]] ; then
    echo This script is only for Windows binary packages
    exit 1
fi

if [[ -z "$QD_HOME" ]] ; then
    if ! [[ -f src/rfc_fstar_compiler.ml ]] ; then
        echo QuackyDucky not found
        exit 1
    fi
    # This file MUST be run from the EverParse root directory
    export QD_HOME=$PWD
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

if [[ -d everparse ]] ; then
    echo everparse/ is already there, please make way
    exit 1
fi

    # Verify if F* and KReMLin are here
    if [[ -z "$FSTAR_HOME" ]] ; then
        git clone --branch taramana_dep_ninja https://github.com/FStarLang/FStar &&
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
    make -C "$QD_HOME" "$@" &&

    # Copy dependencies and Z3
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
    cp $QD_HOME/quackyducky.native everparse/bin/qd.exe &&
    mkdir -p everparse/src &&
    cp -p -r $QD_HOME/src/lowparse everparse/src/ &&
    mkdir -p everparse/src/package &&
    cp -p -r $QD_HOME/src/package/build.ninja everparse/src/package &&
    cp -p -r $QD_HOME/src/package/everparse.bat everparse/ &&

    # Fetch and extract ninja
    NINJA_URL=$(wget -q -nv -O- https://api.github.com/repos/ninja-build/ninja/releases/latest 2>/dev/null | jq -r '.assets[] | select(.browser_download_url | contains("ninja-win")) | .browser_download_url') &&
    wget -O ninja.zip $NINJA_URL &&
    unzip ninja.zip -d everparse/bin/ &&

    # TODO: licenses

    # Reset permissions and build the package
    chmod a+x everparse/bin/*.exe everparse/bin/*.dll &&
    rm -f everparse.zip &&
    zip -r everparse.zip everparse &&
    
    # END
    true
