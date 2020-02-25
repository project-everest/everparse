#!/bin/bash

set -e

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

print_component_commit_id() {
    ( cd $1 && git show --no-patch --format=%h )
}

print_component_commit_date_iso() {
    ( cd $1 && git show --no-patch --format=%ad --date=iso )
}

print_date_utc_of_iso_hr() {
    date --utc --date="$1" '+%Y-%m-%d %H:%M:%S'
}

everparse_version=$(cat $QD_HOME/version.txt)
everparse_last_version=$(git show --no-patch --format=%h $everparse_version || true)
everparse_commit=$(git show --no-patch --format=%h)
if [[ $everparse_commit != $everparse_last_version ]] ; then
    everparse_version=$everparse_commit
fi
platform=$(uname --machine)

    # Verify if F* and KReMLin are here
    if [[ -z "$FSTAR_HOME" ]] ; then
        git clone --branch nik_rename_let https://github.com/FStarLang/FStar &&
        export FSTAR_HOME=$(cygpath -m $PWD/FStar)
    else
        export FSTAR_HOME=$(cygpath -m "$FSTAR_HOME")
    fi &&
    if [[ -z "$KREMLIN_HOME" ]] ; then
        git clone https://github.com/FStarLang/kremlin &&
        export KREMLIN_HOME=$(cygpath -m $PWD/kremlin)
    else
        export KREMLIN_HOME=$(cygpath -m "$KREMLIN_HOME")
    fi &&

    fstar_commit_id=$(print_component_commit_id "$FSTAR_HOME") &&
    fstar_commit_date_iso=$(print_component_commit_date_iso "$FSTAR_HOME") &&
    fstar_commit_date_hr=$(print_date_utc_of_iso_hr "$fstar_commit_date_iso") &&
    kremlin_commit_id=$(print_component_commit_id "$KREMLIN_HOME") &&
    kremlin_commit_date_iso=$(print_component_commit_date_iso "$KREMLIN_HOME") &&
    kremlin_commit_date_hr=$(print_date_utc_of_iso_hr "$kremlin_commit_date_iso") &&
    z3_version_string=$($Z3_DIR/z3.exe --version) &&

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
    cp -p -r $FSTAR_HOME/ulib/.cache everparse/ulib/ &&

    # Copy KReMLin
    cp -p $KREMLIN_HOME/Kremlin.native everparse/bin/krml.exe &&
    cp -p -r $KREMLIN_HOME/kremlib everparse/ &&
    cp -p -r $KREMLIN_HOME/misc everparse/ &&

    # Copy EverParse
    cp $QD_HOME/quackyducky.native everparse/bin/qd.exe &&
    cp -p -r $QD_HOME/src/3d/3d everparse/bin/3d.exe &&
    mkdir -p everparse/src &&
    cp -p -r $QD_HOME/src/lowparse everparse/src/ &&
    cp -p -r $QD_HOME/src/package/everparse.bat everparse/ &&
    cp -p -r $QD_HOME/src/3d/prelude everparse/src/3d &&
    cp -p -r $QD_HOME/src/3d/.clang-format everparse/src/3d &&
    mkdir -p everparse/include/ &&
    cp -p -r $QD_HOME/src/package/EverParseEndianness_$OS.h everparse/include/EverParseEndianness.h &&
    cp -p -r $QD_HOME/src/3d/noheader.txt everparse/src/3d/ &&
    cp -p -r $QD_HOME/src/package/README.pkg everparse/README &&
    echo "This is EverParse $everparse_version" >> everparse/README &&
    echo "Running with F* $fstar_commit_id ($fstar_commit_date_hr UTC+0000)" >> everparse/README &&
    echo "Running with KReMLin $kremlin_commit_id ($kremlin_commit_date_hr UTC+0000)" >> everparse/README &&
    echo -n "Running with $z3_version_string" >> everparse/README &&

    # licenses
    mkdir -p everparse/licenses &&
    cp -p $FSTAR_HOME/LICENSE everparse/licenses/FStar &&
    cp -p $KREMLIN_HOME/LICENSE everparse/licenses/KReMLin &&
    cp -p $QD_HOME/LICENSE everparse/licenses/EverParse &&
    wget --output-document=everparse/licenses/z3 https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt &&
    
    # Reset permissions and build the package
    chmod a+x everparse/bin/*.exe everparse/bin/*.dll &&
    rm -f everparse.zip &&
    zip -r everparse.zip everparse &&
    mv everparse.zip everparse_"$everparse_version"_"$OS"_"$platform".zip &&
    
    # END
    true
