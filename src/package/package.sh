#!/bin/bash

set -e

if [[ -z "$OS" ]] ; then
    OS=$(uname)
fi

is_windows=false
if [[ "$OS" = "Windows_NT" ]] ; then
   is_windows=true
fi

if [[ -z "$QD_HOME" ]] ; then
    if ! [[ -f src/rfc_fstar_compiler.ml ]] ; then
        echo QuackyDucky not found
        exit 1
    fi
    # This file MUST be run from the EverParse root directory
    export QD_HOME=$PWD
fi

if $is_windows ; then
    exe=.exe
else
    exe=
fi

platform=$(uname --machine)
if [[ "$OS" = "Linux" ]] && [[ "$platform" = x86_64 ]] && ! [[ -d z3 ]] ; then
    # Download a dependency-free z3
    z3_tagged=z3-4.8.5-linux-clang
    z3_archive=$z3_tagged-$platform.tar.gz
    wget --output-document=$z3_archive https://github.com/tahina-pro/z3/releases/download/$z3_tagged/$z3_archive
    tar xzf $z3_archive
    Z3_DIR="$PWD/z3"
    z3=z3
    echo "Z3_DIR=$Z3_DIR"
    export PATH="$Z3_DIR:$PATH"
else
    z3=z3$exe
    Z3_DIR=$(dirname $(which $z3))
    if [[ -z "$Z3_DIR" ]] ; then
        echo z3 is missing
        exit 1
    fi
fi

if $is_windows ; then
    LIBGMP10_DLL=$(which libgmp-10.dll)
    if [[ -z "$LIBGMP10_DLL" ]] ; then
        echo libgmp-10.dll is missing
        exit 1
    fi
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

if [[ -z "$everparse_version" ]] ; then
    everparse_version=$(cat $QD_HOME/version.txt)
    everparse_last_version=$(git show --no-patch --format=%h $everparse_version || true)
    everparse_commit=$(git show --no-patch --format=%h)
    if [[ $everparse_commit != $everparse_last_version ]] ; then
        everparse_version=$everparse_commit
    fi
fi

fixpath () {
    if $is_windows ; then
        cygpath -m "$1"
    else
        echo "$1"
    fi
}

make_everparse() {
    # Verify if F* and KReMLin are here
    if [[ -z "$FSTAR_HOME" ]] ; then
        git clone https://github.com/FStarLang/FStar &&
        export FSTAR_HOME=$(fixpath $PWD/FStar)
    else
        export FSTAR_HOME=$(fixpath "$FSTAR_HOME")
    fi &&
    if [[ -z "$KREMLIN_HOME" ]] ; then
        git clone https://github.com/FStarLang/kremlin &&
        export KREMLIN_HOME=$(fixpath $PWD/kremlin)
    else
        export KREMLIN_HOME=$(fixpath "$KREMLIN_HOME")
    fi &&

    fstar_commit_id=$(print_component_commit_id "$FSTAR_HOME") &&
    fstar_commit_date_iso=$(print_component_commit_date_iso "$FSTAR_HOME") &&
    fstar_commit_date_hr=$(print_date_utc_of_iso_hr "$fstar_commit_date_iso") &&
    kremlin_commit_id=$(print_component_commit_id "$KREMLIN_HOME") &&
    kremlin_commit_date_iso=$(print_component_commit_date_iso "$KREMLIN_HOME") &&
    kremlin_commit_date_hr=$(print_date_utc_of_iso_hr "$kremlin_commit_date_iso") &&
    z3_version_string=$($Z3_DIR/$z3 --version) &&

    # Rebuild everything
    export OTHERFLAGS='--admit_smt_queries true' &&
    make -C "$FSTAR_HOME" "$@" &&
    make -C "$KREMLIN_HOME" "$@" minimal &&
    make -C "$KREMLIN_HOME/kremlib" "$@" verify-all &&
    make -C "$QD_HOME" "$@" &&

    # Copy dependencies and Z3
    mkdir -p everparse/bin &&
    if $is_windows
    then
        cp -p $LIBGMP10_DLL everparse/bin/ &&
        cp -p $Z3_DIR/*.exe $Z3_DIR/*.dll $Z3_DIR/*.lib everparse/bin/
    else
        cp -p $Z3_DIR/z3 everparse/bin/
    fi &&

    # Copy F*
    cp -p $FSTAR_HOME/bin/fstar.exe everparse/bin/ &&
    mkdir -p everparse/ulib/ &&
    cp -p $FSTAR_HOME/ulib/*.fst everparse/ulib &&
    cp -p $FSTAR_HOME/ulib/*.fsti everparse/ulib &&
    cp -p -r $FSTAR_HOME/ulib/.cache everparse/ulib/ &&

    # Copy KReMLin
    cp -p $KREMLIN_HOME/Kremlin.native everparse/bin/krml$exe &&
    cp -p -r $KREMLIN_HOME/kremlib everparse/ &&
    cp -p -r $KREMLIN_HOME/misc everparse/ &&

    # Copy EverParse
    cp -p $QD_HOME/quackyducky.native everparse/bin/qd$exe &&
    cp -p -r $QD_HOME/src/3d/3d everparse/bin/3d$exe &&
    mkdir -p everparse/src/3d &&
    cp -p -r $QD_HOME/src/lowparse everparse/src/ &&
    if $is_windows ; then
        cp -p -r $QD_HOME/src/package/everparse.cmd everparse/
    else
        cp -p -r $QD_HOME/src/package/everparse.sh everparse/
    fi &&
    cp -p -r $QD_HOME/src/3d/prelude everparse/src/3d/prelude &&
    cp -p -r $QD_HOME/src/3d/.clang-format everparse/src/3d &&
    cp -p -r $QD_HOME/src/3d/copyright.txt everparse/src/3d &&
    if $is_windows ; then cp -p -r $QD_HOME/src/3d/EverParseEndianness_Windows_NT.h everparse/src/3d/ ; fi &&
    cp -p -r $QD_HOME/src/3d/EverParseEndianness.h everparse/src/3d/ &&
    cp -p -r $QD_HOME/src/3d/noheader.txt everparse/src/3d/ &&
    if $is_windows ; then
        cp -p -r $QD_HOME/src/package/README.Windows.pkg everparse/README
    else
        cp -p -r $QD_HOME/src/package/README.pkg everparse/README
    fi &&
    echo "This is EverParse $everparse_version" >> everparse/README &&
    echo "Running with F* $fstar_commit_id ($fstar_commit_date_hr UTC+0000)" >> everparse/README &&
    echo "Running with KReMLin $kremlin_commit_id ($kremlin_commit_date_hr UTC+0000)" >> everparse/README &&
    echo -n "Running with $z3_version_string" >> everparse/README &&

    # Download and copy clang-format
    if $is_windows ; then
        wget --output-document=everparse/bin/clang-format.exe https://prereleases.llvm.org/win-snapshots/clang-format-2663a25f.exe
    fi &&
    
    # licenses
    mkdir -p everparse/licenses &&
    cp -p $FSTAR_HOME/LICENSE everparse/licenses/FStar &&
    cp -p $KREMLIN_HOME/LICENSE everparse/licenses/KReMLin &&
    cp -p $QD_HOME/LICENSE everparse/licenses/EverParse &&
    wget --output-document=everparse/licenses/z3 https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt &&
    if $is_windows ; then
        wget --output-document=everparse/licenses/clang-format https://raw.githubusercontent.com/llvm/llvm-project/master/clang/LICENSE.TXT
    fi &&
    
    # Reset permissions and build the package
    if $is_windows ; then
        chmod a+x everparse/bin/*.exe everparse/bin/*.dll
    fi
}

zip_everparse() {
    set -x
    with_version=$1
    if $is_windows ; then
        ext=.zip
    else
        ext=.tar.gz
    fi
    rm -f everparse$ext &&
    if $is_windows ; then
        zip -r everparse$ext everparse
    else
        time tar cvzf everparse$ext everparse/*
    fi &&
    if $with_version ; then mv everparse$ext everparse_"$everparse_version"_"$OS"_"$platform"$ext ; fi &&
    
    # END
    true
}

print_usage ()
{
  cat <<HELP
USAGE: $0 [OPTIONS]

OPTION:
  -make     Build and place all components in the everparse folder

  -zip      Like -make, but also zip the folder and name with the version

  -zip-noversion      Like -zip, but without the version
HELP
}

case "$1" in
    -zip)
        make_everparse &&
            zip_everparse true
        ;;

    -zip-noversion)
        make_everparse &&
            zip_everparse false
        ;;

    -make)
        make_everparse
        ;;

    *)
        print_usage
        ;;
esac
