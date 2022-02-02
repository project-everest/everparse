#!/usr/bin/env bash

set -e
set -x

SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MAKE="$(which gmake >/dev/null 2>&1 && echo gmake || echo make) $EVERPARSE_MAKE_OPTS"
DATE=$(which gdate >/dev/null 2>&1 && echo gdate || echo date)


if [[ -z "$OS" ]] ; then
    OS=$(uname)
fi

is_windows=false
if [[ "$OS" = "Windows_NT" ]] ; then
   is_windows=true
fi

fixpath () {
    if $is_windows ; then
        cygpath -m "$1"
    else
        echo "$1"
    fi
}

if [[ -z "$QD_HOME" ]] ; then
    # This file MUST be run from the EverParse root directory
    export QD_HOME=$(fixpath $PWD)
else
    export QD_HOME=$(fixpath "$QD_HOME")
fi

if $is_windows ; then
    exe=.exe
else
    exe=
fi

platform=$(uname -m)
z3=z3$exe
if ! Z3_DIR=$(dirname $(which $z3)) ; then
    if [[ -d z3 ]] ; then
        true
    elif $is_windows ; then
        z3_tagged=Z3-4.8.5
        z3_archive=z3-4.8.5-x64-win.zip
        wget --output-document=$z3_archive https://github.com/Z3Prover/z3/releases/download/$z3_tagged/$z3_archive
        unzip $z3_archive
        mv z3-4.8.5-x64-win z3
        chmod +x z3/bin/z3.exe
        if [[ -f z3/bin/*.dll ]] ; then chmod +x z3/bin/*.dll ; fi
        if [[ -f z3/lib/*.dll ]] ; then chmod +x z3/lib/*.dll ; fi
    elif [[ "$OS" = "Linux" ]] && [[ "$platform" = x86_64 ]] ; then
        # Download a dependency-free z3
        z3_tagged=z3-4.8.5-linux-clang
        z3_archive=$z3_tagged-$platform.tar.gz
        wget --output-document=$z3_archive https://github.com/tahina-pro/z3/releases/download/$z3_tagged/$z3_archive
        tar xzf $z3_archive
    else
        echo "z3 4.8.5 is missing, please add it to your PATH"
        exit 1
    fi
    Z3_DIR="$PWD/z3/bin"
    export PATH="$Z3_DIR:$PATH"
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
    $DATE --utc --date="$1" '+%Y-%m-%d %H:%M:%S'
}

if [[ -z "$everparse_version" ]] ; then
    everparse_version=$(cat $QD_HOME/version.txt)
    everparse_last_version=$(git show --no-patch --format=%h $everparse_version || true)
    if everparse_commit=$(git show --no-patch --format=%h) ; then
        if [[ $everparse_commit != $everparse_last_version ]] ; then
            everparse_version=$everparse_commit
        fi
    fi
fi

make_everparse() {
    # Verify if F* and KReMLin are here
    cp0=$(which gcp >/dev/null 2>&1 && echo gcp || echo cp)
    cp="$cp0 --preserve=mode,timestamps"
    if [[ -z "$FSTAR_HOME" ]] ; then
        [[ -d FStar ]] || git clone https://github.com/FStarLang/FStar
        export FSTAR_HOME=$(fixpath $PWD/FStar)
    else
        export FSTAR_HOME=$(fixpath "$FSTAR_HOME")
    fi
    if [[ -z "$KREMLIN_HOME" ]] ; then
        { [[ -d kremlin ]] || git clone https://github.com/FStarLang/kremlin ; }
        export KREMLIN_HOME=$(fixpath $PWD/kremlin)
    else
        export KREMLIN_HOME=$(fixpath "$KREMLIN_HOME")
    fi

    if fstar_commit_id=$(print_component_commit_id "$FSTAR_HOME") ; then
        fstar_commit_date_iso=$(print_component_commit_date_iso "$FSTAR_HOME")
        fstar_commit_date_hr=$(print_date_utc_of_iso_hr "$fstar_commit_date_iso")" UTC+0000"
    fi
    if kremlin_commit_id=$(print_component_commit_id "$KREMLIN_HOME") ; then
        kremlin_commit_date_iso=$(print_component_commit_date_iso "$KREMLIN_HOME")
        kremlin_commit_date_hr=$(print_date_utc_of_iso_hr "$kremlin_commit_date_iso")" UTC+0000"
    fi
    z3_version_string=$($Z3_DIR/$z3 --version)

    # Rebuild F* and kremlin
    export OTHERFLAGS='--admit_smt_queries true'
    $MAKE -C "$FSTAR_HOME" "$@"
    if [[ -z "$fstar_commit_id" ]] ; then
        fstar_commit_id=$("$FSTAR_HOME/bin/fstar.exe" --version | grep '^commit=' | sed 's!^.*=!!')
        fstar_commit_date_hr=$("$FSTAR_HOME/bin/fstar.exe" --version | grep '^date=' | sed 's!^.*=!!')
    fi
    $MAKE -C "$KREMLIN_HOME" "$@" minimal
    $MAKE -C "$KREMLIN_HOME/kremlib" "$@" verify-all

    # Build the hacl-star package if not available
    if [[ -z "$NO_EVERCRYPT" ]] && ! ocamlfind query hacl-star ; then
        mkdir -p ocaml-packages
        export OCAMLFIND_DESTDIR=$(fixpath "$PWD/ocaml-packages")
        if $is_windows ; then
            export OCAMLPATH="$OCAMLFIND_DESTDIR;$OCAMLPATH"
        else
            export OCAMLPATH="$OCAMLFIND_DESTDIR:$OCAMLPATH"
        fi
        if [[ -z $HACL_HOME ]] ; then
            [[ -d hacl-star ]] || git clone https://github.com/project-everest/hacl-star
            HACL_HOME=$(fixpath $PWD/hacl-star)
        else
            HACL_HOME=$(fixpath "$HACL_HOME")
        fi
        if ! ocamlfind query hacl-star-raw ; then
            (cd $HACL_HOME/dist/gcc-compatible ; ./configure --disable-bzero)
            $MAKE -C $HACL_HOME/dist/gcc-compatible "$@"
            $MAKE -C $HACL_HOME/dist/gcc-compatible install-hacl-star-raw
        fi
        if ! ocamlfind query hacl-star ; then
            (cd $HACL_HOME/bindings/ocaml ; dune build ; dune install)
        fi
    fi

    # Install ocaml-sha if EverCrypt is disabled
    if [[ -n "$NO_EVERCRYPT" ]] && ! ocamlfind query sha ; then
        opam install --yes sha
    fi

    # Rebuild EverParse
    $MAKE -C "$QD_HOME" "$@"

    # Copy dependencies and Z3
    mkdir -p everparse/bin
    if $is_windows
    then
        $cp $LIBGMP10_DLL everparse/bin/
        $cp $Z3_DIR/*.exe everparse/bin/
        if [[ -f $Z3_DIR/*.dll ]] ; then $cp $Z3_DIR/*.dll everparse/bin/ ; fi
        if [[ -f $Z3_DIR/../lib/*.dll ]] ; then cp $Z3_DIR/../lib/*.dll everparse/bin/ ; fi
        if [[ -z "$NO_EVERCRYPT" ]] ; then
            for f in $(ocamlfind printconf destdir)/stublibs $($SED 's![\t\v\f \r\n]*$!!' < $(ocamlfind printconf ldconf)) $(ocamlfind query hacl-star-raw) ; do
                libevercrypt_dll=$f/libevercrypt.dll
                if [[ -f $libevercrypt_dll ]] ; then
                    break
                fi
                unset libevercrypt_dll
            done
            [[ -n $libevercrypt_dll ]]
            $cp $libevercrypt_dll everparse/bin/
        fi
        # copy libffi-6 in all cases (ocaml-sha also seems to need it)
        $cp $(which libffi-6.dll) everparse/bin/
    else
        if [[ -z "$NO_EVERCRYPT" ]] ; then
            for f in $(ocamlfind printconf destdir)/stublibs $(cat $(ocamlfind printconf ldconf)) $(ocamlfind query hacl-star-raw) ; do
                libevercrypt_so=$f/libevercrypt.so
                if [[ -f $libevercrypt_so ]] ; then
                    break
                fi
                unset libevercrypt_so
            done
            [[ -n $libevercrypt_so ]]
            $cp $libevercrypt_so everparse/bin/
        fi
        {
            # Locate libffi
            {
                # Debian:
                libffi=$(dpkg -L libffi7 | grep '/libffi.so.7$' | head -n 1)
                [[ -n "$libffi" ]]
            } || {
                # Debian (older):
                libffi=$(dpkg -L libffi6 | grep '/libffi.so.6$' | head -n 1)
                [[ -n "$libffi" ]]
            } || {
                # Arch:
                libffi=$(pacman -Qql libffi | grep '/libffi.so.7$' | head -n 1)
                [[ -n "$libffi" ]]
            } || {
                # Fedora:
                libffi=$(rpm --query libffi --list | grep '/libffi.so.6$' | head -n 1)
                [[ -n "$libffi" ]]
            } || {
                # Default: not found
                echo libffi not found
                exit 1
            }
            $cp $libffi everparse/bin/
        }
        $cp $Z3_DIR/z3 everparse/bin/
    fi

    # Copy F*
    $cp $FSTAR_HOME/bin/fstar.exe everparse/bin/
    $cp -r $FSTAR_HOME/bin/fstar-tactics-lib everparse/bin/
    $cp -r $FSTAR_HOME/ulib everparse/

    # Copy KReMLin
    $cp $KREMLIN_HOME/Kremlin.native everparse/bin/krml$exe
    $cp -r $KREMLIN_HOME/kremlib everparse/
    $cp -r $KREMLIN_HOME/include everparse/
    $cp -r $KREMLIN_HOME/misc everparse/

    # Copy EverParse
    $cp $QD_HOME/bin/qd.exe everparse/bin/qd.exe
    $cp -r $QD_HOME/bin/3d.exe everparse/bin/3d.exe
    mkdir -p everparse/src/3d
    $cp -r $QD_HOME/src/lowparse everparse/src/
    if $is_windows ; then
        $cp -r $QD_HOME/src/package/everparse.cmd everparse/
    else
        $cp -r $QD_HOME/src/package/everparse.sh everparse/
    fi
    $cp -r $QD_HOME/src/3d/prelude everparse/src/3d/prelude
    $cp -r $QD_HOME/src/3d/.clang-format everparse/src/3d
    $cp -r $QD_HOME/src/3d/copyright.txt everparse/src/3d
    if $is_windows ; then $cp -r $QD_HOME/src/3d/EverParseEndianness_Windows_NT.h everparse/src/3d/ ; fi
    $cp -r $QD_HOME/src/3d/EverParseEndianness.h everparse/src/3d/
    $cp -r $QD_HOME/src/3d/noheader.txt everparse/src/3d/
    if $is_windows ; then
        $cp -r $QD_HOME/src/package/README.Windows.pkg everparse/README
    else
        $cp -r $QD_HOME/src/package/README.pkg everparse/README
    fi
    echo "This is EverParse $everparse_version" >> everparse/README
    echo "Running with F* $fstar_commit_id ($fstar_commit_date_hr)" >> everparse/README
    echo "Running with KReMLin $kremlin_commit_id ($kremlin_commit_date_hr)" >> everparse/README
    echo -n "Running with $z3_version_string" >> everparse/README

    # Download and copy clang-format
    if $is_windows ; then
        wget --output-document=everparse/bin/clang-format.exe https://prereleases.llvm.org/win-snapshots/clang-format-2663a25f.exe
    fi
    
    # licenses
    mkdir -p everparse/licenses
    $cp $FSTAR_HOME/LICENSE everparse/licenses/FStar
    $cp $KREMLIN_HOME/LICENSE everparse/licenses/KReMLin
    $cp $QD_HOME/LICENSE everparse/licenses/EverParse
    wget --output-document=everparse/licenses/z3 https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt
    if [[ -z "$NO_EVERCRYPT" ]] ; then
        wget --output-document=everparse/licenses/EverCrypt https://raw.githubusercontent.com/project-everest/hacl-star/master/LICENSE
    fi
    wget --output-document=everparse/licenses/libffi6 https://raw.githubusercontent.com/libffi/libffi/master/LICENSE
    if $is_windows ; then
        wget --output-document=everparse/licenses/clang-format https://raw.githubusercontent.com/llvm/llvm-project/main/clang/LICENSE.TXT
    fi
    if $is_windows ; then
        {
            cat >everparse/licenses/libgmp10 <<EOF
libgmp10 (the GNU Multiple Precision Arithmetic Library,
Copyright 2000 - 2020 The GNU Project - Free Software Foundation)
is licensed under the GNU LGPL v3, a copy of which follows;
this EverParse binary package combines EverParse with libgmp10
in accordance with Section 4.d.1 of the GNU LGPL v3.

EOF
        }
        wget --output-document=everparse/licenses/gnulgplv3 https://www.gnu.org/licenses/lgpl-3.0.txt
        cat everparse/licenses/gnulgplv3 >> everparse/licenses/libgmp10
        rm everparse/licenses/gnulgplv3
        wget --output-document=everparse/licenses/gnugplv3 https://www.gnu.org/licenses/gpl-3.0.txt
        cat everparse/licenses/gnugplv3 >> everparse/licenses/libgmp10
        rm everparse/licenses/gnugplv3
    fi
    
    # Reset permissions and build the package
    if $is_windows ; then
        chmod a+x everparse/bin/*.exe everparse/bin/*.dll
    fi
}

zip_everparse() {
    with_version=$1
    if $is_windows ; then
        ext=.zip
    else
        ext=.tar.gz
    fi
    rm -f everparse$ext
    if $is_windows ; then
        zip -r everparse$ext everparse
    else
        time tar cvzf everparse$ext everparse/*
    fi
    if $with_version ; then mv everparse$ext everparse_"$everparse_version"_"$OS"_"$platform"$ext ; fi
    
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
        shift
        make_everparse "$@"
            zip_everparse true
        ;;

    -zip-noversion)
        shift
        make_everparse "$@"
            zip_everparse false
        ;;

    -make)
        shift
        make_everparse "$@"
        ;;

    *)
        print_usage
        ;;
esac
