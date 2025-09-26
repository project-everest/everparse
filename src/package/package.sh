#!/usr/bin/env bash

set -e
set -x

SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MAKE="$(which gmake >/dev/null 2>&1 && echo gmake || echo make) $EVERPARSE_MAKE_OPTS"
DATE=$(which gdate >/dev/null 2>&1 && echo gdate || echo date)

# We do not read any of these from the environment. This builds a
# package from the current master branches, or the existing checkouts in
# FStar/ and karamel/.
unset FSTAR_EXE
unset FSTAR_HOME
unset KRML_HOME

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

if [[ -z "$EVERPARSE_HOME" ]] ; then
    # This file MUST be run from the EverParse root directory
    export EVERPARSE_HOME=$(fixpath $PWD)
else
    export EVERPARSE_HOME=$(fixpath "$EVERPARSE_HOME")
fi

if $is_windows ; then
    exe=.exe
else
    exe=
fi

download () {
    source="$1"
    target="$2"
    curl -L -o "$target" "$source"
}

platform=$(uname -m)

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
    everparse_version=$(sed 's!\r!!g' $EVERPARSE_HOME/version.txt)
    everparse_last_version=$(git show --no-patch --format=%h $everparse_version || true)
    if everparse_commit=$(git show --no-patch --format=%h) ; then
        if [[ $everparse_commit != $everparse_last_version ]] ; then
            everparse_version=$everparse_commit
        fi
    fi
fi

make_everparse() {
    #!!!!! NB: We admit queries when building F*, krml, and everparse!
    export OTHERFLAGS='--admit_smt_queries true'
    #!!!!!

    cp0=$(which gcp >/dev/null 2>&1 && echo gcp || echo cp)
    cp="$cp0 --preserve=mode,timestamps"

    ## Setup F*. We need to locate a package, either it's already
    # there or we try to build one from the repo.

    FSTAR_PKG_ENVELOPE=__fstar-install
    # The package extracts into a fstar directory, and everything
    # is under there.
    FSTAR_PKG_ROOT="$FSTAR_PKG_ENVELOPE/fstar"
    FSTAR_SRC_PKG_ROOT=fstar-src/fstar
    if ! [[ -d $FSTAR_PKG_ROOT ]] ; then
        if [[ -d $FSTAR_SRC_PKG_ROOT ]] ; then
            # build from a source package
            dune_sandbox_opt=
            if $is_windows ; then
		# Dune crashes with "cannot delete sandbox." This fix comes
		# from https://github.com/ocaml/dune/issues/8228#issuecomment-1642104172
                dune_sandbox_opt=DUNE_CONFIG__BACKGROUND_SANDBOXES=disabled
            fi
            env $dune_sandbox_opt $MAKE -C $FSTAR_SRC_PKG_ROOT "$@" ADMIT=1 package
            $cp $FSTAR_SRC_PKG_ROOT/fstar.tar.gz . || $cp $FSTAR_SRC_PKG_ROOT/fstar.zip .
        else
            if ! [ -f fstar.tar.gz ] && ! [ -f fstar.zip ]; then
                # build a binary package from a full F* clone
                if ! [ -d FStar ]; then
                    git clone https://github.com/FStarLang/FStar --depth 1
                fi
                $MAKE -C FStar "$@" ADMIT=1
                $MAKE -C FStar "$@" FSTAR_TAG= package
                $cp FStar/fstar.tar.gz . || $cp FStar/fstar.zip .
            fi
        fi
	{
            mkdir -p "$FSTAR_PKG_ENVELOPE"
            if [ -f fstar.tar.gz ]; then
                FSTAR_PKG=$(realpath fstar.tar.gz)
                tar xzf $FSTAR_PKG -C "$FSTAR_PKG_ENVELOPE"
            elif [ -f fstar.zip ]; then
                FSTAR_PKG=$(realpath fstar.zip)
                pushd "$FSTAR_PKG_ENVELOPE"
                unzip -q "$FSTAR_PKG"
                popd
            else
                echo "unexpected, no package?" >&2
                exit 1
            fi
	}
    fi

    export FSTAR_EXE=$(realpath $FSTAR_PKG_ROOT/bin/fstar.exe)
    export FSTAR_EXE=$(fixpath "$FSTAR_EXE")
    fstar_commit_id=$("$FSTAR_EXE" --version | grep '^commit=' | sed 's!^.*=!!')
    fstar_commit_date_hr=$("$FSTAR_EXE" --version | grep '^date=' | sed 's!^.*=!!')

    ## Setup krml

    if ! [ -d karamel ]; then
      git clone https://github.com/FStarLang/karamel --depth 1
    fi
    export KRML_HOME=$(fixpath $PWD/karamel)
    $MAKE -C "$KRML_HOME" "$@"
    if karamel_commit_id=$(print_component_commit_id "$KRML_HOME") ; then
        karamel_commit_date_iso=$(print_component_commit_date_iso "$KRML_HOME")
        karamel_commit_date_hr=$(print_date_utc_of_iso_hr "$karamel_commit_date_iso")" UTC+0000"
    fi

    # Install ocaml-sha if not found
    if ! ocamlfind query sha ; then
        opam install --yes sha
    fi

    # Rebuild EverParse
    NO_PULSE=1 $MAKE -C "$EVERPARSE_HOME" "$@" package-subset

    # Copy dependencies
    mkdir -p everparse/bin
    if $is_windows
    then
        $cp $LIBGMP10_DLL everparse/bin/
        # copy libffi-6 in all cases (ocaml-sha also seems to need it)
        $cp $(which libffi-6.dll) everparse/bin/
    else
        {
            # Locate libffi
            {
                # Debian:
                libffi=$(dpkg -L libffi8 | grep '/libffi.so.8$' | head -n 1)
                [[ -n "$libffi" ]]
            } || {
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
    fi

    # Copy F*
    cp $FSTAR_PKG_ROOT/bin/* everparse/bin/
    mkdir -p everparse/lib/fstar/
    cp $FSTAR_PKG_ROOT/lib/fstar/fstar.include everparse/lib/fstar/
    cp -r $FSTAR_PKG_ROOT/lib/fstar/ulib everparse/lib/fstar/ulib
    cp -r $FSTAR_PKG_ROOT/lib/fstar/ulib.checked everparse/lib/fstar/ulib.checked
    cp -r $FSTAR_PKG_ROOT/lib/fstar/z3-4.13.3 everparse/lib/fstar/

    # Copy KaRaMeL
    $cp -L $KRML_HOME/krml everparse/bin/krml$exe
    $cp -r $KRML_HOME/krmllib everparse/
    $cp -r $KRML_HOME/include everparse/
    $cp -r $KRML_HOME/misc everparse/

    # Copy EverParse
    $cp $EVERPARSE_HOME/bin/qd.exe everparse/bin/qd.exe
    $cp -r $EVERPARSE_HOME/bin/3d.exe everparse/bin/3d.exe
    mkdir -p everparse/src/3d
    $cp -r $EVERPARSE_HOME/src/lowparse everparse/src/
    if $is_windows ; then
        $cp -r $EVERPARSE_HOME/src/package/everparse.cmd everparse/
    else
        $cp -r $EVERPARSE_HOME/src/package/everparse.sh everparse/
    fi
    $cp -r $EVERPARSE_HOME/src/3d/prelude everparse/src/3d/prelude
    $cp -r $EVERPARSE_HOME/src/3d/.clang-format everparse/src/3d
    $cp -r $EVERPARSE_HOME/src/3d/copyright.txt everparse/src/3d
    if $is_windows ; then $cp -r $EVERPARSE_HOME/src/3d/EverParseEndianness_Windows_NT.h everparse/src/3d/ ; fi
    $cp -r $EVERPARSE_HOME/src/3d/EverParseEndianness.h everparse/src/3d/
    $cp -r $EVERPARSE_HOME/src/3d/noheader.txt everparse/src/3d/
    if $is_windows ; then
        $cp -r $EVERPARSE_HOME/src/package/README.Windows.pkg everparse/README
    else
        $cp -r $EVERPARSE_HOME/src/package/README.pkg everparse/README
    fi
    echo "This is EverParse $everparse_version" >> everparse/README
    echo "Running with F* $fstar_commit_id ($fstar_commit_date_hr)" >> everparse/README
    echo "Running with KaRaMeL $karamel_commit_id ($karamel_commit_date_hr)" >> everparse/README

    # Download and copy clang-format
    if $is_windows ; then
        download https://prereleases.llvm.org/win-snapshots/clang-format-2663a25f.exe everparse/bin/clang-format.exe
    fi

    # Set executable permissions on EXE and DLL on Windows
    if $is_windows ; then
        chmod a+x everparse/bin/*.exe everparse/bin/*.dll everparse/lib/fstar/z3-*/bin/*.exe everparse/lib/fstar/z3-*/bin/*.dll
    fi

    # licenses
    mkdir -p everparse/licenses
    $cp $FSTAR_PKG_ROOT/LICENSE everparse/licenses/FStar
    $cp $KRML_HOME/LICENSE-APACHE everparse/licenses/KaRaMeL-Apache
    $cp $KRML_HOME/LICENSE-MIT everparse/licenses/KaRaMeL-MIT
    $cp $EVERPARSE_HOME/LICENSE everparse/licenses/EverParse
    download https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt everparse/licenses/z3
    download https://raw.githubusercontent.com/libffi/libffi/master/LICENSE everparse/licenses/libffi6
    if $is_windows ; then
        download https://raw.githubusercontent.com/llvm/llvm-project/main/clang/LICENSE.TXT everparse/licenses/clang-format
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
        download https://raw.githubusercontent.com/github/choosealicense.com/refs/heads/gh-pages/_licenses/lgpl-3.0.txt everparse/licenses/gnulgplv3
        cat everparse/licenses/gnulgplv3 >> everparse/licenses/libgmp10
        rm everparse/licenses/gnulgplv3
        download https://raw.githubusercontent.com/github/choosealicense.com/refs/heads/gh-pages/_licenses/gpl-3.0.txt everparse/licenses/gnugplv3
        cat everparse/licenses/gnugplv3 >> everparse/licenses/libgmp10
        rm everparse/licenses/gnugplv3
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
}

nuget_everparse() {
    with_version=$1
    if $is_windows ; then
        # Create the nuget package

        # We are in the top-level everparse root

        nuget_base=nuget_package

        if [[ -d $nuget_base ]] ; then
            echo "Nuget base directory $nuget_base already exists, please make way"
            exit 1
        fi

        mkdir -p $nuget_base

        # Set up the directory structure for the nuget package
        
        # Copy README to nuget top-level
        cp everparse/README $nuget_base
        # Copy the manifest file to nuget top-level
        cp src/package/EverParse.nuspec $nuget_base
        # Create the content directory, and copy all the files there

        #NOTE: this is creating the content dir with win- prefix,
        #      since we are in if $is_windows
        #      if someday we do it for linux also, change accordingly
        
        content_dir=$nuget_base/content/win-$platform
        mkdir -p $content_dir
        cp -R everparse/* $content_dir

        # Download nuget.exe to create the package
        nuget_exe_url=https://dist.nuget.org/win-x86-commandline/latest/nuget.exe
        download $nuget_exe_url nuget.exe
        chmod a+x nuget.exe

        # Run the pack command
        pushd $nuget_base


	if [[ -z "$everparse_nuget_version" ]] ; then
		everparse_nuget_version=1.0.0
	fi
	# NoDefaultExcludes for .clang-format file that nuget pack excludes
        ../nuget.exe pack -OutputFileNamesWithoutVersion -NoDefaultExcludes -Version $everparse_nuget_version ./EverParse.nuspec
        cp EverParse.nupkg ..
        if $with_version ; then mv ../EverParse.nupkg ../EverParse."$everparse_nuget_version".nupkg ; fi
        popd
    else
        echo "We are not on Windows, skipping nuget package"
    fi
    # Not doing any cleanup in the spirit of existing package

    # TODO: push this package?
    
    # END
    true
}

print_usage ()
{
  cat <<HELP
USAGE: $0 [OPTIONS]

By default, this script builds and places all components in the everparse folder

OPTION:
  -zip      Also zip on Windows, tar.gz on Linux, the folder and name with the version

  -zip-noversion
            Like -zip, but without the version. Incompatible with -zip

  -nuget    Also nuget the folder and name with the version.
            Does nothing on non-Windows platforms.

  -nuget-noversion
            Like -nuget, but without the version.
            Incompatible with -nuget

  --        Ends the list of script-specific options. Beyond that option,
            passes other arguments to 'make'
HELP
}

zip_everparse_cmd=
nuget_everparse_cmd=
process_args=true

while [[ -n "$1" ]] && $process_args ; do
    case "$1" in
        -zip)
            shift
            if [[ -n "$zip_everparse_cmd" ]] ; then
               echo "ERROR: only one of -zip or -zip-noversion can be given"
               print_usage
               exit 1
            fi
            zip_everparse_cmd="zip_everparse true"
            ;;

        -zip-noversion)
            shift
            if [[ -n "$zip_everparse_cmd" ]] ; then
               echo "ERROR: only one of -zip or -zip-noversion can be given"
               print_usage
               exit 1
            fi
            zip_everparse_cmd="zip_everparse false"
            ;;

        -nuget)
            shift
            if [[ -n "$nuget_everparse_cmd" ]] ; then
               echo "ERROR: only one of -nuget or -nuget-noversion can be given"
               print_usage
               exit 1
            fi
            nuget_everparse_cmd="nuget_everparse true"
            ;;

        -nuget-noversion)
            shift
            if [[ -n "$nuget_everparse_cmd" ]] ; then
               echo "ERROR: only one of -nuget or -nuget-noversion can be given"
               print_usage
               exit 1
            fi
            nuget_everparse_cmd="nuget_everparse false"
            ;;

        -help)
            shift
            print_usage
            exit 0
            ;;

        --)
            shift
            process_args=false
            ;;

        *)
            print_usage
            exit 1
            ;;
    esac
done


make_everparse "$@"
if [[ -n "$zip_everparse_cmd" ]] ; then $zip_everparse_cmd ; fi
if [[ -n "$nuget_everparse_cmd" ]] ; then $nuget_everparse_cmd ; fi
true
