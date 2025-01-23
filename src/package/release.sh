#!/bin/bash

set -e
set -x

DATE=$(which gdate >/dev/null 2>&1 && echo gdate || echo date)

if [[ -z "$EVERPARSE_HOME" ]] ; then
    # This file MUST be run from the EverParse root directory
    export EVERPARSE_HOME=$PWD
fi

# Necessary for gh to authenticate to GitHub
if [[ -z "$GH_TOKEN" ]] ; then
    echo Missing environment variable: GH_TOKEN
    exit 1
fi

if [[ -z "$OS" ]] ; then
    OS=$(uname)
fi

is_windows=false
if [[ "$OS" = "Windows_NT" ]] ; then
   is_windows=true
fi

if [[ -z "$EVERPARSE_RELEASE_ORG" ]] ; then
    EVERPARSE_RELEASE_ORG=project-everest
fi
if [[ -z "$EVERPARSE_RELEASE_REPO" ]] ; then
    EVERPARSE_RELEASE_REPO=everparse
fi
remote="https://${GH_TOKEN}@github.com/${EVERPARSE_RELEASE_ORG}/${EVERPARSE_RELEASE_REPO}.git"

branchname=$(git rev-parse --abbrev-ref HEAD)
git diff --staged --exit-code --ignore-cr-at-eol
git diff --exit-code --ignore-cr-at-eol
git fetch $remote --tags
git pull $remote $branchname --ff-only

FSTAR_SRC_ENVELOPE=fstar-src
FSTAR_SRC_PKG_ROOT=$FSTAR_SRC_ENVELOPE/fstar
if $is_windows ; then
    # On Windows, abort if the F* source package does not exist
    if ! [[ -d "$FSTAR_SRC_PKG_ROOT" ]] ; then
        echo 'Cannot find the F* source package. Please run this script on Linux first.'
        exit 1
    fi
else
    # On Linux, regenerate the F* source package
    # FSTAR_TAG must be explicitly defined to an empty string
    # to prevent the F* build system from mangling the name of
    # the source archive
    FSTAR_TAG= make -C FStar package-src ADMIT=1
    rm -rf "$FSTAR_SRC_PKG_ROOT"
    mkdir -p "$FSTAR_SRC_ENVELOPE"
    tar -x -f FStar/fstar-src.tar.gz -C "$FSTAR_SRC_ENVELOPE/" -z
    # Remove two empty directories that shouldn't be there, and whose names will clash on Windows
    if [[ -d "$FSTAR_SRC_PKG_ROOT/none" ]] ; then rmdir "$FSTAR_SRC_PKG_ROOT/none" ; fi
    if [[ -d "$FSTAR_SRC_PKG_ROOT/None" ]] ; then rmdir "$FSTAR_SRC_PKG_ROOT/None" ; fi
    git add -- "$FSTAR_SRC_PKG_ROOT/"
    if
        ! {
            git diff --staged --exit-code --ignore-cr-at-eol -- "$FSTAR_SRC_PKG_ROOT/" &&
                git diff --exit-code --ignore-cr-at-eol -- "$FSTAR_SRC_PKG_ROOT/"
        }
    then
        git commit -m "Refresh fstar-src"
    fi
fi

everparse_version=$(sed 's!\r!!g' $EVERPARSE_HOME/version.txt)
everparse_last_version=$(git show --no-patch --format=%h $everparse_version || true)
everparse_commit=$(git show --no-patch --format=%h)
if [[ $everparse_commit != $everparse_last_version ]] ; then
    if $is_windows ; then
        echo "This commit does not match the latest release. release.sh must be run on Linux first."
        exit 1
    fi
    everparse_version=$($DATE '+v%Y.%m.%d')
    echo $everparse_version > $EVERPARSE_HOME/version.txt
    git add $EVERPARSE_HOME/version.txt
    git commit -m "Release $everparse_version"
    git tag $everparse_version
fi
export everparse_version
#strip the v
export everparse_nuget_version=${everparse_version:1}

src/package/package.sh -zip -nuget

# push my commit and the tag
git push $remote $branchname $everparse_version

platform=$(uname -m)

if $is_windows ; then
    ext=.zip
else
    ext=.tar.gz
fi

if $is_windows ; then
    exe=.exe
else
    exe=
fi

gh="gh$exe -R ${EVERPARSE_RELEASE_ORG}/${EVERPARSE_RELEASE_REPO}"

function upload_archive () {
    archive="$1"
    if ! $gh release view $everparse_version ; then
        $gh release create --prerelease --generate-notes --target $branchname $everparse_version $archive
    else
        $gh release upload $everparse_version $archive
    fi
}

upload_archive everparse_"$everparse_version"_"$OS"_"$platform""$ext"

if $is_windows ; then
    # Also upload the NuGet package to GitHub releases
    upload_archive EverParse."$everparse_nuget_version".nupkg
fi
