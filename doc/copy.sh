#!/usr/bin/env bash

set -x

if [[ $1 == "" ]]; then
  echo "USAGE: $0 DST where DST is the directory in which files have to be copied"
  exit 1
fi

destpath=$(realpath "$1")
cd $(dirname $0)

if which gsed &>/dev/null; then
  SED=gsed
else
  SED=sed
fi

if which gfind &>/dev/null; then
  FIND=gfind
else
  FIND=find
fi

# make html # assume this is already done, see in the Makefile, 3d-ci depends on html
cp -R _build/html/* "$destpath"

cd "$destpath"
rm -rf static && mv _static static
rm -rf images && if [[ -d _images ]] ; then mv _images images ; fi
$FIND . -type f | grep -v '\.git' | xargs $SED -i 's/_static/static/g'
$FIND . -type f | grep -v '\.git' | xargs $SED -i 's/_images/images/g'
$FIND . -type f | grep -v '\.git' | xargs $SED -i 's/_sources/sources/g'
