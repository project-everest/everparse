#!/bin/bash

# Build c3d and extract the .so
# (for now useless without clang as patched by package/Dockerfile)

set -e
set -x

build_tag=$1
if [[ -z $build_tag ]] ; then
    build_image=build-c3d
else
    build_image=build-c3d:$build_tag
fi
docker build -t $build_image -f package/Dockerfile .
docker create --name=build-c3d-$build_tag $build_image
# The plugin is useful for those who already have clang installed and wish to
# run it as part of a global compilation run; the executable is likely more
# useful.
# docker cp build-c3d-$build_tag:/home/test/out/src/C3d.so .
docker cp build-c3d-$build_tag:/home/test/out/driver/clang-c3d .
docker rm build-c3d-$build_tag

# Test 
./clang-c3d tests/basic0.h
