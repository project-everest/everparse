#!/bin/bash

# Build c3d and extract the .so
# (for now useless without clang as patched by package/Dockerfile)

set -e
set -x
docker build -t build-c3d -f package/Dockerfile .
docker create --name=build-c3d build-c3d
# The plugin is useful for those who already have clang installed and wish to
# run it as part of a global compilation run; the executable is likely more
# useful.
# docker cp build-c3d:/home/test/out/src/C3d.so .
docker cp build-c3d:/home/test/out/driver/clang-c3d .
docker rm build-c3d
