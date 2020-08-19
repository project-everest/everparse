#!/bin/bash

# Build c3d and extract the .so
# (for now useless without clang as patched by package/Dockerfile)

set -e
set -x
docker build -t build-c3d -f package/Dockerfile .
docker create --name=build-c3d build-c3d
docker cp build-c3d:/home/test/out/C3d.so .
docker rm build-c3d
