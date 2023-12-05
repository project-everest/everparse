#!/usr/bin/env bash
set -e
set -x

DOCKER_IMAGE_NAME=cborrustbindingsimg"$$"
echo $DOCKER_IMAGE_NAME

docker build -t $DOCKER_IMAGE_NAME -f rust/rust.Dockerfile .

DOCKER_CONTAINER_NAME=cborrustbindingscont"$$"
docker create --name $DOCKER_CONTAINER_NAME $DOCKER_IMAGE_NAME
docker cp $DOCKER_CONTAINER_NAME:/usr/src/cbor-extern/CBOR_Extern.rs rust/CBOR_Extern.rs
docker rm $DOCKER_CONTAINER_NAME
