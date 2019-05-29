#!/bin/bash

set -e

dest_dir=$1

if ! [[ -d $dest_dir ]]; then
  echo "First argument ($dest_dir) is not a directory"
  echo "Usage: $0 DEST-DIR [NUM-BLOCKS]"
  exit 1
fi

if ! which jq &>/dev/null; then
  echo "jq not found, please install jq"
  exit 1
fi

start_block=100000

if [[ $2 == "" ]]; then
  num_blocks=10000
else
  num_blocks=$2
fi

for i in $(seq $start_block $((start_block+num_blocks))); do
  hash=$(wget -q https://blockchain.info/block-height/$i?format=json -O - | jq '.blocks[0].hash' | tr -d '"')
  echo "Block $i has hash $hash"
  wget -q https://blockchain.info/block/$hash?format=hex -O $dest_dir/block$i
done
