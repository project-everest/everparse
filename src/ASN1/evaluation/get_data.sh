#!/bin/bash
set -e
set -x

unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

function get_dataset () {
    local set=$1
    local target=$2
    local file=$set.zip
    rm -f $file
    wget https://tmp.ht.vc/$file
    mkdir -p $target
    unzip -j $file -d $target
}

# Getting X.509 positive datasets
get_dataset certs data/X509/positive

# Getting X.509 negative datasets
get_dataset negative data/X509/negative

# Getting CRL
get_dataset crls data/CRL/positive
get_dataset negcrls data/CRL/negative
