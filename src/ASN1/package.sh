#!/bin/bash
set -e
set -x

unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

git clean -ffdx

evaluation/get_data.sh

ln -s . asn1star
tar czf asn1star.tgz $(find asn1star/ -type f -and -not -name .gitignore -and -not -name package.sh -and -not -name asn1star.tgz -and -not -path asn1star/test_norm -and -not -name get_data.sh -and -not -name '*.zip' -and -not -name README-internal.txt)
rm asn1star
