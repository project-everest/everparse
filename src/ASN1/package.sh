#!/bin/bash
set -e
set -x

unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

git clean -ffdx

ln -s . asn1star
tar czf asn1star.tgz $(find asn1star/ -type f -and -not -name .gitignore -and -not -name package.sh -and -not -name asn1star.tgz -and -not -path asn1star/test_norm -and -not -name README-internal.txt)
rm asn1star
