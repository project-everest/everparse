#!/usr/bin/env bash
set -e
unset CDPATH
package_home="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
(cd "$package_home/bin" ; chmod +x * ) || true
chmod +x "$package_home"/lib/fstar/z3-*/bin/* || true
export LD_LIBRARY_PATH="$package_home/bin:$LD_LIBRARY_PATH"
if which clang-format >/dev/null ; then
    clang_format=--clang_format
else
    clang_format=
fi
exec "$package_home/bin/everparse-3d.exe" --__arg0 everparse.sh --batch $clang_format "$@"
