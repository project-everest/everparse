#!/bin/bash
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
nohup code-server --auth none --bind-addr 0.0.0.0:8080 --disable-workspace-trust . \
    >>code-server.log 2>&1 &
disown

echo Started code-server on http://localhost:8080
echo
