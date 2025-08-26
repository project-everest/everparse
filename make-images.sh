#!/usr/bin/env bash
set -e
set -x
if [[ -n "$CI_BRANCH" ]] ; then
    ci_branch_arg="--build-arg CI_BRANCH=$CI_BRANCH"
fi
if [[ -n "$CACHE_BUST" ]] ; then
    cache_bust_arg="--build-arg CACHE_BUST=$CACHE_BUST"
else
    cache_bust_arg="--build-arg CACHE_BUST=$(date +%s)"
fi
run_docker () {
    docker build -f git.Dockerfile $ci_branch_arg $cache_bust_arg "$@" .
}
run_docker --pull -t evercbor-ccs2025-deps --target deps
run_docker -t evercbor-ccs2025-build --target build
run_docker -t evercbor-ccs2025-test --target test
docker save evercbor-ccs2025-deps evercbor-ccs2025-build evercbor-ccs2025-test | gzip > evercbor-ccs2025.tar.gz
