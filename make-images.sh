#!/usr/bin/env bash
set -e
set -x
if [[ -n "$CI_BRANCH" ]] ; then
    ci_branch_arg="--build-arg CI_BRANCH=$CI_BRANCH"
fi
cache_bust_arg="--build-arg CACHE_BUST=$(date +%s)"
run_docker () {
    docker build -f git.Dockerfile $ci_branch_arg $cache_bust_arg "$@" .
}
run_docker --pull -t ccs2025-deps --target deps
run_docker -t ccs2025-build --target build
run_docker -t ccs2025-test --target test
docker save ccs2025-deps > ccs2025-deps.tar
gzip ccs2025-deps.tar
docker save ccs2025-deps > ccs2025-deps.tar
gzip ccs2025-deps.tar
docker save ccs2025-build > ccs2025-build.tar
gzip ccs2025-build.tar
docker save ccs2025-test > ccs2025-test.tar
gzip ccs2025-test.tar
