#!/usr/bin/env python3
"""Static stack bound for extracted validators.

Reads the call graph and frame sizes produced either by
`gcc -fcallgraph-info=su` (a .ci file, with --ci), or by clang, which has no
-fcallgraph-info: frame sizes from `clang -fstack-usage` (a .su file, with
--su) and call graph from `clang -S -emit-llvm` (a .ll file, with --ll), both
at -O0. Then checks that no cycle (recursion) and no frame of dynamic or unbounded size
is reachable from the given entry points, and prints the worst-case stack
usage of each entry point (sum of frame sizes along the deepest call path).
Fails if a bound exceeds --budget bytes."""

import argparse
import re
import sys

NODE = re.compile(r'node: \{ title: "([^"]*)" label: "([^"]*)"')
EDGE = re.compile(r'edge: \{ sourcename: "([^"]*)" targetname: "([^"]*)"')
SIZE = re.compile(r"\\n(\d+) bytes \(([a-z,]+)\)")
SU = re.compile(r"^(.*)\t(\d+)\t([a-z,]+)$")
DEFINE = re.compile(r"^define [^@]*@([\w.$]+)\(")
CALL = re.compile(r"\b(?:call|invoke) [^@%]*?(@[\w.$]+|%[\w.$]+)\(")


def name(title):
    return title.rsplit(":", 1)[-1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=int, required=True)
    ap.add_argument("--ci", help="gcc -fcallgraph-info=su output")
    ap.add_argument("--su", help="clang -fstack-usage output")
    ap.add_argument("--ll", help="clang -S -emit-llvm output")
    ap.add_argument("entries", nargs="+")
    a = ap.parse_args()
    if bool(a.ci) == bool(a.su or a.ll) or bool(a.su) != bool(a.ll):
        ap.error("expected either --ci, or both --su and --ll")

    frame, kind, succ = {}, {}, {}
    if a.ci:
        read_ci(a.ci, frame, kind, succ)
        src = a.ci
    else:
        read_su_ll(a.su, a.ll, frame, kind, succ)
        src = a.su
    check(a, src, frame, kind, succ)


def read_ci(path, frame, kind, succ):
    with open(path) as f:
        for line in f:
            m = NODE.search(line)
            if m:
                n = name(m.group(1))
                s = SIZE.search(m.group(2))
                # external functions (e.g. libc) have no size: count 0
                frame[n] = int(s.group(1)) if s else 0
                kind[n] = s.group(2) if s else "external"
                succ.setdefault(n, set())
                continue
            m = EDGE.search(line)
            if m:
                succ.setdefault(name(m.group(1)), set()).add(name(m.group(2)))


def read_su_ll(su, ll, frame, kind, succ):
    with open(su) as f:
        for line in f:
            m = SU.match(line.rstrip("\n"))
            if m:
                n = name(m.group(1))
                frame[n] = int(m.group(2))
                kind[n] = m.group(3)
                succ.setdefault(n, set())
    cur = None
    with open(ll) as f:
        for line in f:
            m = DEFINE.match(line)
            if m:
                cur = m.group(1)
                succ.setdefault(cur, set())
                continue
            if line.startswith("}"):
                cur = None
                continue
            if cur is None:
                continue
            for c in CALL.findall(line):
                if c.startswith("%"):
                    # indirect call: the callee is unknown
                    kind[cur] = "indirect call"
                elif not c.startswith("@llvm."):
                    succ[cur].add(c[1:])
    for n in succ:
        if n not in frame:
            frame[n] = 0
            kind.setdefault(n, "external")


def check(a, src, frame, kind, succ):
    errors = 0
    memo, onstack = {}, set()

    def bound(n, path):
        nonlocal errors
        if n in memo:
            return memo[n]
        if n in onstack:
            print("recursion: " + " -> ".join(path + [n]))
            errors += 1
            return 0
        if kind.get(n, "external") not in ("static", "dynamic,bounded", "external"):
            print(f"{n}: frame size is {kind[n]}")
            errors += 1
        onstack.add(n)
        b = frame.get(n, 0) + max((bound(m, path + [n]) for m in succ.get(n, ())), default=0)
        onstack.discard(n)
        memo[n] = b
        return b

    for e in a.entries:
        if e not in frame:
            sys.exit(f"entry point {e} not found in {src}")
        b = bound(e, [])
        status = "ok" if b <= a.budget else f"OVER BUDGET ({a.budget})"
        print(f"{e}: at most {b} bytes of stack, {status}")
        if b > a.budget:
            errors += 1
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
