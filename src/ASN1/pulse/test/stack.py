#!/usr/bin/env python3
"""Static stack bound for extracted validators.

Reads the call graph produced by `gcc -fcallgraph-info=su` (a .ci file),
checks that no cycle (recursion) and no frame of dynamic or unbounded size
is reachable from the given entry points, and prints the worst-case stack
usage of each entry point (sum of frame sizes along the deepest call path).
Fails if a bound exceeds --budget bytes."""

import argparse
import re
import sys

NODE = re.compile(r'node: \{ title: "([^"]*)" label: "([^"]*)"')
EDGE = re.compile(r'edge: \{ sourcename: "([^"]*)" targetname: "([^"]*)"')
SIZE = re.compile(r"\\n(\d+) bytes \(([a-z,]+)\)")


def name(title):
    return title.rsplit(":", 1)[-1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=int, required=True)
    ap.add_argument("ci")
    ap.add_argument("entries", nargs="+")
    a = ap.parse_args()

    frame, kind, succ = {}, {}, {}
    with open(a.ci) as f:
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
            sys.exit(f"entry point {e} not found in {a.ci}")
        b = bound(e, [])
        status = "ok" if b <= a.budget else f"OVER BUDGET ({a.budget})"
        print(f"{e}: at most {b} bytes of stack, {status}")
        if b > a.budget:
            errors += 1
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
