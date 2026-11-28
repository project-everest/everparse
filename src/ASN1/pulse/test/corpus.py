#!/usr/bin/env python3
"""Compare a Custard-extracted C validator against the pure F* spec runner
(../evaluation/ASN1_Parser.exe, extracted to OCaml) on a corpus of DER files.

For every file, the C validator and the spec must agree exactly: the spec
returns Some (_, n) iff the C validator succeeds consuming n bytes.  Files
listed in <dir>_ignore.txt are skipped, as in ../evaluation/run.sh, and so
are files larger than --max-size (the spec runner is slow on them)."""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys

SUCCESS = re.compile(rb"parsing succeeded consuming (\d+) bytes")


def spec_verdict(spec, fmt, path):
    r = subprocess.run([spec, fmt, path], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    m = SUCCESS.search(r.stdout)
    if r.returncode == 0 and m:
        return int(m.group(1))
    if b"could not be read" in r.stdout:
        sys.exit(f"spec runner could not read {path}")
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--format", required=True, choices=["X509", "CRL"])
    ap.add_argument("--spec", required=True)
    ap.add_argument("--exe", required=True)
    ap.add_argument("--max-size", type=int, default=100000)
    ap.add_argument("-j", type=int, default=os.cpu_count() or 1)
    ap.add_argument("dirs", nargs="+")
    a = ap.parse_args()

    files = []
    skipped = 0
    for d in a.dirs:
        d = d.rstrip("/")
        ign = set()
        ign_file = d + "_ignore.txt"
        if os.path.exists(ign_file):
            with open(ign_file) as f:
                ign = {l.strip() for l in f if l.strip() and not l.startswith("//")}
        for name in sorted(os.listdir(d)):
            if not name.endswith(".der"):
                continue
            p = os.path.join(d, name)
            if name in ign or os.path.getsize(p) > a.max_size:
                skipped += 1
                continue
            files.append(p)

    r = subprocess.run([a.exe], input="\n".join(files).encode() + b"\n",
                       stdout=subprocess.PIPE, check=True)
    c = {}
    for line in r.stdout.decode().splitlines():
        ok, off, _size, path = line.split(" ", 3)
        c[path] = int(off) if ok == "1" else None
    assert len(c) == len(files)

    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        spec = dict(zip(files, ex.map(lambda p: spec_verdict(a.spec, a.format, p), files)))

    mismatches = 0
    accepted = 0
    for p in files:
        if spec[p] is not None:
            accepted += 1
        if spec[p] != c[p]:
            mismatches += 1
            print(f"MISMATCH {p}: spec {spec[p]}, C {c[p]}")
    print(f"{a.format}: {len(files)} files ({accepted} accepted by the spec, "
          f"{skipped} skipped), {mismatches} mismatches")
    sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
