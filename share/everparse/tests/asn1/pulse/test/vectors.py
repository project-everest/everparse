#!/usr/bin/env python3
"""Print difftest vectors of one ASN.1 type as "A|R <hex> <id>" lines for
driver.c.  The expected verdict is the vector's "expect" field or, with
--oracle, the verdict of the pure F* spec runner (difftest out/ours.jsonl),
which also covers generated mutations whose "expect" is only a guess."""
import argparse, json

ap = argparse.ArgumentParser()
ap.add_argument("--type", required=True)
ap.add_argument("--oracle")
ap.add_argument("files", nargs="+")
args = ap.parse_args()

oracle = None
if args.oracle:
    oracle = {}
    for line in open(args.oracle):
        r = json.loads(line)
        oracle[r["id"]] = r["verdict"]

for path in args.files:
    for v in json.load(open(path))["vectors"]:
        if v["type"] != args.type:
            continue
        verdict = v["expect"] if oracle is None else oracle.get(v["id"])
        if verdict not in ("accept", "reject"):
            continue
        print(("A " if verdict == "accept" else "R ") + v["hex"].replace(" ", ""), v["id"])
