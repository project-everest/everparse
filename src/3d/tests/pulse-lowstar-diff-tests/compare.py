"""Strict, field-addressed trace comparison; never compare process addresses."""

import json
from pathlib import Path
from corpus import HarnessError


def read_trace(path):
    records = {}
    for number, line in enumerate(Path(path).read_text().splitlines(), 1):
        if not line.startswith("@@"):
            continue  # Unchanged clients can write their own diagnostics to stdout.
        try:
            row = json.loads(line[2:])
        except ValueError as error:
            raise HarnessError(f"{path}:{number}: invalid observation: {error}") from error
        if set(row) != {"case", "function", "field", "value"}:
            raise HarnessError(f"{path}:{number}: invalid observation schema")
        key = (row["case"], row["function"], row["field"])
        if not all(isinstance(k, str) and k for k in key):
            raise HarnessError(f"{path}:{number}: invalid observation key")
        if key in records:
            raise HarnessError(f"{path}:{number}: duplicate observation {key}")
        if row["value"] is not None and type(row["value"]) not in {str, int}:
            raise HarnessError(f"{path}:{number}: non-scalar observation {key}")
        if row["value"] == "<unregistered-pointer>":
            raise HarnessError(f"{path}:{number}: unnormalized pointer at {key}")
        records[key] = row["value"]
    if not records:
        raise HarnessError(f"{path}: no observations (exit status is not differential evidence)")
    return records


def compare(left, right):
    differences = []
    for key in sorted(left.keys() | right.keys()):
        a, b = left.get(key), right.get(key)
        if key not in left or key not in right or type(a) is not type(b) or a != b:
            differences.append({"case": key[0], "function": key[1], "field": key[2],
                                "legacy_lowstar": a, "lowstar": b,
                                "missing": "legacy_lowstar" if key not in left else
                                           "lowstar" if key not in right else None})
    return differences


def check_executed(records, inputs, required):
    names = list(required)
    expected = {(row[0], names[int(row[1])]) for row in
                (line.split() for line in inputs.splitlines())}
    actual = {(key[0], key[1]) for key in records if key[2] == "return"}
    if actual != expected:
        raise HarnessError(f"input execution mismatch: {len(expected-actual)} missing, "
                           f"{len(actual-expected)} unexpected; "
                           f"first missing: {sorted(expected-actual)[:3]}")


def coverage(records, required):
    result = {}
    for fn, contract in required.items():
        rows = {key: value for key, value in records.items() if key[1] == fn}
        cases = {key[0] for key in rows}
        missing = []
        success = failure = 0
        for case in sorted(cases):
            fields = {k[2] for k in rows if k[0] == case}
            missing.extend(f"{case}:{field}" for field in contract["fields"] if field not in fields)
            ret = rows.get((case, fn, "return"))
            if contract["return"] == "uint32_t" and ret == 0:
                missing.extend(f"{case}:{field}" for field in
                               ("validator.return", "validator.kind", "validator.position")
                               if field not in fields)
            if ret is not None:
                ok = ret == 1 if contract["return"] == "BOOLEAN" else (
                    ret == 0 if contract["return"] == "uint32_t" else
                    ret >> 60 == 0 if contract.get("direct", True) else
                    rows.get((case, fn, "error.count")) == 0 and
                    rows.get((case, fn, "stream.status"), 1) == 1)
                success += ok
                failure += not ok
        if not cases:
            missing.append("no executed cases")
        result[fn] = {"cases": len(cases), "success": success, "failure": failure,
                      "missing_fields": missing}
        if contract.get("negative_only"):
            result[fn]["negative_only"] = contract["negative_only"]
    return result
