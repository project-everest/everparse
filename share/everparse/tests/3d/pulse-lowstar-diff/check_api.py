#!/usr/bin/env python3
"""Reject missing, mixed, or wrong-API generated validator headers."""

import argparse
from pathlib import Path
import re
import sys


VALIDATOR = re.compile(r"\b(uint(?:8|64)_t)\s+(\w*Validate\w*)\s*\(")
WRAPPER = re.compile(r"\b(BOOLEAN|bool)\s+(\w*Check\w*)\s*\(([^;]*)\);")
PULSE_INTERNAL = re.compile(r"EverParsePulseInternal")

# Older extraction exposed the Pulse worker next to the public uint64_t
# adapter. Native Custard keeps it private and preserves its F* name.
# Runtime constants may normalize to literals, so their names alone cannot
# distinguish a native Lowstar implementation from a legacy one.
LOWSTAR_WORKER = re.compile(r"Validate_*Core")
LOWSTAR_NATIVE_WORKER = re.compile(r"\buint8_t\s+\w+_validate_+core_+\w+\s*\(")


def check_api(api, directory):
    expected = "uint64_t" if api == "lowstar" else "uint8_t"
    validators = []
    for header in sorted(directory.glob("*.h")):
        source = header.read_text()
        boolean = "BOOLEAN" if api == "lowstar" else "bool"
        for result, _, parameters in WRAPPER.findall(source):
            if result != "BOOLEAN":
                raise ValueError(f"{header}: expected BOOLEAN wrapper results")
            if any(ty != boolean for ty in re.findall(r"\b(BOOLEAN|bool)\b", parameters)):
                raise ValueError(f"{header}: expected {api} Boolean parameters ({boolean})")
        types = [
            ty
            for ty, name in VALIDATOR.findall(source)
            if not (api == "lowstar" and LOWSTAR_WORKER.search(name))
        ]
        if not types:
            continue
        validators.append(header)
        if any(ty != expected for ty in types):
            raise ValueError(f"{header}: expected {api} validator results ({expected})")
    if not validators:
        raise ValueError(f"{directory}: missing generated {api} validators")
    for header in validators:
        implementation = header.with_suffix(".c")
        if not implementation.is_file():
            raise ValueError(f"{header}: not generated with --api {api}; missing implementation")
        source = implementation.read_text()
        internal = directory / "internal" / header.name
        if internal.is_file():
            source += internal.read_text()
        if "EverParsePulseInternal.h" in source or "EverParsePulseInternal.h" in header.read_text():
            raise ValueError(f"{header}: obsolete separate Pulse support header; regenerate this output")
        lowstar = bool(PULSE_INTERNAL.search(source) or LOWSTAR_NATIVE_WORKER.search(source))
        if lowstar != (api == "lowstar"):
            raise ValueError(f"{header}: not generated with --api {api}; regenerate this output")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("api", choices=("lowstar", "pulse"))
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    try:
        check_api(args.api, args.directory)
    except (OSError, ValueError) as error:
        print(f"pulse-lowstar-diff: {error}", file=sys.stderr)
        sys.exit(1)
