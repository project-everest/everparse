#!/usr/bin/env python3
"""Reject missing, mixed, or wrong-API generated validator headers."""

import argparse
from pathlib import Path
import re
import sys


VALIDATOR = re.compile(r"\b(uint(?:8|64)_t)\s+\w+Validate\w*\s*\(")
PULSE_INTERNAL = re.compile(r"EVERPARSEPULSEINTERNAL_|EverParsePulseInternal")


def check_api(api, directory):
    expected = "uint64_t" if api == "lowstar" else "uint8_t"
    validators = []
    for header in sorted(directory.glob("*.h")):
        source = header.read_text()
        types = VALIDATOR.findall(source)
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
        if bool(PULSE_INTERNAL.search(source)) != (api == "lowstar"):
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
