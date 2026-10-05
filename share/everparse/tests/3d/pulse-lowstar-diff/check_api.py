#!/usr/bin/env python3
"""Reject missing, mixed, or wrong-API generated validator headers."""

import argparse
from pathlib import Path
import re
import sys


VALIDATOR = re.compile(r"\b(uint(?:8|64)_t)\s+\w+Validate\w*\s*\(")
PULSE_INTERNAL = '#include "EverParsePulseInternal.h"'


def check_api(api, directory):
    expected = "uint64_t" if api == "lowstar" else "uint8_t"
    validators = 0
    for header in sorted(directory.glob("*.h")):
        source = header.read_text()
        types = VALIDATOR.findall(source)
        if not types:
            continue
        validators += len(types)
        if any(ty != expected for ty in types):
            raise ValueError(f"{header}: expected {api} validator results ({expected})")
        if (PULSE_INTERNAL in source) != (api == "lowstar"):
            raise ValueError(f"{header}: not generated with --api {api}; regenerate this output")
    if not validators:
        raise ValueError(f"{directory}: missing generated {api} validators")


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
