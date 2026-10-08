#!/usr/bin/env python3
"""Reject missing, mixed, or wrong-API generated validator headers."""

import argparse
from pathlib import Path
import re
import sys


VALIDATOR = re.compile(r"\b(uint(?:8|64)_t)\s+(\w*Validate\w*)\s*\(")
PULSE_INTERNAL = re.compile(r"EVERPARSEPULSEINTERNAL_|EverParsePulseInternal")

# Under --api lowstar, 3d emits the Pulse-native worker as
# `validate_<reserved_prefix>core_<root>` (InterpreterTarget.pulse_worker_name),
# which KaRaMeL renders as `<Module>ValidateCore<Root>`, and wraps it in a
# public adapter returning the legacy uint64_t result. The worker is tagged
# KrmlPrivate, so the old extraction hid it in internal/ -- which this script
# deliberately does not glob. Custard ignores KrmlPrivate (see the comment in
# ../lowstar/Makefile), so the worker now sits in the public header, where its
# uint8_t result must not be mistaken for a wrong-API public validator.
LOWSTAR_WORKER = re.compile(r"Validate_*Core")


def check_api(api, directory):
    expected = "uint64_t" if api == "lowstar" else "uint8_t"
    validators = []
    for header in sorted(directory.glob("*.h")):
        source = header.read_text()
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
