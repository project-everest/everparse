#!/usr/bin/env python3
"""Deeply nested ANY values, as driver.c vectors ("A <hex>" / "R <hex>"):
SEQUENCE { SEQUENCE { ... { NULL } ... } } nested <depth> times (accept),
and the same with an innermost length overrunning its parent (reject)."""

import sys


def der_len(n):
    if n < 0x80:
        return bytes([n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(b)]) + b


def nest(inner, depth):
    v = inner
    for _ in range(depth):
        v = b"\x30" + der_len(len(v)) + v
    return v


depth = int(sys.argv[1])
print("A " + nest(b"\x05\x00", depth).hex() + " nested-" + str(depth))
print("R " + nest(b"\x05\x01", depth).hex() + " nested-overrun-" + str(depth))
