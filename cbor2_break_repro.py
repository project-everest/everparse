"""
Minimal repro: cbor2.loads accepts the CBOR break stop code (0xff) wherever a
data item is expected, instead of rejecting it as malformed CBOR.

Per RFC 8949 §3.2.1, the break stop code (major type 7, additional info 31,
encoded as the single byte 0xff) is only valid as a terminator inside an
indefinite-length string, array, or map. Anywhere else it is malformed CBOR
and a well-formed-CBOR decoder MUST reject it.

cbor2 instead returns an internal sentinel object (the "break marker"),
even with allow_indefinite=False (added in 6.0), and this sentinel leaks
into definite-length arrays/maps and generic CBORTag values as if it were
a normal data item. Reproduced on cbor2 6.0.1.
"""

import sys
import cbor2
from importlib.metadata import version as _pkg_version

CASES = [
    # (label, hex, expected_description, kwargs)
    ("lone break",                                "ff",          "single 0xff",                              {}),
    ("lone break, allow_indefinite=False",        "ff",          "single 0xff",                              {"allow_indefinite": False}),
    ("definite array [1, BREAK, 2]",              "8301ff02",    "def-array of 3 items, middle is 0xff",     {}),
    ("definite array [BREAK]",                    "81ff",        "def-array of 1 item: 0xff",                {}),
    ("definite map {1: BREAK}",                   "a101ff",      "def-map, value is 0xff",                   {}),
    ("definite map {BREAK: 1}",                   "a1ff01",      "def-map, key is 0xff",                     {}),
    ("nested [[BREAK], 1]",                       "8281ff01",    "def-array containing a def-array of 0xff", {}),
    ("tag(100000) wrapping BREAK",                "da000186a0ff", "generic tag whose tagged value is 0xff",  {}),
]

def run(label, hex_bytes, kwargs):
    data = bytes.fromhex(hex_bytes)
    try:
        result = cbor2.loads(data, **kwargs)
    except cbor2.CBORDecodeError as e:
        print(f"[OK]   {label:<42}  -> CBORDecodeError: {e}")
        return True
    print(f"[BUG]  {label:<42}  -> {result!r}")
    return False

print(f"cbor2 version: {_pkg_version('cbor2')}")
print(f"python:        {sys.version.split()[0]}")
print()

ok = True
for label, hexb, _desc, kwargs in CASES:
    ok &= run(label, hexb, kwargs)

# The sentinel cannot be identified through the public API.
LONE = b"\xff"
print()
print(f"singleton across calls?            {cbor2.loads(LONE) is cbor2.loads(LONE)}")
print(f"public 'break_marker' exported?    {'break_marker' in dir(cbor2)}")

sys.exit(0 if ok else 1)
