"""EverCBOR cross-language tests against Intel cbor2.

Reads the artefact files written by the C test binaries (see cbor_tests.c)
and re-runs the same conformance checks through the cbor2 Python library:

  * For invalid test cases:  cbor2.loads() must raise CBORDecodeError.
  * For valid test cases:    cbor2.loads() must succeed and the parsed
                             value must compare equal (via Python ==) to a
                             value built independently through the cbor2
                             constructor API.
  * For canonical test cases: cbor2.dumps(expected, canonical=True) must
                              equal the input bytes byte-for-byte.

Each test is repeated --iterations times and timed, mirroring the C suite.

Artefacts produced by the C binaries live under <out_dir>/ as

    <api>_<name>.input.cbor        # always (valid + invalid)
    <api>_<name>.serialized.cbor   # valid tests only

where <api> is "det" or "nondet". This script iterates over both APIs
and skips files that do not exist (e.g. *_nondet tests under det produce
no .serialized file because the input is rejected there).
"""

from __future__ import annotations

import argparse
import importlib.metadata
import inspect
import os
import sys
import time
from pathlib import Path
from typing import Any, Callable

try:
    import cbor2
    from cbor2 import CBORDecodeError, CBORTag, CBORSimpleValue
except ImportError as exc:  # pragma: no cover
    sys.stderr.write(f"FATAL: cannot import cbor2: {exc}\n"
                     f"Install it with: pip install cbor2\n")
    raise SystemExit(2)

# cbor2 6.x exposes its hashable-mapping type as cbor2.frozendict (lowercase);
# on Python 3.15+ the language gained a builtin frozendict and cbor2 uses that.
try:
    FrozenDict = cbor2.frozendict           # type: ignore[attr-defined]
except AttributeError:
    try:
        FrozenDict = cbor2.FrozenDict       # type: ignore[attr-defined]
    except AttributeError:
        FrozenDict = frozenset  # placeholder, will not be reached on supported versions
        sys.stderr.write("FATAL: cbor2.frozendict / cbor2.FrozenDict not found\n")
        raise SystemExit(2)


# ----------------------------------------------------------------------------
# Decoder feature detection
# ----------------------------------------------------------------------------

def _supports_loads_kwarg(name: str) -> bool:
    try:
        sig = inspect.signature(cbor2.loads)
    except (TypeError, ValueError):
        return False
    return name in sig.parameters


HAS_ALLOW_INDEFINITE = _supports_loads_kwarg("allow_indefinite")
HAS_ALLOW_DUP_KEYS = _supports_loads_kwarg("allow_duplicate_keys")
HAS_IMMUTABLE = _supports_loads_kwarg("immutable")
HAS_MAX_DEPTH = _supports_loads_kwarg("max_depth")

# The recursion-budget tests build CBOR objects nested ~2200 levels deep.
# Python's default recursion limit is 1000 and cbor2's default max_depth is
# 400; both need to be raised to accommodate the very deep arrays.
_DEEP_LIMIT = 4096
sys.setrecursionlimit(max(sys.getrecursionlimit(), _DEEP_LIMIT))


def strict_loads(data: bytes) -> Any:
    """cbor2.loads with the strictest settings supported by the installed version."""
    kwargs: dict[str, Any] = {}
    if HAS_IMMUTABLE:
        kwargs["immutable"] = True
    if HAS_ALLOW_INDEFINITE:
        kwargs["allow_indefinite"] = False
    if HAS_ALLOW_DUP_KEYS:
        kwargs["allow_duplicate_keys"] = False
    if HAS_MAX_DEPTH:
        kwargs["max_depth"] = _DEEP_LIMIT
    return cbor2.loads(data, **kwargs)


def lenient_loads(data: bytes) -> Any:
    """cbor2.loads with only `immutable=True` (i.e. accepting indefinite/dup-keys)."""
    if HAS_IMMUTABLE:
        return cbor2.loads(data, immutable=True)
    return cbor2.loads(data)


# ----------------------------------------------------------------------------
# Helpers used by the test factories
# ----------------------------------------------------------------------------

def _fdict(items) -> Any:
    """Build a hashable map (used as a key) from an iterable of (k, v) pairs."""
    return FrozenDict(dict(items))


# Deeply nested array depth must match #define ARR_DEPTH 30 in cbor_tests.c.
ARR_DEPTH = 30
# Deeply nested map depth must match #define MAP_DEPTH 10 in cbor_tests.c.
MAP_DEPTH = 10
# Nested-map-key recursion depth must match #define MAP_KEY_DEPTH 3 in cbor_tests.c.
MAP_KEY_DEPTH = 3


def _arr_deep(d: int, leaf: int) -> Any:
    out: Any = leaf
    for _ in range(d):
        out = (out,)
    return out


def _map_deep(d: int, leaf: int) -> Any:
    out: Any = leaf
    for _ in range(d):
        out = FrozenDict({0: out})
    return out


def _dnm(d: int, x: int) -> Any:
    """Mirror of build_dnm() in cbor_tests.c: binary recursion on the key side."""
    if d == 0:
        return x
    left = _dnm(d - 1, 2 * x)
    right = _dnm(d - 1, 2 * x + 1)
    return _fdict([(left, 0), (right, 1)])


def _expected_map_nested_keys() -> Any:
    a = _dnm(MAP_KEY_DEPTH, 0)
    b = _dnm(MAP_KEY_DEPTH, 1)
    pair1 = (a, a)
    pair2 = (a, b)
    return FrozenDict({pair1: 0, pair2: 1})


# ----------------------------------------------------------------------------
# Test catalogue
# ----------------------------------------------------------------------------
#
# Each entry is keyed by the test name used in cbor_tests.c. Fields:
#
#   valid:     True if cbor2 (in strict mode) must accept the input.
#   canonical: True if the C-emitted input bytes are canonical (input bytes
#              must equal cbor2.dumps(expected, canonical=True)).
#   expected:  zero-arg factory returning the expected Python object. Only
#              consulted for valid tests.
#   strict:    True (default) if we use strict_loads(); False if the test
#              must use lenient_loads() because its semantics depend on a
#              feature that is only checked under stricter modes (notably
#              the duplicate-key tests need the strict path to make the
#              decoder reject; the *_nondet tests need the strict path so
#              that allow_indefinite=False does not accidentally accept
#              malformed inputs).

class T(dict):
    """Convenience: T(valid=..., expected=lambda: ..., canonical=..., kind=...).

    `kind` is one of:
      * "cbor"  (default) — input file is a CBOR encoding; standard
        validate/parse/equality flow.
      * "utf8_invalid_payload" — input file holds raw bytes that the C
        side rejected as invalid UTF-8 in mk_text_string. The Python
        equivalent asserts that bytes.decode('utf-8') raises
        UnicodeDecodeError. `valid` is implicitly False for this kind.
    """
    pass


def _qcbor_complex_value() -> Any:
    return FrozenDict({
        "first integer": 42,
        "an array of two strings": ("string1", "string2"),
        "map in a map": FrozenDict({
            "bytes 1":     b"\x78\x78\x78\x78",
            "bytes 2":     b"\x79\x79\x79\x79",
            "another int": 98,
            "text 2":      "lies, damn lies and statistics",
        }),
    })


def _arr_int_boundaries_value() -> Any:
    ints = (
        -9223372036854775808,
        -4294967297, -4294967296, -4294967295, -4294967294,
        -2147483648, -2147483647,
        -65538, -65537, -65536, -65535, -65534,
        -257, -256, -255, -254,
        -25, -24, -23, -1,
        0, 0, 1, 22, 23, 24, 25, 26,
        254, 255, 256, 257,
        65534, 65535, 65536, 65537, 65538,
        2147483647, 2147483647, 2147483648, 2147483649,
        4294967294, 4294967295, 4294967296, 4294967297,
        9223372036854775807,
        0xFFFFFFFFFFFFFFFF,  # last entry, the only > int64
    )
    return ints


def _arr_empties_value() -> Any:
    return (0, (), ((), (0,), FrozenDict({}),
                    FrozenDict({1: FrozenDict({}),
                                2: FrozenDict({}),
                                3: ()})))


TESTS: dict[str, T] = {
    # Major type 0
    "uint_zero_canonical":         T(valid=True,  canonical=True,  expected=lambda: 0),
    "uint_small_canonical":        T(valid=True,  canonical=True,  expected=lambda: 23),
    "uint_one_byte_canonical":     T(valid=True,  canonical=True,  expected=lambda: 100),
    "uint_two_byte_canonical":     T(valid=True,  canonical=True,  expected=lambda: 1000),
    "uint_four_byte_canonical":    T(valid=True,  canonical=True,  expected=lambda: 1_000_000),
    "uint_eight_byte_canonical":   T(valid=True,  canonical=True,  expected=lambda: 1 << 32),
    "uint_zero_nondet":            T(valid=True,  canonical=False, expected=lambda: 0),
    "uint_100_nondet":             T(valid=True,  canonical=False, expected=lambda: 100),
    "uint_zero_long_nondet":       T(valid=True,  canonical=False, expected=lambda: 0),

    # Major type 1
    "neg_minus_one_canonical":     T(valid=True,  canonical=True,  expected=lambda: -1),
    "neg_small_canonical":         T(valid=True,  canonical=True,  expected=lambda: -10),
    "neg_one_byte_canonical":      T(valid=True,  canonical=True,  expected=lambda: -100),
    "neg_minus_one_nondet":        T(valid=True,  canonical=False, expected=lambda: -1),

    # Major type 2 (byte string)
    "bstr_empty_canonical":        T(valid=True,  canonical=True,  expected=lambda: b""),
    "bstr_short_canonical":        T(valid=True,  canonical=True,  expected=lambda: b"\xde\xad\xbe\xef"),
    "bstr_empty_nondet":           T(valid=True,  canonical=False, expected=lambda: b""),

    # Major type 3 (text string)
    "tstr_empty_canonical":        T(valid=True,  canonical=True,  expected=lambda: ""),
    "tstr_hello_canonical":        T(valid=True,  canonical=True,  expected=lambda: "hello"),
    "tstr_hello_nondet":           T(valid=True,  canonical=False, expected=lambda: "hello"),

    # Major type 4 (array)
    "arr_empty_canonical":         T(valid=True,  canonical=True,  expected=lambda: ()),
    "arr_three_canonical":         T(valid=True,  canonical=True,  expected=lambda: (1, 2, 3)),
    "arr_empty_nondet":            T(valid=True,  canonical=False, expected=lambda: ()),
    "arr_deeply_nested_canonical": T(valid=True,  canonical=True,  expected=lambda: _arr_deep(ARR_DEPTH, 1)),

    # Major type 5 (map)
    "map_empty_canonical":         T(valid=True,  canonical=True,  expected=lambda: FrozenDict({})),
    "map_two_canonical":           T(valid=True,  canonical=True,
                                     expected=lambda: FrozenDict({1: b"\x01", 2: "ab"})),
    "map_two_nondet":              T(valid=True,  canonical=False,
                                     expected=lambda: FrozenDict({1: b"\x01", 2: "ab"})),
    "map_deeply_nested_canonical": T(valid=True,  canonical=True,
                                     expected=lambda: _map_deep(MAP_DEPTH, 0)),
    "map_nested_keys_canonical":   T(valid=True,  canonical=True,
                                     expected=_expected_map_nested_keys),
    "map_dup_key_invalid":         T(valid=False),
    "map_dup_diff_enc_invalid":    T(valid=False),

    # Major type 6 (tagged)
    "tag_canonical":               T(valid=True,  canonical=True,
                                     expected=lambda: CBORTag(1000, 0)),
    "tag_nondet":                  T(valid=True,  canonical=False,
                                     expected=lambda: CBORTag(1000, 0)),

    # Major type 7 (simple value, no floats)
    "simple_short_canonical":      T(valid=True,  canonical=True,
                                     expected=lambda: CBORSimpleValue(16)),
    "simple_long_canonical":       T(valid=True,  canonical=True,
                                     expected=lambda: CBORSimpleValue(100)),
    "simple_24_invalid":           T(valid=False),

    # General invalid encodings
    "invalid_truncated":           T(valid=False),
    "invalid_bstr_short":          T(valid=False),
    "invalid_arr_short":           T(valid=False),
    "invalid_map_short":           T(valid=False),
    "invalid_indefinite":          T(valid=False),

    # ---- Imported from cbor-test-unverified gentest ----
    "uint_one_canonical":          T(valid=True,  canonical=True,  expected=lambda: 1),
    "uint_ten_canonical":          T(valid=True,  canonical=True,  expected=lambda: 10),
    "uint_24_canonical":           T(valid=True,  canonical=True,  expected=lambda: 24),
    "uint_25_canonical":           T(valid=True,  canonical=True,  expected=lambda: 25),
    "uint_trillion_canonical":     T(valid=True,  canonical=True,  expected=lambda: 10**12),
    "neg_two_byte_canonical":      T(valid=True,  canonical=True,  expected=lambda: -1000),
    "tstr_a_canonical":            T(valid=True,  canonical=True,  expected=lambda: "a"),
    "tstr_ietf_canonical":         T(valid=True,  canonical=True,  expected=lambda: "IETF"),
    "tstr_escapes_canonical":      T(valid=True,  canonical=True,  expected=lambda: "\"\\"),
    "tstr_u_umlaut_canonical":     T(valid=True,  canonical=True,  expected=lambda: "\u00fc"),
    "tstr_water_canonical":        T(valid=True,  canonical=True,  expected=lambda: "\u6c34"),
    "tstr_drachma_canonical":      T(valid=True,  canonical=True,  expected=lambda: "\U00010151"),
    "arr_nested_canonical":        T(valid=True,  canonical=True,  expected=lambda: (1, (2, 3), (4, 5))),
    "arr_25_canonical":            T(valid=True,  canonical=True,
                                     expected=lambda: tuple(range(1, 26))),
    "map_mixed_canonical":         T(valid=True,  canonical=True,
                                     expected=lambda: FrozenDict({"a": 1, "b": (2, 3)})),
    "arr_with_map_canonical":      T(valid=True,  canonical=True,
                                     expected=lambda: ("a", FrozenDict({"b": "c"}))),
    "map_five_canonical":          T(valid=True,  canonical=True,
                                     expected=lambda: FrozenDict({"a": "A", "b": "B",
                                                                   "c": "C", "d": "D",
                                                                   "e": "E"})),

    # ---- Recursion-budget tests ----
    "arr_2200_deep_canonical":             T(valid=True,  canonical=True,
                                              expected=lambda: _arr_deep(2200, 1)),
    "arr_2200_deep_truncated_invalid":     T(valid=False),

    # ---- qcbortests ports ----
    "arr_int_boundaries_canonical":        T(valid=True,  canonical=True,
                                              expected=_arr_int_boundaries_value),
    "arr_empties_canonical":               T(valid=True,  canonical=True,
                                              expected=_arr_empties_value),
    "map_qcbor_complex_nondet":            T(valid=True,  canonical=False,
                                              expected=_qcbor_complex_value),
}


# ---- UTF-8 tests (auto-populated below from the same table the C side uses) ----
#
# Format: (suffix, kind), where kind is one of:
#   "valid"   — the CBOR-encoded text-string is in the file and decodes to
#               the expected unicode string (= bytes.decode('utf-8')).
#   "invalid" — the file holds the raw byte sequence that the C side
#               rejected; bytes.decode('utf-8') must raise.
_UTF8_TESTS: tuple[tuple[str, str, bytes], ...] = (
    # 1-byte forms
    ("t05_0",            "valid",   bytes([0x00])),
    ("t29_4",            "invalid", bytes([0x80, 0x20])),
    ("t29_5",            "invalid", bytes([0x20, 0x80, 0x20])),
    ("t29_6",            "invalid", bytes([0x81, 0x20])),
    ("t29_7",            "invalid", bytes([0xc1, 0x20])),
    ("t29_8",            "invalid", bytes([0xf5, 0x20])),
    ("t29_9",            "invalid", bytes([0xff, 0x20])),
    ("t29_1",            "invalid", bytes([0x20, 0x80])),
    ("t29_2",            "invalid", bytes([0x20, 0x21, 0x21, 0x23, 0xfe, 0x20])),
    ("t29_3",            "invalid", bytes([0x20, 0x21, 0x21, 0x23, 0x24, 0xfe])),
    # 2-byte UTF-8
    ("t30_1",            "invalid", bytes([0xc2, 0x7f])),
    ("t30_2",            "invalid", bytes([0xc2, 0xc0])),
    ("t30_3",            "invalid", bytes([0xc2, 0xff])),
    ("t30_5",            "invalid", bytes([0xdf, 0x7f])),
    ("t30_6",            "invalid", bytes([0xdf, 0xc0])),
    ("t30_7",            "invalid", bytes([0xdf, 0xff])),
    ("t30_0",            "invalid", bytes([0xc2, 0x00])),
    ("t30_4",            "invalid", bytes([0xdf, 0x00])),
    # 3-byte UTF-8
    ("t31_0",            "invalid", bytes([0xe0, 0x80, 0x00])),
    ("t31_1",            "invalid", bytes([0xe0, 0x80, 0x7f])),
    ("t31_2",            "invalid", bytes([0xe0, 0x80, 0xc0])),
    ("t31_3",            "invalid", bytes([0xe0, 0x80, 0xff])),
    ("t32_0",            "invalid", bytes([0xed, 0x80, 0x00])),
    ("t32_1",            "invalid", bytes([0xed, 0x80, 0x7f])),
    ("t32_2",            "invalid", bytes([0xed, 0x80, 0xc0])),
    ("t32_3",            "invalid", bytes([0xed, 0x80, 0xff])),
    # 4-byte UTF-8
    ("t33_0",            "invalid", bytes([0xf0, 0x90, 0x80, 0x00])),
    ("t33_1",            "invalid", bytes([0xf0, 0x90, 0x80, 0x7f])),
    ("t33_2",            "invalid", bytes([0xf0, 0x90, 0x80, 0xc0])),
    ("t33_3",            "invalid", bytes([0xf0, 0x90, 0x80, 0xff])),
    ("t34_0",            "invalid", bytes([0xf1, 0x80, 0x80, 0x00])),
    ("t34_1",            "invalid", bytes([0xf1, 0x80, 0x80, 0x7f])),
    ("t34_2",            "invalid", bytes([0xf1, 0x80, 0x80, 0xc0])),
    ("t34_3",            "invalid", bytes([0xf1, 0x80, 0x80, 0xff])),
    ("t35_0",            "invalid", bytes([0xf4, 0x80, 0x80, 0x00])),
    ("t35_1",            "invalid", bytes([0xf4, 0x80, 0x80, 0x7f])),
    ("t35_2",            "invalid", bytes([0xf4, 0x80, 0x80, 0xc0])),
    ("t35_3",            "invalid", bytes([0xf4, 0x80, 0x80, 0xff])),
    # Overlong and partials
    ("t37_0_overlong",   "invalid", bytes([0xc0, 0x80])),
    ("t37_1_overlong",   "invalid", bytes([0xe0, 0x80, 0x80])),
    ("t37_2_overlong",   "invalid", bytes([0xf0, 0x80, 0x80, 0x80])),
    ("t37_3_overlong",   "invalid", bytes([0x20, 0x00, 0x20, 0xff])),
    ("t37_4_partial",    "valid",   bytes([0x20, 0x00])),
    ("t37_2_1_partial",  "valid",   bytes([0x20, 0x00, 0x35])),
    ("t9_1",             "invalid", bytes([0xc2, 0x41, 0x42])),
    # Non-character / replacement-character runs
    ("t36_9",            "valid",   bytes([0xef, 0xbf, 0xbf, 0x3d, 0xef, 0xbf, 0xbf, 0x2e])),
    ("t36_9_1",          "valid",   bytes([0xef, 0xbf, 0xbe, 0x3d, 0xef, 0xbf, 0xbe, 0x2e])),
    ("t36_10", "invalid", bytes([0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0x3d, 0xe0, 0x80, 0xaf, 0x2e])),
    ("t36_8",  "invalid", bytes([0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0x3d, 0xed, 0xa0, 0x80, 0x2e])),
    ("t36_7",  "invalid", bytes([0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0x3d, 0xf7, 0xbf, 0xbf, 0xbf, 0x2e])),
)

for _suffix, _validity, _payload in _UTF8_TESTS:
    _name = f"utf8_{_suffix}"
    if _validity == "valid":
        # The C side wrapped the payload into a CBOR text-string in the
        # input file; the expected Python value is that UTF-8 text.
        TESTS[_name] = T(valid=True, canonical=True,
                          expected=lambda p=_payload: p.decode("utf-8"))
    else:
        # Input file holds the raw payload bytes; assert UTF-8 decode raises.
        TESTS[_name] = T(valid=False, kind="utf8_invalid_payload")


# ----------------------------------------------------------------------------
# Per-test workhorse
# ----------------------------------------------------------------------------

class TestSkipped(Exception):
    pass


def _run_one(input_bytes: bytes, serialized_bytes: bytes | None,
             spec: T, *, allow_dup_keys_supported: bool) -> None:
    """Run one assertion pass for a single (input_bytes, [serialized_bytes]) pair.

    Raises AssertionError on failure, or TestSkipped if the test cannot be
    meaningfully evaluated by the installed cbor2 version.
    """
    kind = spec.get("kind", "cbor")

    if kind == "utf8_invalid_payload":
        # Input file holds raw UTF-8-invalid payload bytes that the C side
        # rejected at mk_text_string time. The Python equivalent is that
        # str.decode() raises.
        try:
            input_bytes.decode("utf-8")
        except UnicodeDecodeError:
            return
        raise AssertionError("UTF-8 decode of supposedly invalid payload "
                             "succeeded")

    if not spec["valid"]:
        # Special-case: cbor2 cannot reject duplicate map keys without the
        # allow_duplicate_keys=False flag, which only landed post-6.0.1.
        if not allow_dup_keys_supported and spec is TESTS["map_dup_key_invalid"]:
            raise TestSkipped("cbor2 lacks allow_duplicate_keys flag")
        if not allow_dup_keys_supported and spec is TESTS["map_dup_diff_enc_invalid"]:
            raise TestSkipped("cbor2 lacks allow_duplicate_keys flag")
        try:
            strict_loads(input_bytes)
        except CBORDecodeError:
            return
        raise AssertionError("strict cbor2.loads accepted an invalid encoding")

    expected = spec["expected"]()
    parsed = strict_loads(input_bytes)
    if parsed != expected:
        raise AssertionError(f"parsed={parsed!r} != expected={expected!r}")

    if spec["canonical"]:
        # Re-encode canonically and compare with the C-emitted input bytes.
        re_encoded = cbor2.dumps(expected, canonical=True)
        if re_encoded != input_bytes:
            raise AssertionError(
                f"canonical re-encoding {re_encoded.hex()} != input "
                f"{input_bytes.hex()}")

    if serialized_bytes is not None:
        # The C side serialized the constructed object; loading those bytes
        # must give an equal value too.
        ser_parsed = strict_loads(serialized_bytes)
        if ser_parsed != expected:
            raise AssertionError(
                f"serialized-file parse {ser_parsed!r} != expected {expected!r}")


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def discover(out_dir: Path, api: str) -> dict[str, tuple[bytes, bytes | None]]:
    """Return {test_name: (input_bytes, serialized_bytes_or_None)} for one API."""
    found: dict[str, tuple[bytes, bytes | None]] = {}
    prefix = f"{api}_"
    for input_path in sorted(out_dir.glob(f"{prefix}*.input.cbor")):
        name = input_path.name[len(prefix):-len(".input.cbor")]
        ser_path = out_dir / f"{prefix}{name}.serialized.cbor"
        ser_bytes = ser_path.read_bytes() if ser_path.exists() else None
        found[name] = (input_path.read_bytes(), ser_bytes)
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=Path("out"),
                        help="directory containing artefacts written by the C tests")
    parser.add_argument("--iterations", type=int, default=1000,
                        help="number of timed iterations per test")
    parser.add_argument("--apis", nargs="+", default=["det", "nondet"],
                        help="which artefact-producing APIs to consume")
    args = parser.parse_args()

    try:
        version = importlib.metadata.version("cbor2")
    except importlib.metadata.PackageNotFoundError:
        version = "unknown"

    feature_summary = ", ".join(
        f"{f}={'yes' if v else 'no'}"
        for f, v in [("immutable", HAS_IMMUTABLE),
                     ("allow_indefinite", HAS_ALLOW_INDEFINITE),
                     ("allow_duplicate_keys", HAS_ALLOW_DUP_KEYS)]
    )
    print(f"cbor2 v{version}; decoder features: {feature_summary}")
    print(f"Reading artefacts from {args.out_dir}")
    print(f"Iterations per test: {args.iterations}")

    if not args.out_dir.exists():
        sys.stderr.write(f"FATAL: --out-dir {args.out_dir} does not exist; "
                         f"run the C test binaries first.\n")
        return 2

    overall_passed = 0
    overall_failed = 0
    overall_skipped = 0
    overall_seconds = 0.0

    for api in args.apis:
        artefacts = discover(args.out_dir, api)
        if not artefacts:
            print(f"\n[{api}] no artefacts found, skipping")
            continue
        print(f"\n[{api}] {len(artefacts)} test(s)")

        api_passed = api_failed = api_skipped = 0
        api_seconds = 0.0

        for name in sorted(artefacts):
            input_bytes, ser_bytes = artefacts[name]
            spec = TESTS.get(name)
            label = f"[{api}] {name:<36} "
            print(label, end="", flush=True)

            if spec is None:
                print("SKIP  (no Python spec)")
                api_skipped += 1
                continue

            # Initial untimed run, mainly to detect TestSkipped before timing.
            try:
                _run_one(input_bytes, ser_bytes, spec,
                         allow_dup_keys_supported=HAS_ALLOW_DUP_KEYS)
            except TestSkipped as why:
                print(f"SKIP  ({why})")
                api_skipped += 1
                continue
            except AssertionError as why:
                print(f"FAIL  {why}")
                api_failed += 1
                continue

            # Timed loop
            t0 = time.perf_counter()
            try:
                for _ in range(args.iterations):
                    _run_one(input_bytes, ser_bytes, spec,
                             allow_dup_keys_supported=HAS_ALLOW_DUP_KEYS)
            except AssertionError as why:
                print(f"FAIL  {why}")
                api_failed += 1
                continue
            seconds = time.perf_counter() - t0
            api_seconds += seconds
            print(f"PASS  {args.iterations} iters in {seconds:.6f}s "
                  f"({seconds / args.iterations:.3e} s/iter)")
            api_passed += 1

        overall_passed += api_passed
        overall_failed += api_failed
        overall_skipped += api_skipped
        overall_seconds += api_seconds
        print(f"[{api}] Summary: {api_passed} passed, "
              f"{api_failed} failed, {api_skipped} skipped; "
              f"total time {api_seconds:.6f}s")

    print(f"\nOverall: {overall_passed} passed, {overall_failed} failed, "
          f"{overall_skipped} skipped; total {overall_seconds:.6f}s")
    return 0 if overall_failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
