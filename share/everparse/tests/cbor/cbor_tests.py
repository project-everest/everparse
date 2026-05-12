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


def strict_loads(data: bytes) -> Any:
    """cbor2.loads with the strictest settings supported by the installed version."""
    kwargs: dict[str, Any] = {}
    if HAS_IMMUTABLE:
        kwargs["immutable"] = True
    if HAS_ALLOW_INDEFINITE:
        kwargs["allow_indefinite"] = False
    if HAS_ALLOW_DUP_KEYS:
        kwargs["allow_duplicate_keys"] = False
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
    """Convenience: T(valid=..., expected=lambda: ..., canonical=...)."""
    pass


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
}


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
