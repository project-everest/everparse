//! Conformance tests for the non-deterministic-encoding EverCBOR Rust API.
//! Mirrors tests/det.rs.

use cborrs_nondet::cbornondet::CborNondetIntKind::*;
use cborrs_nondet::cbornondet::CborNondetView::*;
use cborrs_nondet::cbornondet::*;

mod common;

const API: &str = "nondet";
const SER_BUF: usize = 8192;

fn read_in(name: &str) -> Vec<u8> { common::read_input(API, name) }
fn read_ser(name: &str) -> Vec<u8> { common::read_serialized(API, name) }

fn parse_one<'a>(name: &str, bytes: &'a [u8]) -> CborNondet<'a> {
    let (cbor, rem) = cbor_nondet_parse(None, false, bytes)
        .unwrap_or_else(|| panic!("[{API}/{name}] parse failed"));
    assert!(rem.is_empty(), "[{API}/{name}] parse left {} byte(s)", rem.len());
    cbor
}

fn check_serialize_and_roundtrip<'a>(name: &str, expected: CborNondet<'a>, parsed: CborNondet<'a>) {
    let ser = read_ser(name);
    let mut buf = vec![0u8; SER_BUF];
    let n = cbor_nondet_serialize(expected, &mut buf)
        .unwrap_or_else(|| panic!("[{API}/{name}] serialize failed"));
    buf.truncate(n);
    assert_eq!(buf, ser, "[{API}/{name}] Rust-serialized != C-emitted");
    let (reparsed, rem) = cbor_nondet_parse(None, false, &buf)
        .unwrap_or_else(|| panic!("[{API}/{name}] reparse failed"));
    assert!(rem.is_empty());
    assert!(cbor_nondet_equal(reparsed, parsed));
    assert!(cbor_nondet_equal(reparsed, expected));
}

fn leak_arr<const N: usize>(items: [CborNondet<'static>; N]) -> &'static [CborNondet<'static>] {
    Box::leak(Box::new(items)) as &[_]
}
fn leak_entries<const N: usize>(entries: [CborNondetMapEntry<'static>; N]) -> &'static mut [CborNondetMapEntry<'static>] {
    Box::leak(Box::new(entries)) as &mut [_]
}

/// Nondet counterpart of `det.rs::arr_wrap!` — see that file for the
/// rationale. Each `()` token unrolls into a stack-local `let items = [..]`
/// keeping the per-level borrow alive without `Box::leak`.
macro_rules! arr_wrap {
    ($current:ident,) => {};
    ($current:ident, () $($rest:tt)*) => {
        let items = [$current];
        let $current = cbor_nondet_mk_array(&items).unwrap();
        arr_wrap!($current, $($rest)*);
    };
}

/// Nondet counterpart of `det.rs::map_wrap!`.
macro_rules! map_wrap {
    ($current:ident,) => {};
    ($current:ident, () $($rest:tt)*) => {
        let entry = cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64, 0), $current);
        let mut entries = [entry];
        let $current = cbor_nondet_mk_map(&mut entries).unwrap();
        map_wrap!($current, $($rest)*);
    };
}

// ===== Macros =====
macro_rules! int_canonical {
    ($name:ident, $kind:ident, $value:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let input = read_in(stem);
            let parsed = parse_one(stem, &input);
            match cbor_nondet_destruct(parsed) {
                Int64 { kind: $kind, value } => assert_eq!(value, $value),
                _ => panic!("[{API}/{stem}] expected Int64"),
            }
            let expected = cbor_nondet_mk_int64($kind, $value);
            assert!(cbor_nondet_equal(parsed, expected));
            check_serialize_and_roundtrip(stem, expected, parsed);
        }
    };
}
macro_rules! int_nondet { ($name:ident, $kind:ident, $value:expr) => { int_canonical!($name, $kind, $value); }; }

macro_rules! text_canonical {
    ($name:ident, $s:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let s: &str = $s;
            let input = read_in(stem);
            let parsed = parse_one(stem, &input);
            match cbor_nondet_destruct(parsed) {
                TextString { payload } => assert_eq!(payload, s),
                _ => panic!("[{API}/{stem}] expected TextString"),
            }
            let expected = cbor_nondet_mk_text_string(s).unwrap();
            assert!(cbor_nondet_equal(parsed, expected));
            check_serialize_and_roundtrip(stem, expected, parsed);
        }
    };
}
macro_rules! text_nondet { ($name:ident, $s:expr) => { text_canonical!($name, $s); }; }

macro_rules! bstr_canonical {
    ($name:ident, $bytes:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let payload: &[u8] = $bytes;
            let input = read_in(stem);
            let parsed = parse_one(stem, &input);
            match cbor_nondet_destruct(parsed) {
                ByteString { payload: p } => assert_eq!(p, payload),
                _ => panic!("[{API}/{stem}] expected ByteString"),
            }
            let expected = cbor_nondet_mk_byte_string(payload).unwrap();
            assert!(cbor_nondet_equal(parsed, expected));
            check_serialize_and_roundtrip(stem, expected, parsed);
        }
    };
}
macro_rules! bstr_nondet { ($name:ident, $bytes:expr) => { bstr_canonical!($name, $bytes); }; }

macro_rules! simple_canonical {
    ($name:ident, $value:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let input = read_in(stem);
            let parsed = parse_one(stem, &input);
            match cbor_nondet_destruct(parsed) {
                SimpleValue { _0 } => assert_eq!(_0, $value),
                _ => panic!("[{API}/{stem}] expected SimpleValue"),
            }
            let expected = cbor_nondet_mk_simple_value($value).unwrap();
            assert!(cbor_nondet_equal(parsed, expected));
            check_serialize_and_roundtrip(stem, expected, parsed);
        }
    };
}

macro_rules! invalid_test {
    ($name:ident) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let input = read_in(stem);
            assert!(cbor_nondet_parse(None, false, &input).is_none(),
                    "[{API}/{stem}] nondet parser accepted invalid input");
        }
    };
}

/// Walks `parsed` via the nondet iterator API (`CborNondetArray`/
/// `CborNondetMap` IntoIterator impls) and walks `expected` via the
/// random-access accessors. Recurses through containers and tags.
/// Returns true iff structurally equal AND the iterator yields the right
/// shape at every level.
///
/// Note: nondet map iteration order is arbitrary (the iterator yields
/// entries in the parser's internal canonical order, which may differ
/// from the input bytes for non-canonical encodings). The check matches
/// each iterator-yielded key against `expected` via `cbor_nondet_map_get`,
/// so order does not affect the outcome.
fn walk_iter_check<'a>(parsed: CborNondet<'a>, expected: CborNondet<'a>) -> bool {
    match (cbor_nondet_destruct(parsed), cbor_nondet_destruct(expected)) {
        (Int64 { kind: kp, value: vp }, Int64 { kind: ke, value: ve }) => {
            kp == ke && vp == ve
        }
        (ByteString { payload: pp }, ByteString { payload: pe }) => pp == pe,
        (TextString { payload: pp }, TextString { payload: pe }) => pp == pe,
        (SimpleValue { _0: a }, SimpleValue { _0: b }) => a == b,
        (Tagged { tag: tp, payload: pp }, Tagged { tag: te, payload: pe }) => {
            tp == te && walk_iter_check(pp, pe)
        }
        (Array { _0: ap }, Array { _0: ae }) => {
            let lp = cbor_nondet_get_array_length(ap);
            let le = cbor_nondet_get_array_length(ae);
            if lp != le { return false; }
            let mut count = 0u64;
            for item in ap.into_iter() {
                let Some(e_item) = cbor_nondet_get_array_item(ae, count) else {
                    return false;
                };
                if !walk_iter_check(item, e_item) { return false; }
                count += 1;
            }
            count == lp
        }
        (Map { _0: mp }, Map { _0: me }) => {
            let lp = cbor_nondet_get_map_length(mp);
            let le = cbor_nondet_get_map_length(me);
            if lp != le { return false; }
            let mut count = 0u64;
            for entry in mp.into_iter() {
                let k = cbor_nondet_map_entry_key(entry);
                let v = cbor_nondet_map_entry_value(entry);
                let Some(e_v) = cbor_nondet_map_get(me, k) else { return false; };
                if !walk_iter_check(v, e_v) { return false; }
                count += 1;
            }
            count == lp
        }
        _ => false,
    }
}

// ===== Tests (same names as det) =====
int_canonical!(uint_zero_canonical, UInt64, 0);
int_canonical!(uint_one_canonical, UInt64, 1);
int_canonical!(uint_ten_canonical, UInt64, 10);
int_canonical!(uint_small_canonical, UInt64, 23);
int_canonical!(uint_24_canonical, UInt64, 24);
int_canonical!(uint_25_canonical, UInt64, 25);
int_canonical!(uint_one_byte_canonical, UInt64, 100);
int_canonical!(uint_two_byte_canonical, UInt64, 1_000);
int_canonical!(uint_four_byte_canonical, UInt64, 1_000_000);
int_canonical!(uint_eight_byte_canonical, UInt64, 1u64 << 32);
int_canonical!(uint_trillion_canonical, UInt64, 1_000_000_000_000u64);
int_canonical!(neg_minus_one_canonical, NegInt64, 0);
int_canonical!(neg_small_canonical, NegInt64, 9);
int_canonical!(neg_one_byte_canonical, NegInt64, 99);
int_canonical!(neg_two_byte_canonical, NegInt64, 999);
int_nondet!(uint_zero_nondet, UInt64, 0);
int_nondet!(uint_100_nondet, UInt64, 100);
int_nondet!(uint_zero_long_nondet, UInt64, 0);
int_nondet!(neg_minus_one_nondet, NegInt64, 0);
bstr_canonical!(bstr_empty_canonical, &[]);
bstr_canonical!(bstr_short_canonical, &[0xde, 0xad, 0xbe, 0xef]);
bstr_nondet!(bstr_empty_nondet, &[]);
text_canonical!(tstr_empty_canonical, "");
text_canonical!(tstr_a_canonical, "a");
text_canonical!(tstr_hello_canonical, "hello");
text_canonical!(tstr_ietf_canonical, "IETF");
text_canonical!(tstr_escapes_canonical, "\"\\");
text_canonical!(tstr_u_umlaut_canonical, "\u{00fc}");
text_canonical!(tstr_water_canonical, "\u{6c34}");
text_canonical!(tstr_drachma_canonical, "\u{10151}");
text_nondet!(tstr_hello_nondet, "hello");

// ===== Arrays, maps, complex structures =====
#[test]
fn arr_empty_canonical() {
    let stem = "arr_empty_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    match cbor_nondet_destruct(parsed) {
        Array { _0 } => assert_eq!(cbor_nondet_get_array_length(_0), 0),
        _ => panic!("expected empty Array"),
    }
    let expected = cbor_nondet_mk_array(&[]).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_three_canonical() {
    let stem = "arr_three_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items = [cbor_nondet_mk_int64(UInt64,1), cbor_nondet_mk_int64(UInt64,2), cbor_nondet_mk_int64(UInt64,3)];
    let expected = cbor_nondet_mk_array(&items).unwrap();
    match cbor_nondet_destruct(parsed) {
        Array { _0 } => {
            assert_eq!(cbor_nondet_get_array_length(_0), 3);
            for (i, want) in [1u64,2,3].iter().enumerate() {
                let item = cbor_nondet_get_array_item(_0, i as u64).unwrap();
                match cbor_nondet_destruct(item) {
                    Int64 { kind: UInt64, value } => assert_eq!(value, *want),
                    _ => panic!("not uint"),
                }
            }
        }
        _ => panic!("expected Array"),
    }
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_nested_canonical() {
    let stem = "arr_nested_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let inner1_items = [cbor_nondet_mk_int64(UInt64,2), cbor_nondet_mk_int64(UInt64,3)];
    let inner1 = cbor_nondet_mk_array(&inner1_items).unwrap();
    let inner2_items = [cbor_nondet_mk_int64(UInt64,4), cbor_nondet_mk_int64(UInt64,5)];
    let inner2 = cbor_nondet_mk_array(&inner2_items).unwrap();
    let outer_items = [cbor_nondet_mk_int64(UInt64,1), inner1, inner2];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_25_canonical() {
    let stem = "arr_25_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items: Vec<CborNondet<'static>> = (1u64..=25).map(|i| cbor_nondet_mk_int64(UInt64,i)).collect();
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_empty_nondet() {
    let stem = "arr_empty_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let expected = cbor_nondet_mk_array(&[]).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_deeply_nested_canonical() {
    // DEPTH = 30 (must match cbor_tests.c); see arr_wrap! definition.
    let stem = "arr_deeply_nested_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let current = cbor_nondet_mk_int64(UInt64, 1);
    arr_wrap!(current,
        () () () () () () () () () ()
        () () () () () () () () () ()
        () () () () () () () () () ()
    );
    assert!(cbor_nondet_equal(parsed, current));
    check_serialize_and_roundtrip(stem, current, parsed);
}

#[test]
fn arr_2200_deep_canonical() {
    const DEPTH: usize = 2200;
    let stem = "arr_2200_deep_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut current: CborNondet<'static> = cbor_nondet_mk_int64(UInt64, 1);
    for _ in 0..DEPTH { current = cbor_nondet_mk_array(leak_arr([current])).unwrap(); }
    assert!(cbor_nondet_equal(parsed, current));
    check_serialize_and_roundtrip(stem, current, parsed);
}

invalid_test!(arr_2200_deep_truncated_invalid);

#[test]
fn map_empty_canonical() {
    let stem = "map_empty_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut entries: [CborNondetMapEntry<'_>; 0] = [];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_two_canonical() {
    let stem = "map_two_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let v1 = cbor_nondet_mk_byte_string(&[0x01]).unwrap();
    let v2 = cbor_nondet_mk_text_string("ab").unwrap();
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,1), v1),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,2), v2),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_two_nondet() {
    let stem = "map_two_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let v1 = cbor_nondet_mk_byte_string(&[0x01]).unwrap();
    let v2 = cbor_nondet_mk_text_string("ab").unwrap();
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,1), v1),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,2), v2),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_mixed_canonical() {
    let stem = "map_mixed_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let arr_items = [cbor_nondet_mk_int64(UInt64,2), cbor_nondet_mk_int64(UInt64,3)];
    let arr = cbor_nondet_mk_array(&arr_items).unwrap();
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("a").unwrap(), cbor_nondet_mk_int64(UInt64,1)),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("b").unwrap(), arr),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_with_map_canonical() {
    let stem = "arr_with_map_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut inner_entries = [cbor_nondet_mk_map_entry(
        cbor_nondet_mk_text_string("b").unwrap(),
        cbor_nondet_mk_text_string("c").unwrap())];
    let inner = cbor_nondet_mk_map(&mut inner_entries).unwrap();
    let outer_items = [cbor_nondet_mk_text_string("a").unwrap(), inner];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_five_canonical() {
    let stem = "map_five_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("a").unwrap(), cbor_nondet_mk_text_string("A").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("b").unwrap(), cbor_nondet_mk_text_string("B").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("c").unwrap(), cbor_nondet_mk_text_string("C").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("d").unwrap(), cbor_nondet_mk_text_string("D").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("e").unwrap(), cbor_nondet_mk_text_string("E").unwrap()),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_deeply_nested_canonical() {
    // DEPTH = 10 (must match cbor_tests.c); see map_wrap! definition.
    let stem = "map_deeply_nested_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let current = cbor_nondet_mk_int64(UInt64, 0);
    map_wrap!(current, () () () () () () () () () ());
    assert!(cbor_nondet_equal(parsed, current));
    check_serialize_and_roundtrip(stem, current, parsed);
}

#[test]
fn map_nested_keys_canonical() {
    const DEPTH: usize = 3;
    let stem = "map_nested_keys_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    fn dnm(d: usize, x: u64) -> CborNondet<'static> {
        if d == 0 { return cbor_nondet_mk_int64(UInt64, x); }
        let left = dnm(d-1, 2*x);
        let right = dnm(d-1, 2*x+1);
        let entries = leak_entries([
            cbor_nondet_mk_map_entry(left, cbor_nondet_mk_int64(UInt64,0)),
            cbor_nondet_mk_map_entry(right, cbor_nondet_mk_int64(UInt64,1)),
        ]);
        cbor_nondet_mk_map(entries).unwrap()
    }
    let dnm0 = dnm(DEPTH, 0);
    let dnm1 = dnm(DEPTH, 1);
    let pair1_items = [dnm0, dnm0];
    let pair1 = cbor_nondet_mk_array(&pair1_items).unwrap();
    let pair2_items = [dnm0, dnm1];
    let pair2 = cbor_nondet_mk_array(&pair2_items).unwrap();
    let mut outer = [
        cbor_nondet_mk_map_entry(pair1, cbor_nondet_mk_int64(UInt64,0)),
        cbor_nondet_mk_map_entry(pair2, cbor_nondet_mk_int64(UInt64,1)),
    ];
    let expected = cbor_nondet_mk_map(&mut outer).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

invalid_test!(map_dup_key_invalid);
invalid_test!(map_dup_diff_enc_invalid);

#[test]
fn map_qcbor_complex_nondet() {
    let stem = "map_qcbor_complex_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut inner_entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("bytes 1").unwrap(), cbor_nondet_mk_byte_string(&[0x78,0x78,0x78,0x78]).unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("bytes 2").unwrap(), cbor_nondet_mk_byte_string(&[0x79,0x79,0x79,0x79]).unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("another int").unwrap(), cbor_nondet_mk_int64(UInt64,98)),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("text 2").unwrap(), cbor_nondet_mk_text_string("lies, damn lies and statistics").unwrap()),
    ];
    let inner = cbor_nondet_mk_map(&mut inner_entries).unwrap();
    let arr_items = [cbor_nondet_mk_text_string("string1").unwrap(), cbor_nondet_mk_text_string("string2").unwrap()];
    let arr = cbor_nondet_mk_array(&arr_items).unwrap();
    let mut outer = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("first integer").unwrap(), cbor_nondet_mk_int64(UInt64,42)),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("an array of two strings").unwrap(), arr),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("map in a map").unwrap(), inner),
    ];
    let expected = cbor_nondet_mk_map(&mut outer).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn tag_canonical() {
    let stem = "tag_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let payload = cbor_nondet_mk_int64(UInt64, 0);
    let expected = cbor_nondet_mk_tagged(1000, &payload);
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn tag_nondet() {
    let stem = "tag_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let payload = cbor_nondet_mk_int64(UInt64, 0);
    let expected = cbor_nondet_mk_tagged(1000, &payload);
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

simple_canonical!(simple_short_canonical, 16);
simple_canonical!(simple_long_canonical, 100);
invalid_test!(simple_24_invalid);
invalid_test!(invalid_truncated);
invalid_test!(invalid_bstr_short);
invalid_test!(invalid_arr_short);
invalid_test!(invalid_map_short);
invalid_test!(invalid_indefinite);

#[test]
fn arr_int_boundaries_canonical() {
    let stem = "arr_int_boundaries_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let int_values: &[i64] = &[
        i64::MIN,
        -4_294_967_297,-4_294_967_296,-4_294_967_295,-4_294_967_294,
        -2_147_483_648,-2_147_483_647,
        -65_538,-65_537,-65_536,-65_535,-65_534,
        -257,-256,-255,-254,-25,-24,-23,-1,
        0,0,1,22,23,24,25,26,
        254,255,256,257,
        65_534,65_535,65_536,65_537,65_538,
        2_147_483_647,2_147_483_647,2_147_483_648,2_147_483_649,
        4_294_967_294,4_294_967_295,4_294_967_296,4_294_967_297,
        9_223_372_036_854_775_807,
    ];
    let mut items: Vec<CborNondet<'static>> = Vec::with_capacity(int_values.len()+1);
    for v in int_values {
        if *v < 0 { items.push(cbor_nondet_mk_int64(NegInt64, (-1 - *v) as u64)); }
        else      { items.push(cbor_nondet_mk_int64(UInt64, *v as u64)); }
    }
    items.push(cbor_nondet_mk_int64(UInt64, u64::MAX));
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_empties_canonical() {
    let stem = "arr_empties_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut empty1: [CborNondetMapEntry<'_>; 0] = [];
    let mut empty2: [CborNondetMapEntry<'_>; 0] = [];
    let mut empty3: [CborNondetMapEntry<'_>; 0] = [];
    let inner_map_v0 = cbor_nondet_mk_map(&mut empty1).unwrap();
    let inner_map_v1 = cbor_nondet_mk_map(&mut empty2).unwrap();
    let inner_arr_v3 = cbor_nondet_mk_array(&[]).unwrap();
    let mut inner_entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,1), inner_map_v0),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,2), inner_map_v1),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,3), inner_arr_v3),
    ];
    let inner_map = cbor_nondet_mk_map(&mut inner_entries).unwrap();
    let leaf_arr_items = [cbor_nondet_mk_int64(UInt64, 0)];
    let leaf_arr = cbor_nondet_mk_array(&leaf_arr_items).unwrap();
    let outer_inner_items = [
        cbor_nondet_mk_array(&[]).unwrap(), leaf_arr,
        cbor_nondet_mk_map(&mut empty3).unwrap(), inner_map,
    ];
    let outer_inner = cbor_nondet_mk_array(&outer_inner_items).unwrap();
    let outer_items = [cbor_nondet_mk_int64(UInt64,0), cbor_nondet_mk_array(&[]).unwrap(), outer_inner];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

// ===== UTF-8 (table-driven) =====
macro_rules! utf8_test_valid {
    ($name:ident, $bytes:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let input = read_in(stem);
            let payload: &[u8] = $bytes;
            let s: &str = std::str::from_utf8(payload).expect("payload not UTF-8");
            let parsed = parse_one(stem, &input);
            match cbor_nondet_destruct(parsed) {
                TextString { payload: p } => assert_eq!(p, s),
                _ => panic!("[{API}/{stem}] expected TextString"),
            }
            let expected = cbor_nondet_mk_text_string(s).unwrap();
            assert!(cbor_nondet_equal(parsed, expected));
            check_serialize_and_roundtrip(stem, expected, parsed);
        }
    };
}
macro_rules! utf8_test_invalid {
    ($name:ident, $bytes:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let payload: &[u8] = $bytes;
            let stored = read_in(stem);
            assert_eq!(stored, payload);
            assert!(std::str::from_utf8(payload).is_err());
        }
    };
}
include!("utf8_data/nondet.rs");

// ============================================================
//   New tests for branch coverage
// ============================================================

// ----- Major type 0 -----
int_canonical!(uint_uint8_max_canonical, UInt64, 0xff);
int_canonical!(uint_256_canonical, UInt64, 256);
int_canonical!(uint_uint16_max_canonical, UInt64, 0xffff);
int_canonical!(uint_65536_canonical, UInt64, 65536);
int_canonical!(uint_uint32_max_canonical, UInt64, 0xffffffff);
int_canonical!(uint_uint64_max_minus_one_canonical, UInt64, 0xfffffffffffffffe);
int_canonical!(uint_uint64_max_canonical, UInt64, u64::MAX);
int_nondet!(uint_24_two_byte_nondet, UInt64, 24);
int_nondet!(uint_24_four_byte_nondet, UInt64, 24);
int_nondet!(uint_24_eight_byte_nondet, UInt64, 24);
int_nondet!(uint_uint8_max_two_byte_nondet, UInt64, 0xff);
int_nondet!(uint_uint16_max_four_byte_nondet, UInt64, 0xffff);

// ----- Major type 1 -----
int_canonical!(neg_minus_256_canonical, NegInt64, 0xff);
int_canonical!(neg_minus_257_canonical, NegInt64, 0x100);
int_canonical!(neg_minus_65536_canonical, NegInt64, 0xffff);
int_canonical!(neg_minus_65537_canonical, NegInt64, 0x10000);
int_canonical!(neg_minus_2pow32_canonical, NegInt64, 0xffffffff);
int_canonical!(neg_minus_2pow32_minus_one_canonical, NegInt64, 0x100000000);
int_canonical!(neg_min_canonical, NegInt64, u64::MAX);
int_nondet!(neg_minus_one_two_byte_nondet, NegInt64, 0);

// ----- Major type 2 -----
fn bytes_seq(n: usize) -> Vec<u8> { (0..n).map(|i| (i & 0xff) as u8).collect() }
fn make_static_bytes(n: usize) -> &'static [u8] { Box::leak(bytes_seq(n).into_boxed_slice()) }
#[test]
fn bstr_23_canonical() {
    let stem = "bstr_23_canonical";
    let payload = make_static_bytes(23);
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let expected = cbor_nondet_mk_byte_string(payload).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn bstr_24_canonical() {
    let stem = "bstr_24_canonical";
    let payload = make_static_bytes(24);
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let expected = cbor_nondet_mk_byte_string(payload).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn bstr_255_canonical() {
    let stem = "bstr_255_canonical";
    let payload = make_static_bytes(255);
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let expected = cbor_nondet_mk_byte_string(payload).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn bstr_256_canonical() {
    let stem = "bstr_256_canonical";
    let payload = make_static_bytes(256);
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let expected = cbor_nondet_mk_byte_string(payload).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
bstr_nondet!(bstr_short_two_byte_nondet, &[0xde, 0xad, 0xbe, 0xef]);
bstr_nondet!(bstr_short_eight_byte_nondet, &[0xde, 0xad, 0xbe, 0xef]);
invalid_test!(bstr_oversized_invalid);

// ----- Major type 3 -----
fn a_str(n: usize) -> &'static str { Box::leak("a".repeat(n).into_boxed_str()) }
text_canonical!(tstr_23_canonical, a_str(23));
text_canonical!(tstr_24_canonical, a_str(24));
text_canonical!(tstr_255_canonical, a_str(255));
text_canonical!(tstr_256_canonical, a_str(256));
text_nondet!(tstr_a_eight_byte_nondet, "a");
invalid_test!(tstr_oversized_invalid);

// ----- Major type 4 -----
#[test]
fn arr_23_canonical() {
    let stem = "arr_23_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items: Vec<CborNondet<'static>> =
        (0u64..23).map(|i| cbor_nondet_mk_int64(UInt64, i)).collect();
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn arr_24_canonical() {
    let stem = "arr_24_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items: Vec<CborNondet<'static>> =
        (0u64..24).map(|i| cbor_nondet_mk_int64(UInt64, i)).collect();
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn arr_three_one_byte_nondet() {
    let stem = "arr_three_one_byte_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items = [cbor_nondet_mk_int64(UInt64,1), cbor_nondet_mk_int64(UInt64,2), cbor_nondet_mk_int64(UInt64,3)];
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn arr_three_two_byte_nondet() {
    let stem = "arr_three_two_byte_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items = [cbor_nondet_mk_int64(UInt64,1), cbor_nondet_mk_int64(UInt64,2), cbor_nondet_mk_int64(UInt64,3)];
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}
#[test]
fn arr_empty_eight_byte_nondet() {
    let stem = "arr_empty_eight_byte_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let expected = cbor_nondet_mk_array(&[]).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

// ----- Major type 5 -----
#[test]
fn map_two_one_byte_nondet() {
    let stem = "map_two_one_byte_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,1), cbor_nondet_mk_int64(UInt64,1)),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,2), cbor_nondet_mk_int64(UInt64,2)),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_mixed_key_types_canonical() {
    let stem = "map_mixed_key_types_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,1), cbor_nondet_mk_int64(UInt64,0)),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("a").unwrap(), cbor_nondet_mk_int64(UInt64,1)),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

// ----- Major type 6 -----
macro_rules! tag_uint0_canonical {
    ($name:ident, $tag:expr) => {
        #[test]
        fn $name() {
            let stem = stringify!($name);
            let input = read_in(stem);
            let parsed = parse_one(stem, &input);
            let payload = cbor_nondet_mk_int64(UInt64, 0);
            let expected = cbor_nondet_mk_tagged($tag, &payload);
            assert!(cbor_nondet_equal(parsed, expected));
            check_serialize_and_roundtrip(stem, expected, parsed);
        }
    };
}
tag_uint0_canonical!(tag_short_canonical, 6);
tag_uint0_canonical!(tag_short_last_canonical, 19);
tag_uint0_canonical!(tag_one_byte_first_canonical, 99);
tag_uint0_canonical!(tag_one_byte_last_canonical, 200);
tag_uint0_canonical!(tag_two_byte_first_canonical, 257);
tag_uint0_canonical!(tag_two_byte_last_canonical, 65535);
tag_uint0_canonical!(tag_four_byte_first_canonical, 65536);
tag_uint0_canonical!(tag_four_byte_last_canonical, 0xffffffff);
tag_uint0_canonical!(tag_eight_byte_first_canonical, 1u64 << 32);
tag_uint0_canonical!(tag_max_canonical, u64::MAX);

#[test]
fn tag_nested_canonical() {
    let stem = "tag_nested_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let leaf = cbor_nondet_mk_int64(UInt64, 1);
    let mid = cbor_nondet_mk_tagged(5678, &leaf);
    let expected = cbor_nondet_mk_tagged(1234, &mid);
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn tag_array_payload_canonical() {
    let stem = "tag_array_payload_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items = [
        cbor_nondet_mk_int64(UInt64, 1),
        cbor_nondet_mk_int64(UInt64, 2),
        cbor_nondet_mk_int64(UInt64, 3),
    ];
    let arr = cbor_nondet_mk_array(&items).unwrap();
    let expected = cbor_nondet_mk_tagged(99, &arr);
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn tag_inner_nondet() {
    let stem = "tag_inner_nondet";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let inner = cbor_nondet_mk_int64(UInt64, 24);
    let expected = cbor_nondet_mk_tagged(1000, &inner);
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

// ----- Major type 7 -----
simple_canonical!(simple_zero_canonical, 0);
simple_canonical!(simple_19_canonical, 19);
simple_canonical!(simple_32_canonical, 32);
simple_canonical!(simple_99_canonical, 99);
simple_canonical!(simple_254_canonical, 254);
simple_canonical!(simple_255_canonical, 255);
invalid_test!(simple_25_invalid);
invalid_test!(simple_26_invalid);
invalid_test!(simple_27_invalid);
invalid_test!(simple_28_invalid);
invalid_test!(simple_29_invalid);
invalid_test!(simple_30_invalid);
invalid_test!(simple_31_invalid);

// ----- Cross-cutting -----
invalid_test!(empty_buffer_invalid);
invalid_test!(trunc_19_invalid);
invalid_test!(trunc_1a_invalid);
invalid_test!(trunc_1b_invalid);

#[test]
fn trailing_bytes_canonical() {
    let stem = "trailing_bytes_canonical";
    let input = read_in(stem);
    let (cbor, rem) = cbor_nondet_parse(None, false, &input)
        .unwrap_or_else(|| panic!("[{API}/{stem}] parse failed"));
    assert!(!rem.is_empty(),
        "[{API}/{stem}] trailing bytes were unexpectedly consumed");
    let expected = cbor_nondet_mk_int64(UInt64, 0);
    assert!(cbor_nondet_equal(cbor, expected));
}

invalid_test!(break_stop_alone_invalid);
invalid_test!(indef_bstr_invalid);
invalid_test!(indef_tstr_invalid);
invalid_test!(indef_arr_zero_invalid);
invalid_test!(indef_arr_multi_invalid);
invalid_test!(indef_map_invalid);
invalid_test!(reserved_uint_1c_invalid);
invalid_test!(reserved_uint_1d_invalid);
invalid_test!(reserved_uint_1e_invalid);
invalid_test!(reserved_negint_3c_invalid);
invalid_test!(reserved_arr_9c_invalid);
invalid_test!(reserved_map_bc_invalid);
invalid_test!(reserved_tag_dc_invalid);

// ===== Iterator-walk variants =====
//
// Mirror of det.rs's `_iter_canonical` block. Each test reads the C-emitted
// input bytes for the fixture, parses them, builds the expected value
// independently, and invokes `walk_iter_check(parsed, expected)` to exercise
// the nondet iterator API at every level of nesting (in addition to the
// regular equality + round-trip checks).

#[test]
fn arr_wide_deep_canonical() {
    let stem = "arr_wide_deep_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let inners: [[CborNondet<'static>; 3]; 4] = [
        [cbor_nondet_mk_int64(UInt64, 1), cbor_nondet_mk_int64(UInt64, 2),
         cbor_nondet_mk_int64(UInt64, 3)],
        [cbor_nondet_mk_int64(UInt64, 4), cbor_nondet_mk_int64(UInt64, 5),
         cbor_nondet_mk_int64(UInt64, 6)],
        [cbor_nondet_mk_int64(UInt64, 7), cbor_nondet_mk_int64(UInt64, 8),
         cbor_nondet_mk_int64(UInt64, 9)],
        [cbor_nondet_mk_int64(UInt64, 10), cbor_nondet_mk_int64(UInt64, 11),
         cbor_nondet_mk_int64(UInt64, 12)],
    ];
    let i0 = cbor_nondet_mk_array(&inners[0]).unwrap();
    let i1 = cbor_nondet_mk_array(&inners[1]).unwrap();
    let i2 = cbor_nondet_mk_array(&inners[2]).unwrap();
    let i3 = cbor_nondet_mk_array(&inners[3]).unwrap();
    let outer_items = [i0, i1, i2, i3];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_25_iter_canonical() {
    let stem = "arr_25_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items: Vec<CborNondet<'static>> =
        (1u64..=25).map(|i| cbor_nondet_mk_int64(UInt64, i)).collect();
    let expected = cbor_nondet_mk_array(&items).unwrap();
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_nested_iter_canonical() {
    let stem = "arr_nested_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let inner1_items = [cbor_nondet_mk_int64(UInt64, 2), cbor_nondet_mk_int64(UInt64, 3)];
    let inner1 = cbor_nondet_mk_array(&inner1_items).unwrap();
    let inner2_items = [cbor_nondet_mk_int64(UInt64, 4), cbor_nondet_mk_int64(UInt64, 5)];
    let inner2 = cbor_nondet_mk_array(&inner2_items).unwrap();
    let outer_items = [cbor_nondet_mk_int64(UInt64, 1), inner1, inner2];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_deeply_nested_iter_canonical() {
    let stem = "arr_deeply_nested_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let current = cbor_nondet_mk_int64(UInt64, 1);
    arr_wrap!(current,
        () () () () () () () () () ()
        () () () () () () () () () ()
        () () () () () () () () () ()
    );
    assert!(walk_iter_check(parsed, current),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, current));
    check_serialize_and_roundtrip(stem, current, parsed);
}

#[test]
fn arr_empties_iter_canonical() {
    let stem = "arr_empties_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);

    let mut empty1: [CborNondetMapEntry<'_>; 0] = [];
    let mut empty2: [CborNondetMapEntry<'_>; 0] = [];
    let mut empty3: [CborNondetMapEntry<'_>; 0] = [];
    let inner_map_v0 = cbor_nondet_mk_map(&mut empty1).unwrap();
    let inner_map_v1 = cbor_nondet_mk_map(&mut empty2).unwrap();
    let inner_arr_v3 = cbor_nondet_mk_array(&[]).unwrap();
    let mut inner_entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64, 1), inner_map_v0),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64, 2), inner_map_v1),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64, 3), inner_arr_v3),
    ];
    let inner_map = cbor_nondet_mk_map(&mut inner_entries).unwrap();
    let leaf_arr_items = [cbor_nondet_mk_int64(UInt64, 0)];
    let leaf_arr = cbor_nondet_mk_array(&leaf_arr_items).unwrap();
    let outer_inner_items = [
        cbor_nondet_mk_array(&[]).unwrap(), leaf_arr,
        cbor_nondet_mk_map(&mut empty3).unwrap(), inner_map,
    ];
    let outer_inner = cbor_nondet_mk_array(&outer_inner_items).unwrap();
    let outer_items = [cbor_nondet_mk_int64(UInt64, 0),
                       cbor_nondet_mk_array(&[]).unwrap(), outer_inner];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_five_iter_canonical() {
    let stem = "map_five_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut entries = [
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("a").unwrap(),
                                 cbor_nondet_mk_text_string("A").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("b").unwrap(),
                                 cbor_nondet_mk_text_string("B").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("c").unwrap(),
                                 cbor_nondet_mk_text_string("C").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("d").unwrap(),
                                 cbor_nondet_mk_text_string("D").unwrap()),
        cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("e").unwrap(),
                                 cbor_nondet_mk_text_string("E").unwrap()),
    ];
    let expected = cbor_nondet_mk_map(&mut entries).unwrap();
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn map_deeply_nested_iter_canonical() {
    let stem = "map_deeply_nested_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let current = cbor_nondet_mk_int64(UInt64, 0);
    map_wrap!(current, () () () () () () () () () ());
    assert!(walk_iter_check(parsed, current),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, current));
    check_serialize_and_roundtrip(stem, current, parsed);
}

#[test]
fn map_nested_keys_iter_canonical() {
    const DEPTH: usize = 3;
    let stem = "map_nested_keys_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    fn dnm(d: usize, x: u64) -> CborNondet<'static> {
        if d == 0 { return cbor_nondet_mk_int64(UInt64, x); }
        let left = dnm(d - 1, 2 * x);
        let right = dnm(d - 1, 2 * x + 1);
        let entries = leak_entries([
            cbor_nondet_mk_map_entry(left, cbor_nondet_mk_int64(UInt64, 0)),
            cbor_nondet_mk_map_entry(right, cbor_nondet_mk_int64(UInt64, 1)),
        ]);
        cbor_nondet_mk_map(entries).unwrap()
    }
    let dnm0 = dnm(DEPTH, 0);
    let dnm1 = dnm(DEPTH, 1);
    let pair1_items = [dnm0, dnm0];
    let pair1 = cbor_nondet_mk_array(&pair1_items).unwrap();
    let pair2_items = [dnm0, dnm1];
    let pair2 = cbor_nondet_mk_array(&pair2_items).unwrap();
    let mut outer = [
        cbor_nondet_mk_map_entry(pair1, cbor_nondet_mk_int64(UInt64, 0)),
        cbor_nondet_mk_map_entry(pair2, cbor_nondet_mk_int64(UInt64, 1)),
    ];
    let expected = cbor_nondet_mk_map(&mut outer).unwrap();
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn tag_nested_iter_canonical() {
    let stem = "tag_nested_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let leaf = cbor_nondet_mk_int64(UInt64, 1);
    let mid = cbor_nondet_mk_tagged(5678, &leaf);
    let expected = cbor_nondet_mk_tagged(1234, &mid);
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn tag_array_payload_iter_canonical() {
    let stem = "tag_array_payload_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let items = [
        cbor_nondet_mk_int64(UInt64, 1),
        cbor_nondet_mk_int64(UInt64, 2),
        cbor_nondet_mk_int64(UInt64, 3),
    ];
    let arr = cbor_nondet_mk_array(&items).unwrap();
    let expected = cbor_nondet_mk_tagged(99, &arr);
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}

#[test]
fn arr_wide_deep_iter_canonical() {
    let stem = "arr_wide_deep_iter_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let inners: [[CborNondet<'static>; 3]; 4] = [
        [cbor_nondet_mk_int64(UInt64, 1), cbor_nondet_mk_int64(UInt64, 2),
         cbor_nondet_mk_int64(UInt64, 3)],
        [cbor_nondet_mk_int64(UInt64, 4), cbor_nondet_mk_int64(UInt64, 5),
         cbor_nondet_mk_int64(UInt64, 6)],
        [cbor_nondet_mk_int64(UInt64, 7), cbor_nondet_mk_int64(UInt64, 8),
         cbor_nondet_mk_int64(UInt64, 9)],
        [cbor_nondet_mk_int64(UInt64, 10), cbor_nondet_mk_int64(UInt64, 11),
         cbor_nondet_mk_int64(UInt64, 12)],
    ];
    let i0 = cbor_nondet_mk_array(&inners[0]).unwrap();
    let i1 = cbor_nondet_mk_array(&inners[1]).unwrap();
    let i2 = cbor_nondet_mk_array(&inners[2]).unwrap();
    let i3 = cbor_nondet_mk_array(&inners[3]).unwrap();
    let outer_items = [i0, i1, i2, i3];
    let expected = cbor_nondet_mk_array(&outer_items).unwrap();
    assert!(walk_iter_check(parsed, expected),
            "[{API}/{stem}] walk_iter_check failed");
    assert!(cbor_nondet_equal(parsed, expected));
    check_serialize_and_roundtrip(stem, expected, parsed);
}