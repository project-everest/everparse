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
    const DEPTH: usize = 30;
    let stem = "arr_deeply_nested_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut current: CborNondet<'static> = cbor_nondet_mk_int64(UInt64, 1);
    for _ in 0..DEPTH { current = cbor_nondet_mk_array(leak_arr([current])).unwrap(); }
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
    let expected = cbor_nondet_mk_map(leak_entries::<0>([])).unwrap();
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
    const DEPTH: usize = 10;
    let stem = "map_deeply_nested_canonical";
    let input = read_in(stem);
    let parsed = parse_one(stem, &input);
    let mut current: CborNondet<'static> = cbor_nondet_mk_int64(UInt64, 0);
    for _ in 0..DEPTH {
        let entry = cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64,0), current);
        current = cbor_nondet_mk_map(leak_entries([entry])).unwrap();
    }
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
    let pair1 = cbor_nondet_mk_array(leak_arr([dnm0, dnm0])).unwrap();
    let pair2 = cbor_nondet_mk_array(leak_arr([dnm0, dnm1])).unwrap();
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
    let inner_map_v0 = cbor_nondet_mk_map(leak_entries::<0>([])).unwrap();
    let inner_map_v1 = cbor_nondet_mk_map(leak_entries::<0>([])).unwrap();
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
        cbor_nondet_mk_map(leak_entries::<0>([])).unwrap(), inner_map,
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
