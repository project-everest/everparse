use cborrs_nondet::cbornondet::*;
use cborrs_nondet::cbornondet::CborNondetIntKind::*;
use cborrs_nondet::cbornondet::CborNondetView::*;

#[test]
fn parse_bounded()
{
    let input = [0xa1, 0x00, 0xa1, 0x01, 0x02, 0xff];
    let parsed: Option<(CborNondet<'_>, &[u8])> =
        cbor_nondet_parse_bounded(2, 1, &input);
    let (object, rem) = parsed.unwrap();
    let Map { _0: map } = cbor_nondet_destruct(object) else { panic!("Map expected!"); };
    assert!(cbor_nondet_get_map_length(map) == 1);
    assert_eq!(rem, &input[5..]);
    assert!(cbor_nondet_parse_bounded(1, 1, &input).is_none());
    assert!(cbor_nondet_parse_bounded(2, 0, &input).is_none());
    assert!(cbor_nondet_parse_bounded(2, 1, &input[..4]).is_none());
    assert!(cbor_nondet_parse_bounded(2, 1, &[]).is_none());
    assert!(cbor_nondet_parse_bounded(0, 0, &[0x00]).is_some());
    assert!(cbor_nondet_parse_bounded(1, 0, &[0xa0]).is_some());

    let nested_map = [0xa1, 0x00, 0xa2, 0x01, 0x02, 0x03, 0x04];
    assert!(cbor_nondet_parse_bounded(2, 1, &nested_map).is_none());
    assert!(cbor_nondet_parse_bounded(2, 2, &nested_map).is_some());
}

#[test]
fn parse_bounded_sort()
{
    let input = [0xa1, 0x00, 0xa1, 0x01, 0x02, 0xff];
    assert!(cbor_nondet_bounded_sort_scratch_ok(2, 1, 6));
    assert!(!cbor_nondet_bounded_sort_scratch_ok(2, 1, 5));
    assert!(!cbor_nondet_bounded_sort_scratch_ok(usize::MAX, 2, usize::MAX));
    {
        let mut scratch = [0usize; 6];
        let (object, rem) = cbor_nondet_parse_bounded_sort(2, 1, &mut scratch, &input).unwrap();
        let Map { _0: map } = cbor_nondet_destruct(object) else { panic!("Map expected!"); };
        assert!(cbor_nondet_get_map_length(map) == 1);
        assert_eq!(rem, &input[5..]);
    }
    let mut scratch = [0usize; 64];
    assert!(cbor_nondet_parse_bounded_sort(2, 1, &mut scratch[..5], &input).is_none());
    assert!(cbor_nondet_parse_bounded_sort(1, 1, &mut scratch, &input).is_none());
    assert!(cbor_nondet_parse_bounded_sort(2, 0, &mut scratch, &input).is_none());
    assert!(cbor_nondet_parse_bounded_sort(2, 1, &mut scratch, &input[..4]).is_none());
    assert!(cbor_nondet_parse_bounded_sort(0, 0, &mut [], &[0x00]).is_some());

    // the same scratch can be reused while earlier results are alive
    {
        let (o1, _) = cbor_nondet_parse_bounded_sort(2, 1, &mut scratch, &input).unwrap();
        let (o2, _) = cbor_nondet_parse_bounded_sort(2, 1, &mut scratch, &input).unwrap();
        scratch[0] = 0;
        assert!(cbor_nondet_equal(o1, o2));
    }

    // {0: 1, 0: 2}: duplicate keys
    let dup = [0xa2, 0x00, 0x01, 0x00, 0x02];
    assert!(cbor_nondet_parse_bounded_sort(1, 2, &mut scratch, &dup).is_none());
    assert!(cbor_nondet_parse_bounded(1, 2, &dup).is_none());
    // {0: 1, 1: 2}
    let ok = [0xa2, 0x00, 0x01, 0x01, 0x02];
    assert!(cbor_nondet_parse_bounded_sort(1, 2, &mut scratch, &ok).is_some());
    // {{0: 0, 1: 1}: 0, {1: 1, 0: 0}: 1}: equivalent map keys
    let dup_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x00, 0x01];
    assert!(cbor_nondet_parse_bounded_sort(2, 2, &mut scratch, &dup_map_keys).is_none());
    assert!(cbor_nondet_parse_bounded(2, 2, &dup_map_keys).is_none());
    // {{0: 0, 1: 1}: 0, {1: 1, 0: 1}: 1}
    let ok_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x01, 0x01];
    assert!(cbor_nondet_parse_bounded_sort(2, 2, &mut scratch, &ok_map_keys).is_some());
    assert!(cbor_nondet_parse_bounded(2, 2, &ok_map_keys).is_some());
}

#[test]
fn parse_bounded_hash()
{
    let input = [0xa1, 0x00, 0xa1, 0x01, 0x02, 0xff];
    // D = 2, N = 1: scratch >= 3 * 1 * 2 + 1 = 7, hash scratch >= 1
    assert!(cbor_nondet_bounded_hash_scratch_ok(2, 1, 7, 1));
    assert!(!cbor_nondet_bounded_hash_scratch_ok(2, 1, 6, 1));
    assert!(!cbor_nondet_bounded_hash_scratch_ok(2, 1, 7, 0));
    assert!(!cbor_nondet_bounded_hash_scratch_ok(usize::MAX, 2, usize::MAX, usize::MAX));
    for (k0, k1) in [(0, 0), (0x0706050403020100, 0x0f0e0d0c0b0a0908), cbor_nondet_random_hash_key()] {
        {
            let mut scratch = [0usize; 7];
            let mut hscratch = [0u64; 1];
            let (object, rem) = cbor_nondet_parse_bounded_hash(2, 1, k0, k1, &mut scratch, &mut hscratch, &input).unwrap();
            let Map { _0: map } = cbor_nondet_destruct(object) else { panic!("Map expected!"); };
            assert!(cbor_nondet_get_map_length(map) == 1);
            assert_eq!(rem, &input[5..]);
        }
        let mut scratch = [0usize; 64];
        let mut hscratch = [0u64; 8];
        assert!(cbor_nondet_parse_bounded_hash(2, 1, k0, k1, &mut scratch[..6], &mut hscratch, &input).is_none());
        assert!(cbor_nondet_parse_bounded_hash(2, 1, k0, k1, &mut scratch, &mut [], &input).is_none());
        assert!(cbor_nondet_parse_bounded_hash(1, 1, k0, k1, &mut scratch, &mut hscratch, &input).is_none());
        assert!(cbor_nondet_parse_bounded_hash(2, 1, k0, k1, &mut scratch, &mut hscratch, &input[..4]).is_none());
        assert!(cbor_nondet_parse_bounded_hash(0, 0, k0, k1, &mut [], &mut [], &[0x00]).is_some());
        {
            let (o1, _) = cbor_nondet_parse_bounded_hash(2, 1, k0, k1, &mut scratch, &mut hscratch, &input).unwrap();
            let (o2, _) = cbor_nondet_parse_bounded_hash(2, 1, k0, k1, &mut scratch, &mut hscratch, &input).unwrap();
            scratch[0] = 0;
            hscratch[0] = 0;
            assert!(cbor_nondet_equal(o1, o2));
        }
        let dup = [0xa2, 0x00, 0x01, 0x00, 0x02];
        assert!(cbor_nondet_parse_bounded_hash(1, 2, k0, k1, &mut scratch, &mut hscratch, &dup).is_none());
        let ok = [0xa2, 0x00, 0x01, 0x01, 0x02];
        assert!(cbor_nondet_parse_bounded_hash(1, 2, k0, k1, &mut scratch, &mut hscratch, &ok).is_some());
        // {0: 1, 0x1b0000000000000000: 2}: non-minimal duplicate
        let dup_nm = [0xa2, 0x00, 0x01, 0x1b, 0, 0, 0, 0, 0, 0, 0, 0, 0x02];
        assert!(cbor_nondet_parse_bounded_hash(1, 2, k0, k1, &mut scratch, &mut hscratch, &dup_nm).is_none());
        let dup_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x00, 0x01];
        assert!(cbor_nondet_parse_bounded_hash(2, 2, k0, k1, &mut scratch, &mut hscratch, &dup_map_keys).is_none());
        let ok_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x01, 0x01];
        assert!(cbor_nondet_parse_bounded_hash(2, 2, k0, k1, &mut scratch, &mut hscratch, &ok_map_keys).is_some());
    }
    let mut scratch = [0usize; 64];
    let mut hscratch = [0u64; 8];
    let dup_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x00, 0x01];
    assert!(cbor_nondet_parse_bounded_hash_random(2, 2, &mut scratch, &mut hscratch, &dup_map_keys).is_none());
    let ok_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x01, 0x01];
    assert!(cbor_nondet_parse_bounded_hash_random(2, 2, &mut scratch, &mut hscratch, &ok_map_keys).is_some());
}

#[test]
fn parse_bounded_alloc()
{
    let input = [0xa1, 0x00, 0xa1, 0x01, 0x02, 0xff];
    let dup = [0xa2, 0x00, 0x01, 0x00, 0x02];
    let ok = [0xa2, 0x00, 0x01, 0x01, 0x02];
    let dup_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x00, 0x01];
    let ok_map_keys = [0xa2, 0xa2, 0x00, 0x00, 0x01, 0x01, 0x00, 0xa2, 0x01, 0x01, 0x00, 0x01, 0x01];
    type Parse = Box<dyn for<'a> Fn(usize, usize, &'a [u8]) -> Option<(CborNondet<'a>, &'a [u8])>>;
    let parsers: [Parse; 4] = [
        Box::new(cbor_nondet_parse_bounded_sort_alloc),
        Box::new(|d, n, i| cbor_nondet_parse_bounded_hash_alloc(d, n, 0, 0, i)),
        Box::new(|d, n, i| cbor_nondet_parse_bounded_hash_alloc(d, n, 0x0706050403020100, 0x0f0e0d0c0b0a0908, i)),
        Box::new(cbor_nondet_parse_bounded_hash_alloc_random),
    ];
    for parse in parsers.iter() {
        let (object, rem) = parse(2, 1, &input).unwrap();
        let Map { _0: map } = cbor_nondet_destruct(object) else { panic!("Map expected!"); };
        assert!(cbor_nondet_get_map_length(map) == 1);
        assert_eq!(rem, &input[5..]);
        assert!(parse(1, 1, &input).is_none());
        assert!(parse(2, 0, &input).is_none());
        assert!(parse(2, 1, &input[..4]).is_none());
        assert!(parse(0, 0, &[0x00]).is_some());
        assert!(parse(1, 0, &[0xa0]).is_some());
        assert!(parse(1, 2, &dup).is_none());
        assert!(parse(1, 2, &ok).is_some());
        assert!(parse(2, 2, &dup_map_keys).is_none());
        assert!(parse(2, 2, &ok_map_keys).is_some());
        // scratch size overflow
        assert!(parse(usize::MAX, 2, &[0x00]).is_none());
        // allocation failure (3 * 2^44 * 8 bytes exceeds the address space):
        // fails although the input is valid and meets the bounds
        if usize::BITS == 64 && !cfg!(miri) {
            assert!(parse(1, 1 << 44, &[0x00]).is_none());
        }
    }
}

#[test]
fn parse_map_length_bounded()
{
    let input = [0xa1, 0x00, 0xa1, 0x01, 0x02, 0xff];
    for map_key_bound in [None, Some(1)] {
        let parsed: Option<(CborNondet<'_>, &[u8])> =
            cbor_nondet_parse_map_length_bounded(1, map_key_bound, false, &input);
        let (object, rem) = parsed.unwrap();
        let Map { _0: map } = cbor_nondet_destruct(object) else { panic!("Map expected!"); };
        assert!(cbor_nondet_get_map_length(map) == 1);
        assert_eq!(rem, &input[5..]);
        assert!(cbor_nondet_parse_map_length_bounded(0, map_key_bound, false, &input).is_none());
        assert!(cbor_nondet_parse_map_length_bounded(1, map_key_bound, false, &input[..4]).is_none());
        assert!(cbor_nondet_parse_map_length_bounded(1, map_key_bound, false, &[]).is_none());
        assert!(cbor_nondet_parse_map_length_bounded(0, map_key_bound, false, &[0xa0]).is_some());
    }

    let duplicate_keys = [0xa2, 0x00, 0x01, 0x00, 0x02];
    assert!(cbor_nondet_parse_map_length_bounded(2, None, true, &duplicate_keys).is_none());

    let nested_map = [0xa1, 0x00, 0xa2, 0x01, 0x02, 0x03, 0x04];
    assert!(cbor_nondet_parse_map_length_bounded(1, None, false, &nested_map).is_none());
    assert!(cbor_nondet_parse_map_length_bounded(2, None, false, &nested_map).is_some());
}

#[test]
fn test()
{
    // Constructs 3 map entries: ("foo" -> 18), ("bar" -> -1-42), (1729 -> "quux")
    let mut map_entries : [CborNondetMapEntry; 3] =
        [
            cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("foo").unwrap(), cbor_nondet_mk_int64(UInt64, 18)),
            cbor_nondet_mk_map_entry(cbor_nondet_mk_text_string("bar").unwrap(), cbor_nondet_mk_int64(NegInt64, 42)),
            cbor_nondet_mk_map_entry(cbor_nondet_mk_int64(UInt64, 1729), cbor_nondet_mk_text_string("quux").unwrap()),
        ];

    // Constructs an integer object to be used as the payload of a tagged object
    let myint = cbor_nondet_mk_int64(UInt64, 2);

    // Constructs 3 elements, in this order:
    // - the integer object `myint`, tagged with 1234
    // - a byte string
    // - the map whose entries are defined in `map_entries` above
    let array_entries : [CborNondet; 3] =
        [
            cbor_nondet_mk_tagged(1234, & myint),
            cbor_nondet_mk_byte_string(& [18, 42, 17, 29]).unwrap(),
            cbor_nondet_mk_map(& mut map_entries).unwrap()
        ];

    // Constructs an array object whose entries are defined
    // in `array_entries` above
    let test = cbor_nondet_mk_array(&array_entries).unwrap();

    // Test reading from the just-constructed object
    test_on(test);

    // Allocate an output array to serialize our object
    const max_size: usize = 32;
    let mut output_bytes : [u8; max_size] = [0xFF; max_size];

    // Now let's try to serialize our object into a small slice of the
    // output array. It should fail
    assert!(cbor_nondet_serialize(test, & mut output_bytes[0..16]) == None);

    // Now serialize our object into the whole output array (we chose
    // `max_size` to be large enough beforehand)
    let size = cbor_nondet_serialize(test, & mut output_bytes).unwrap();

    // Then, parse our object from the output array, and test reading
    // from it
    let (read, rem) = cbor_nondet_parse(None, false, &output_bytes).unwrap();
    assert!(max_size - rem.len () == size);
    test_on(read);

    // Then, parse our object from only the written slice of the
    // output array, and test reading from it
    let (read, rem) = cbor_nondet_parse(None, false, &output_bytes[0..size]).unwrap();
    assert!(rem.len () == 0);
    test_on(read);
}

/// A test function to walk through the CBOR object we constructed in
/// `test`. It will be called first with the `test` object as
/// constructed, then with a serialization of this object.
fn test_on(test: CborNondet)
{
    // Destruct the just constructed array and check its length
    let Array { _0: a } = cbor_nondet_destruct(test) else { panic!("Array expected!"); };
    assert!(cbor_nondet_get_array_length(a) == 3);

    // Get the map, as the array element at index 2
    let mymap = cbor_nondet_get_array_item(a, 2).unwrap();
    let Map { _0: m } = cbor_nondet_destruct(mymap) else { panic!("Map expected!"); };

    // Check the map value associated to "bar"
    let bar_value = cbor_nondet_map_get(m, cbor_nondet_mk_text_string("bar").unwrap()).unwrap();
    assert!(cbor_nondet_destruct(bar_value) == Int64 { kind: NegInt64, value: 42 });

    // Alternatively, check with the cbornondet equality comparison
    assert!(cbor_nondet_equal(bar_value, cbor_nondet_mk_int64(NegInt64, 42)));
}
