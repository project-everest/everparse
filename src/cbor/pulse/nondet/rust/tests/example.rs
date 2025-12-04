use cborrs::cbornondet::*;
use cborrs::cbornondet::CborNondetIntKind::*;
use cborrs::cbornondet::CborNondetView::*;

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
