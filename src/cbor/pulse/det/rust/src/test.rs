
use crate::cbordet::*;


#[allow(unused_variables)]
#[test]
fn test1()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x00];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test2()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x01];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test3()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x0a];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,10);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test4()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x17];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,23);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test5()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 2] = [0x18, 0x18];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,24);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 2);
  assert!(target_byte_size == 2);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 2);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test6()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 2] = [0x18, 0x19];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,25);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 2);
  assert!(target_byte_size == 2);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 2);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test7()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 2] = [0x18, 0x64];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,100);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 2);
  assert!(target_byte_size == 2);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 2);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test8()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 3] = [0x19, 0x03, 0xe8];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1000);
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 3);
  assert!(target_byte_size == 3);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 3);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test9()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 5] = [0x1a, 0x00, 0x0f, 0x42, 0x40];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1000000);
  let mut target_bytes: [u8; 5] = [0xff; 5];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 5);
  assert!(target_byte_size == 5);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 5);
  assert!(&target_bytes[0..5] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 5);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test10()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 9] = [0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1000000000000);
  let mut target_bytes: [u8; 9] = [0xff; 9];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 9);
  assert!(target_byte_size == 9);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 9);
  assert!(&target_bytes[0..9] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 9);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test11()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x20];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_neg_int64,0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test12()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x29];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_neg_int64,9);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test13()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 2] = [0x38, 0x63];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_neg_int64,99);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 2);
  assert!(target_byte_size == 2);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 2);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test14()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 3] = [0x39, 0x03, 0xe7];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_int64(cbor_major_type_neg_int64,999);
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 3);
  assert!(target_byte_size == 3);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 3);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test15()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x60];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes(""));
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test16()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 2] = [0x61, 0x61];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("a"));
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 2);
  assert!(target_byte_size == 2);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 2);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test17()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 5] = [0x64, 0x49, 0x45, 0x54, 0x46];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("IETF"));
  let mut target_bytes: [u8; 5] = [0xff; 5];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 5);
  assert!(target_byte_size == 5);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 5);
  assert!(&target_bytes[0..5] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 5);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test18()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 3] = [0x62, 0x22, 0x5c];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("\"\\"));
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 3);
  assert!(target_byte_size == 3);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 3);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test19()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 3] = [0x62, 0xc3, 0xbc];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("ü"));
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 3);
  assert!(target_byte_size == 3);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 3);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test20()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 4] = [0x63, 0xe6, 0xb0, 0xb4];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("水"));
  let mut target_bytes: [u8; 4] = [0xff; 4];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 4);
  assert!(target_byte_size == 4);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 4);
  assert!(&target_bytes[0..4] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 4);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test21()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 5] = [0x64, 0xf0, 0x90, 0x85, 0x91];
  let source_bytes = &source_bytes[..];
  let source_cbor : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("𐅑"));
  let mut target_bytes: [u8; 5] = [0xff; 5];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 5);
  assert!(target_byte_size == 5);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 5);
  assert!(&target_bytes[0..5] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 5);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test22()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0x80];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [cbor_raw; 0 ] = [dummy_cbor; 0];
  let source_cbor : cbor_raw = cbor_det_mk_array(&source_cbor_array[..], 0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test23()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 4] = [0x83, 0x01, 0x02, 0x03];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [cbor_raw; 3 ] = [dummy_cbor; 3];
  let source_cbor_array_2 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,3);
  source_cbor_array[2] = source_cbor_array_2;
  let source_cbor_array_1 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,2);
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1);
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : cbor_raw = cbor_det_mk_array(&source_cbor_array[..], 3);
  let mut target_bytes: [u8; 4] = [0xff; 4];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 4);
  assert!(target_byte_size == 4);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 4);
  assert!(&target_bytes[0..4] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 4);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test24()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 8] = [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [cbor_raw; 3 ] = [dummy_cbor; 3];
  let mut source_cbor_array_2_array: [cbor_raw; 2 ] = [dummy_cbor; 2];
  let source_cbor_array_2_array_1 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,5);
  source_cbor_array_2_array[1] = source_cbor_array_2_array_1;
  let source_cbor_array_2_array_0 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,4);
  source_cbor_array_2_array[0] = source_cbor_array_2_array_0;
  let source_cbor_array_2 : cbor_raw = cbor_det_mk_array(&source_cbor_array_2_array[..], 2);
  source_cbor_array[2] = source_cbor_array_2;
  let mut source_cbor_array_1_array: [cbor_raw; 2 ] = [dummy_cbor; 2];
  let source_cbor_array_1_array_1 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,3);
  source_cbor_array_1_array[1] = source_cbor_array_1_array_1;
  let source_cbor_array_1_array_0 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,2);
  source_cbor_array_1_array[0] = source_cbor_array_1_array_0;
  let source_cbor_array_1 : cbor_raw = cbor_det_mk_array(&source_cbor_array_1_array[..], 2);
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1);
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : cbor_raw = cbor_det_mk_array(&source_cbor_array[..], 3);
  let mut target_bytes: [u8; 8] = [0xff; 8];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 8);
  assert!(target_byte_size == 8);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 8);
  assert!(&target_bytes[0..8] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 8);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test25()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 29] = [0x98, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [cbor_raw; 25 ] = [dummy_cbor; 25];
  let source_cbor_array_24 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,25);
  source_cbor_array[24] = source_cbor_array_24;
  let source_cbor_array_23 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,24);
  source_cbor_array[23] = source_cbor_array_23;
  let source_cbor_array_22 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,23);
  source_cbor_array[22] = source_cbor_array_22;
  let source_cbor_array_21 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,22);
  source_cbor_array[21] = source_cbor_array_21;
  let source_cbor_array_20 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,21);
  source_cbor_array[20] = source_cbor_array_20;
  let source_cbor_array_19 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,20);
  source_cbor_array[19] = source_cbor_array_19;
  let source_cbor_array_18 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,19);
  source_cbor_array[18] = source_cbor_array_18;
  let source_cbor_array_17 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,18);
  source_cbor_array[17] = source_cbor_array_17;
  let source_cbor_array_16 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,17);
  source_cbor_array[16] = source_cbor_array_16;
  let source_cbor_array_15 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,16);
  source_cbor_array[15] = source_cbor_array_15;
  let source_cbor_array_14 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,15);
  source_cbor_array[14] = source_cbor_array_14;
  let source_cbor_array_13 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,14);
  source_cbor_array[13] = source_cbor_array_13;
  let source_cbor_array_12 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,13);
  source_cbor_array[12] = source_cbor_array_12;
  let source_cbor_array_11 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,12);
  source_cbor_array[11] = source_cbor_array_11;
  let source_cbor_array_10 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,11);
  source_cbor_array[10] = source_cbor_array_10;
  let source_cbor_array_9 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,10);
  source_cbor_array[9] = source_cbor_array_9;
  let source_cbor_array_8 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,9);
  source_cbor_array[8] = source_cbor_array_8;
  let source_cbor_array_7 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,8);
  source_cbor_array[7] = source_cbor_array_7;
  let source_cbor_array_6 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,7);
  source_cbor_array[6] = source_cbor_array_6;
  let source_cbor_array_5 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,6);
  source_cbor_array[5] = source_cbor_array_5;
  let source_cbor_array_4 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,5);
  source_cbor_array[4] = source_cbor_array_4;
  let source_cbor_array_3 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,4);
  source_cbor_array[3] = source_cbor_array_3;
  let source_cbor_array_2 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,3);
  source_cbor_array[2] = source_cbor_array_2;
  let source_cbor_array_1 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,2);
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1);
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : cbor_raw = cbor_det_mk_array(&source_cbor_array[..], 25);
  let mut target_bytes: [u8; 29] = [0xff; 29];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 29);
  assert!(target_byte_size == 29);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 29);
  assert!(&target_bytes[0..29] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 29);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test26()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 1] = [0xa0];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_map: [cbor_map_entry; 0 ] = [dummy_cbor_map_entry; 0];
  let source_cbor : cbor_raw = cbor_det_mk_map(& mut source_cbor_map[..], 0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 1);
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test27()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 9] = [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_map: [cbor_map_entry; 2 ] = [dummy_cbor_map_entry; 2];
  let source_cbor_map_1_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("b"));
  let mut source_cbor_map_1_value_array: [cbor_raw; 2 ] = [dummy_cbor; 2];
  let source_cbor_map_1_value_array_1 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,3);
  source_cbor_map_1_value_array[1] = source_cbor_map_1_value_array_1;
  let source_cbor_map_1_value_array_0 : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,2);
  source_cbor_map_1_value_array[0] = source_cbor_map_1_value_array_0;
  let source_cbor_map_1_value : cbor_raw = cbor_det_mk_array(&source_cbor_map_1_value_array[..], 2);
  source_cbor_map[1] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_1_key, cbor_map_entry_value: source_cbor_map_1_value};
  let source_cbor_map_0_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("a"));
  let source_cbor_map_0_value : cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64,1);
  source_cbor_map[0] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_0_key, cbor_map_entry_value: source_cbor_map_0_value};
  let source_cbor : cbor_raw = cbor_det_mk_map(& mut source_cbor_map[..], 2);
  let mut target_bytes: [u8; 9] = [0xff; 9];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 9);
  assert!(target_byte_size == 9);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 9);
  assert!(&target_bytes[0..9] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 9);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test28()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 8] = [0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [cbor_raw; 2 ] = [dummy_cbor; 2];
  let mut source_cbor_array_1_map: [cbor_map_entry; 1 ] = [dummy_cbor_map_entry; 1];
  let source_cbor_array_1_map_0_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("b"));
  let source_cbor_array_1_map_0_value : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("c"));
  source_cbor_array_1_map[0] = cbor_map_entry {cbor_map_entry_key: source_cbor_array_1_map_0_key, cbor_map_entry_value: source_cbor_array_1_map_0_value};
  let source_cbor_array_1 : cbor_raw = cbor_det_mk_map(& mut source_cbor_array_1_map[..], 1);
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("a"));
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : cbor_raw = cbor_det_mk_array(&source_cbor_array[..], 2);
  let mut target_bytes: [u8; 8] = [0xff; 8];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 8);
  assert!(target_byte_size == 8);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 8);
  assert!(&target_bytes[0..8] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 8);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test29()
{
  let dummy_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let dummy_cbor_map_entry: cbor_map_entry = cbor_map_entry { cbor_map_entry_key: dummy_cbor, cbor_map_entry_value: dummy_cbor };
  let source_bytes: [u8; 21] = [0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43, 0x61, 0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_map: [cbor_map_entry; 5 ] = [dummy_cbor_map_entry; 5];
  let source_cbor_map_4_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("e"));
  let source_cbor_map_4_value : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("E"));
  source_cbor_map[4] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_4_key, cbor_map_entry_value: source_cbor_map_4_value};
  let source_cbor_map_3_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("d"));
  let source_cbor_map_3_value : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("D"));
  source_cbor_map[3] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_3_key, cbor_map_entry_value: source_cbor_map_3_value};
  let source_cbor_map_2_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("c"));
  let source_cbor_map_2_value : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("C"));
  source_cbor_map[2] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_2_key, cbor_map_entry_value: source_cbor_map_2_value};
  let source_cbor_map_1_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("b"));
  let source_cbor_map_1_value : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("B"));
  source_cbor_map[1] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_1_key, cbor_map_entry_value: source_cbor_map_1_value};
  let source_cbor_map_0_key : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("a"));
  let source_cbor_map_0_value : cbor_raw = cbor_det_mk_string(cbor_major_type_text_string, str::as_bytes("A"));
  source_cbor_map[0] = cbor_map_entry {cbor_map_entry_key: source_cbor_map_0_key, cbor_map_entry_value: source_cbor_map_0_value};
  let source_cbor : cbor_raw = cbor_det_mk_map(& mut source_cbor_map[..], 5);
  let mut target_bytes: [u8; 21] = [0xff; 21];
  let mut target_byte_size: usize = cbor_det_size(source_cbor, 21);
  assert!(target_byte_size == 21);
  target_byte_size = cbor_det_serialize (source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 21);
  assert!(&target_bytes[0..21] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 21);
  let target_cbor : cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}

