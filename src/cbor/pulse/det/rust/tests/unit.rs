
use cborrs::cbordet::*;


#[allow(unused_variables)]
#[test]
fn test1()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x00];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test2()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x01];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test3()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x0a];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,10);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test4()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x17];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,23);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test5()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 2] = [0x18, 0x18];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,24);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 2)).expect("Expected some size to be returned");
  assert!(target_byte_size == 2);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test6()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 2] = [0x18, 0x19];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,25);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 2)).expect("Expected some size to be returned");
  assert!(target_byte_size == 2);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test7()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 2] = [0x18, 0x64];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,100);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 2)).expect("Expected some size to be returned");
  assert!(target_byte_size == 2);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test8()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 3] = [0x19, 0x03, 0xe8];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1000);
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 3)).expect("Expected some size to be returned");
  assert!(target_byte_size == 3);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test9()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 5] = [0x1a, 0x00, 0x0f, 0x42, 0x40];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1000000);
  let mut target_bytes: [u8; 5] = [0xff; 5];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 5)).expect("Expected some size to be returned");
  assert!(target_byte_size == 5);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 5);
  assert!(&target_bytes[0..5] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test10()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 9] = [0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1000000000000);
  let mut target_bytes: [u8; 9] = [0xff; 9];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 9)).expect("Expected some size to be returned");
  assert!(target_byte_size == 9);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 9);
  assert!(&target_bytes[0..9] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test11()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x20];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::NegInt64,0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test12()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x29];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::NegInt64,9);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test13()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 2] = [0x38, 0x63];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::NegInt64,99);
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 2)).expect("Expected some size to be returned");
  assert!(target_byte_size == 2);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test14()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 3] = [0x39, 0x03, 0xe7];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_int64(CborDetIntKind::NegInt64,999);
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 3)).expect("Expected some size to be returned");
  assert!(target_byte_size == 3);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test15()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x60];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("").expect("Expected string short enough");
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test16()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 2] = [0x61, 0x61];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("a").expect("Expected string short enough");
  let mut target_bytes: [u8; 2] = [0xff; 2];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 2)).expect("Expected some size to be returned");
  assert!(target_byte_size == 2);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 2);
  assert!(&target_bytes[0..2] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test17()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 5] = [0x64, 0x49, 0x45, 0x54, 0x46];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("IETF").expect("Expected string short enough");
  let mut target_bytes: [u8; 5] = [0xff; 5];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 5)).expect("Expected some size to be returned");
  assert!(target_byte_size == 5);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 5);
  assert!(&target_bytes[0..5] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test18()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 3] = [0x62, 0x22, 0x5c];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("\"\\").expect("Expected string short enough");
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 3)).expect("Expected some size to be returned");
  assert!(target_byte_size == 3);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test19()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 3] = [0x62, 0xc3, 0xbc];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("ü").expect("Expected string short enough");
  let mut target_bytes: [u8; 3] = [0xff; 3];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 3)).expect("Expected some size to be returned");
  assert!(target_byte_size == 3);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 3);
  assert!(&target_bytes[0..3] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test20()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 4] = [0x63, 0xe6, 0xb0, 0xb4];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("水").expect("Expected string short enough");
  let mut target_bytes: [u8; 4] = [0xff; 4];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 4)).expect("Expected some size to be returned");
  assert!(target_byte_size == 4);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 4);
  assert!(&target_bytes[0..4] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test21()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 5] = [0x64, 0xf0, 0x90, 0x85, 0x91];
  let source_bytes = &source_bytes[..];
  let source_cbor : CborDet = cbor_det_mk_text_string("𐅑").expect("Expected string short enough");
  let mut target_bytes: [u8; 5] = [0xff; 5];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 5)).expect("Expected some size to be returned");
  assert!(target_byte_size == 5);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 5);
  assert!(&target_bytes[0..5] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test22()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0x80];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [CborDet; 0 ] = [dummy_cbor; 0];
  let source_cbor : CborDet = cbor_det_mk_array(&source_cbor_array[..]).expect("Expected an array small enough");
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test23()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 4] = [0x83, 0x01, 0x02, 0x03];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [CborDet; 3 ] = [dummy_cbor; 3];
  let source_cbor_array_2 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,3);
  source_cbor_array[2] = source_cbor_array_2;
  let source_cbor_array_1 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,2);
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1);
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : CborDet = cbor_det_mk_array(&source_cbor_array[..]).expect("Expected an array small enough");
  let mut target_bytes: [u8; 4] = [0xff; 4];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 4)).expect("Expected some size to be returned");
  assert!(target_byte_size == 4);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 4);
  assert!(&target_bytes[0..4] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test24()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 8] = [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [CborDet; 3 ] = [dummy_cbor; 3];
  let mut source_cbor_array_2_array: [CborDet; 2 ] = [dummy_cbor; 2];
  let source_cbor_array_2_array_1 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,5);
  source_cbor_array_2_array[1] = source_cbor_array_2_array_1;
  let source_cbor_array_2_array_0 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,4);
  source_cbor_array_2_array[0] = source_cbor_array_2_array_0;
  let source_cbor_array_2 : CborDet = cbor_det_mk_array(&source_cbor_array_2_array[..]).expect("Expected an array small enough");
  source_cbor_array[2] = source_cbor_array_2;
  let mut source_cbor_array_1_array: [CborDet; 2 ] = [dummy_cbor; 2];
  let source_cbor_array_1_array_1 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,3);
  source_cbor_array_1_array[1] = source_cbor_array_1_array_1;
  let source_cbor_array_1_array_0 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,2);
  source_cbor_array_1_array[0] = source_cbor_array_1_array_0;
  let source_cbor_array_1 : CborDet = cbor_det_mk_array(&source_cbor_array_1_array[..]).expect("Expected an array small enough");
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1);
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : CborDet = cbor_det_mk_array(&source_cbor_array[..]).expect("Expected an array small enough");
  let mut target_bytes: [u8; 8] = [0xff; 8];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 8)).expect("Expected some size to be returned");
  assert!(target_byte_size == 8);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 8);
  assert!(&target_bytes[0..8] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test25()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 29] = [0x98, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [CborDet; 25 ] = [dummy_cbor; 25];
  let source_cbor_array_24 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,25);
  source_cbor_array[24] = source_cbor_array_24;
  let source_cbor_array_23 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,24);
  source_cbor_array[23] = source_cbor_array_23;
  let source_cbor_array_22 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,23);
  source_cbor_array[22] = source_cbor_array_22;
  let source_cbor_array_21 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,22);
  source_cbor_array[21] = source_cbor_array_21;
  let source_cbor_array_20 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,21);
  source_cbor_array[20] = source_cbor_array_20;
  let source_cbor_array_19 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,20);
  source_cbor_array[19] = source_cbor_array_19;
  let source_cbor_array_18 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,19);
  source_cbor_array[18] = source_cbor_array_18;
  let source_cbor_array_17 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,18);
  source_cbor_array[17] = source_cbor_array_17;
  let source_cbor_array_16 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,17);
  source_cbor_array[16] = source_cbor_array_16;
  let source_cbor_array_15 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,16);
  source_cbor_array[15] = source_cbor_array_15;
  let source_cbor_array_14 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,15);
  source_cbor_array[14] = source_cbor_array_14;
  let source_cbor_array_13 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,14);
  source_cbor_array[13] = source_cbor_array_13;
  let source_cbor_array_12 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,13);
  source_cbor_array[12] = source_cbor_array_12;
  let source_cbor_array_11 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,12);
  source_cbor_array[11] = source_cbor_array_11;
  let source_cbor_array_10 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,11);
  source_cbor_array[10] = source_cbor_array_10;
  let source_cbor_array_9 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,10);
  source_cbor_array[9] = source_cbor_array_9;
  let source_cbor_array_8 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,9);
  source_cbor_array[8] = source_cbor_array_8;
  let source_cbor_array_7 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,8);
  source_cbor_array[7] = source_cbor_array_7;
  let source_cbor_array_6 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,7);
  source_cbor_array[6] = source_cbor_array_6;
  let source_cbor_array_5 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,6);
  source_cbor_array[5] = source_cbor_array_5;
  let source_cbor_array_4 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,5);
  source_cbor_array[4] = source_cbor_array_4;
  let source_cbor_array_3 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,4);
  source_cbor_array[3] = source_cbor_array_3;
  let source_cbor_array_2 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,3);
  source_cbor_array[2] = source_cbor_array_2;
  let source_cbor_array_1 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,2);
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1);
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : CborDet = cbor_det_mk_array(&source_cbor_array[..]).expect("Expected an array small enough");
  let mut target_bytes: [u8; 29] = [0xff; 29];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 29)).expect("Expected some size to be returned");
  assert!(target_byte_size == 29);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 29);
  assert!(&target_bytes[0..29] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test26()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 1] = [0xa0];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_map: [CborDetMapEntry; 0 ] = [dummy_cbor_map_entry; 0];
  let source_cbor : CborDet = (cbor_det_mk_map(& mut source_cbor_map[..])).expect("Expected a well-formed map");
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 1)).expect("Expected some size to be returned");
  assert!(target_byte_size == 1);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test27()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 9] = [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_map: [CborDetMapEntry; 2 ] = [dummy_cbor_map_entry; 2];
  let source_cbor_map_1_key : CborDet = cbor_det_mk_text_string("b").expect("Expected string short enough");
  let mut source_cbor_map_1_value_array: [CborDet; 2 ] = [dummy_cbor; 2];
  let source_cbor_map_1_value_array_1 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,3);
  source_cbor_map_1_value_array[1] = source_cbor_map_1_value_array_1;
  let source_cbor_map_1_value_array_0 : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,2);
  source_cbor_map_1_value_array[0] = source_cbor_map_1_value_array_0;
  let source_cbor_map_1_value : CborDet = cbor_det_mk_array(&source_cbor_map_1_value_array[..]).expect("Expected an array small enough");
  source_cbor_map[1] = cbor_det_mk_map_entry(source_cbor_map_1_key, source_cbor_map_1_value);
  let source_cbor_map_0_key : CborDet = cbor_det_mk_text_string("a").expect("Expected string short enough");
  let source_cbor_map_0_value : CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64,1);
  source_cbor_map[0] = cbor_det_mk_map_entry(source_cbor_map_0_key, source_cbor_map_0_value);
  let source_cbor : CborDet = (cbor_det_mk_map(& mut source_cbor_map[..])).expect("Expected a well-formed map");
  let mut target_bytes: [u8; 9] = [0xff; 9];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 9)).expect("Expected some size to be returned");
  assert!(target_byte_size == 9);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 9);
  assert!(&target_bytes[0..9] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test28()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 8] = [0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_array: [CborDet; 2 ] = [dummy_cbor; 2];
  let mut source_cbor_array_1_map: [CborDetMapEntry; 1 ] = [dummy_cbor_map_entry; 1];
  let source_cbor_array_1_map_0_key : CborDet = cbor_det_mk_text_string("b").expect("Expected string short enough");
  let source_cbor_array_1_map_0_value : CborDet = cbor_det_mk_text_string("c").expect("Expected string short enough");
  source_cbor_array_1_map[0] = cbor_det_mk_map_entry(source_cbor_array_1_map_0_key, source_cbor_array_1_map_0_value);
  let source_cbor_array_1 : CborDet = (cbor_det_mk_map(& mut source_cbor_array_1_map[..])).expect("Expected a well-formed map");
  source_cbor_array[1] = source_cbor_array_1;
  let source_cbor_array_0 : CborDet = cbor_det_mk_text_string("a").expect("Expected string short enough");
  source_cbor_array[0] = source_cbor_array_0;
  let source_cbor : CborDet = cbor_det_mk_array(&source_cbor_array[..]).expect("Expected an array small enough");
  let mut target_bytes: [u8; 8] = [0xff; 8];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 8)).expect("Expected some size to be returned");
  assert!(target_byte_size == 8);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 8);
  assert!(&target_bytes[0..8] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
#[allow(unused_variables)]
#[test]
fn test29()
{
  let dummy_cbor: CborDet = cbor_det_mk_int64(CborDetIntKind::UInt64, 0);
  let dummy_cbor_map_entry: CborDetMapEntry = cbor_det_mk_map_entry(dummy_cbor, dummy_cbor);
  let source_bytes: [u8; 21] = [0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43, 0x61, 0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45];
  let source_bytes = &source_bytes[..];
  let mut source_cbor_map: [CborDetMapEntry; 5 ] = [dummy_cbor_map_entry; 5];
  let source_cbor_map_4_key : CborDet = cbor_det_mk_text_string("e").expect("Expected string short enough");
  let source_cbor_map_4_value : CborDet = cbor_det_mk_text_string("E").expect("Expected string short enough");
  source_cbor_map[4] = cbor_det_mk_map_entry(source_cbor_map_4_key, source_cbor_map_4_value);
  let source_cbor_map_3_key : CborDet = cbor_det_mk_text_string("d").expect("Expected string short enough");
  let source_cbor_map_3_value : CborDet = cbor_det_mk_text_string("D").expect("Expected string short enough");
  source_cbor_map[3] = cbor_det_mk_map_entry(source_cbor_map_3_key, source_cbor_map_3_value);
  let source_cbor_map_2_key : CborDet = cbor_det_mk_text_string("c").expect("Expected string short enough");
  let source_cbor_map_2_value : CborDet = cbor_det_mk_text_string("C").expect("Expected string short enough");
  source_cbor_map[2] = cbor_det_mk_map_entry(source_cbor_map_2_key, source_cbor_map_2_value);
  let source_cbor_map_1_key : CborDet = cbor_det_mk_text_string("b").expect("Expected string short enough");
  let source_cbor_map_1_value : CborDet = cbor_det_mk_text_string("B").expect("Expected string short enough");
  source_cbor_map[1] = cbor_det_mk_map_entry(source_cbor_map_1_key, source_cbor_map_1_value);
  let source_cbor_map_0_key : CborDet = cbor_det_mk_text_string("a").expect("Expected string short enough");
  let source_cbor_map_0_value : CborDet = cbor_det_mk_text_string("A").expect("Expected string short enough");
  source_cbor_map[0] = cbor_det_mk_map_entry(source_cbor_map_0_key, source_cbor_map_0_value);
  let source_cbor : CborDet = (cbor_det_mk_map(& mut source_cbor_map[..])).expect("Expected a well-formed map");
  let mut target_bytes: [u8; 21] = [0xff; 21];
  let mut target_byte_size: usize = (cbor_det_size(source_cbor, 21)).expect("Expected some size to be returned");
  assert!(target_byte_size == 21);
  target_byte_size = (cbor_det_serialize (source_cbor, &mut target_bytes[..])).expect("Expected serialization to succeed");
  assert!(target_byte_size == 21);
  assert!(&target_bytes[0..21] == source_bytes);
  let (target_cbor, target_rem) : (CborDet, &[u8]) = (cbor_det_parse(source_bytes)).expect("Expected to parse successfully");
  assert!(target_rem.len () == 0);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}

