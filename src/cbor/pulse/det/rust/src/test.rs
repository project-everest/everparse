use crate::cbordet::*;

#[test]
fn test1() {
  let source_bytes: [u8; 1] = [0x00];
  let source_bytes = &source_bytes[..];
  let source_cbor: cbor_raw = cbor_det_mk_int64(cbor_major_type_uint64, 0);
  let mut target_bytes: [u8; 1] = [0xff; 1];
  let mut target_byte_size: usize = 1;
  assert!(target_byte_size == 1);
  target_byte_size = cbor_det_serialize(source_cbor, &mut target_bytes[..]);
  assert!(target_byte_size == 1);
  assert!(&target_bytes[0..1] == source_bytes);
  target_byte_size = cbor_det_validate(source_bytes);
  assert!(target_byte_size == 1);
  let target_cbor: cbor_raw = cbor_det_parse(source_bytes, target_byte_size);
  assert!(cbor_det_equal(source_cbor, target_cbor));
}
