module CBOR.Pulse.Raw.Format.Nondet
#lang-pulse
friend CBOR.Spec.Raw.Format
module EP = CBOR.Pulse.Raw.EverParse.Format
module EPND = CBOR.Pulse.Raw.EverParse.Nondet.Basic

fn cbor_validate_nondet
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  (pts_to input #pm v)
returns res: SZ.t
ensures
  (pts_to input #pm v ** pure (
    cbor_validate_nondet_post map_key_bound strict_check v res
  ))
{
  assume (pure (SZ.fits_u64));
  let mut poff = 0sz;
  let res = EP.validate_raw_data_item () input poff;
  if (res) {
    let off = !poff;
    let input' = LowParse.Pulse.Base.peek_trade_gen
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item
      input
      0sz
      off;
    admit ()
  } else {
    0sz
  }
}
