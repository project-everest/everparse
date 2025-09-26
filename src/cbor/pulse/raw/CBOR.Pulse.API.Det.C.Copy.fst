module CBOR.Pulse.API.Det.C.Copy
#lang-pulse
friend CBOR.Pulse.API.Det.C
friend CBOR.Pulse.API.Det.Common
friend CBOR.Pulse.API.Det.Type
friend CBOR.Spec.API.Format

module SpecRaw = CBOR.Spec.Raw
module Raw = CBOR.Pulse.Raw.Match
module Trade = Pulse.Lib.Trade.Util
module Copy = CBOR.Pulse.Raw.Copy

let cbor_det_freeable_t = Copy.cbor_freeable

let freeable = Copy.freeable

let cbor_get_from_freeable x = Copy.Mkcbor_freeable?.cbor x

  fn cbor_copy (_: unit)
: cbor_copy_t u#0 u#0 #_ #_ cbor_det_match freeable cbor_get_from_freeable
=
  (c: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_det_match p c v);
  unfold (CBOR.Pulse.API.Det.Common.cbor_det_match p c v);
  let res = Copy.cbor_copy0 c;
  fold (CBOR.Pulse.API.Det.Common.cbor_det_match p c v);
  fold (cbor_det_match p c v);
  Trade.rewrite_with_trade
    (Raw.cbor_match 1.0R res.cbor (SpecRaw.mk_det_raw_cbor v))
    (cbor_det_match 1.0R (cbor_get_from_freeable res) v);
  Trade.trans _ _ (freeable res);
  res
}

let cbor_free _ x = Copy.cbor_free0 x
