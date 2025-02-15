module CBOR.Pulse.API.Det.C.Slice
#lang-pulse
include CBOR.Pulse.API.Det.C
open Pulse.Lib.Pervasives
open CBOR.Spec.Constants

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice.Util
module MS = Pulse.Lib.MutableSlice.Util
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

module SU = Pulse.Lib.Slice.Util
module AP = Pulse.Lib.ArrayPtr
module CAP = Pulse.Lib.ConstArrayPtr

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_validate_from_slice
  (_: unit)
: cbor_det_validate_t
=
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len input;
  let len = S.len input;
  let a = SU.slice_to_arrayptr_intro_trade input;
  let res = cbor_det_validate a len;
  Trade.elim _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_parse_from_slice
  (input: S.slice U8.t) // the length of that slice does not really matter
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    ))
returns res: cbor_det_t
ensures
    (exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == Spec.cbor_det_serialize v'
    ))
{
  S.pts_to_len input;
  let a = SU.slice_to_arrayptr_intro_trade input;
  let res = cbor_det_parse a len;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_parse_valid
  (_: unit)
: cbor_det_parse_valid_t
=
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let len = S.len input;
  S.pts_to_len input;
  Classical.forall_intro cbor_det_parse_aux1;
  let a = SU.slice_to_arrayptr_intro_trade input;
  let res = cbor_det_parse a len;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_parse_full
  (_: unit)
: cbor_det_parse_t u#0 #_ cbor_det_match
= (input: _)
  (#pm: _)
  (#v: _)
{
  CBOR.Pulse.API.Det.Common.cbor_det_parse_full (cbor_det_validate_from_slice ()) (cbor_det_parse_valid ())
    input
}

inline_for_extraction
noextract [@@noextract_to "krml"]
```pulse
fn cbor_det_serialize_full
  (_: unit)
: cbor_det_serialize_t u#0 #_ cbor_det_match
=
  (x: cbor_det_t)
  (output: MS.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  MS.pts_to_len output;
  let slen = MS.len output;
  let len = cbor_det_size x slen;
  if (SZ.gt len 0sz) {
    let out = MS.slice_to_arrayptr_intro output;
    let out' = AP.ghost_split out len;
    let len' = cbor_det_serialize x out len;
    with v1 . assert (pts_to out v1);
    assert (pure (Seq.equal v1 (Spec.cbor_det_serialize y)));
    AP.join out out';
    with v' . assert (pts_to out v');
    Seq.lemma_split v' (SZ.v len');
    MS.slice_to_arrayptr_elim out;
    MS.pts_to_len output;
    assert (pure (Seq.equal (Seq.slice v' 0 (SZ.v len')) (Spec.cbor_det_serialize y)));
    assert (pure (Seq.equal (Seq.slice v' (SZ.v len) (Seq.length v)) (Seq.slice v (SZ.v len) (Seq.length v))));
    Some len'
  } else {
    None #SZ.t
  }
}
```

inline_for_extraction
noextract [@@noextract_to "krml"]
```pulse
fn cbor_det_get_string_as_slice
  (_: unit)
: get_string_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#y: _)
{
  assume (pure (SZ.fits_u64));
  let len = cbor_det_get_string_length () x;
  let a = cbor_det_get_string () x;
  let sl = S.arrayptr_to_slice_intro_trade a (SZ.uint64_to_sizet len);
  Trade.trans _ _ (cbor_det_match p x y);
  sl
}
```
