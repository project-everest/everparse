module CBOR.Pulse.API.Det.C.Slice
#lang-pulse
include CBOR.Pulse.API.Det.C
open Pulse.Lib.Pervasives
open CBOR.Spec.Constants

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

module SU = Pulse.Lib.Slice.Util
module AP = Pulse.Lib.ArrayPtr

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
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len output;
  let slen = S.len output;
  let len = cbor_det_size x slen;
  if (SZ.gt len 0sz) {
    let out = S.slice_to_arrayptr_intro output;
    let out' = AP.ghost_split out len;
    let len' = cbor_det_serialize x out len;
    AP.join out out';
    S.slice_to_arrayptr_elim out;
    S.pts_to_len output;
    Some len'
  } else {
    None #SZ.t
  }
}
```
