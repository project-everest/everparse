module CDDL.Pulse.Serialize.Misc
#lang-pulse
include CDDL.Pulse.Serialize.Base
include CDDL.Spec.Misc
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module I64 = FStar.Int64

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_uint
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
: impl_serialize #_ #_ #_ spec_uint #_ (rel_pure U64.t)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure U64.t c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure U64.t c v);
  let g = Ghost.hide (pack (CInt64 cbor_major_type_uint64 c));
  Cbor.cbor_det_serialize_parse g;
  let x = cbor_mk_int64 cbor_major_type_uint64 c;
  let ser = cbor_det_serialize x out;
  cbor_elim_int64 x;
  match ser {
    None -> {
      0sz
    }
    Some sz -> {
      sz
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_nint
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
: impl_serialize #_ #_ #_ spec_nint #_ (rel_pure U64.t)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure U64.t c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure U64.t c v);
  let g = Ghost.hide (pack (CInt64 cbor_major_type_neg_int64 c));
  Cbor.cbor_det_serialize_parse g;
  let x = cbor_mk_int64 cbor_major_type_neg_int64 c;
  let ser = cbor_det_serialize x out;
  cbor_elim_int64 x;
  match ser {
    None -> {
      0sz
    }
    Some sz -> {
      sz
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_int_range_uint64
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (lo: U64.t)
  (hi: U64.t)
: impl_serialize #_ #_ #_ (spec_int_range_uint64 lo hi) #_ (rel_pure U64.t)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure U64.t c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure U64.t c v);
  if (U64.lte lo c && U64.lte c hi) {
    impl_serialize_uint cbor_det_serialize cbor_mk_int64 cbor_elim_int64 c out
  } else {
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_int_range_int64
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (lo: I64.t)
  (hi: I64.t)
: impl_serialize #_ #_ #_ (spec_int_range_int64 lo hi) #_ (rel_pure I64.t)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure I64.t c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure I64.t c v);
  if (I64.lte lo c && I64.lte c hi) {
    if (I64.lt c 0L) {
      let c' = FStar.Int.Cast.int64_to_uint64 ((-1L) `I64.sub` c);
      fold (rel_pure U64.t c' c');
      let res = impl_serialize_nint cbor_det_serialize cbor_mk_int64 cbor_elim_int64 c' out;
      unfold (rel_pure U64.t c' c');
      res
    } else {
      let c' = FStar.Int.Cast.int64_to_uint64 c;
      fold (rel_pure U64.t c' c');
      let res = impl_serialize_uint cbor_det_serialize cbor_mk_int64 cbor_elim_int64 c' out;
      unfold (rel_pure U64.t c' c');
      res
    }
  } else {
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_int_range_neg_int64
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_int64: mk_int64_t vmatch)
  (cbor_elim_int64: elim_int64_t vmatch)
  (lo: U64.t)
  (hi: U64.t)
: impl_serialize #_ #_ #_ (spec_int_range_neg_int64 lo hi) #_ (rel_pure U64.t)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure U64.t c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure U64.t c v);
  if (U64.lte hi c && U64.lte c lo) {
    impl_serialize_nint cbor_det_serialize cbor_mk_int64 cbor_elim_int64 c out
  } else {
    0sz
  }
}
