module CDDL.Pulse.Serialize.Misc
#lang-pulse
include CDDL.Pulse.Serialize.Base
include CDDL.Pulse.Misc
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

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_literal_cont
  (#ty: Type u#0)
  (#[@@@erasable] vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (#[@@@erasable] u: Ghost.erased cbor)
  (c: unit)
  ([@@@erasable] v: Ghost.erased unit)
  (out: S.slice U8.t)
: with_cbor_literal_cont_t #_ vmatch u
  (exists* w . rel_unit c v ** pts_to out w)
  SZ.t
    (fun res -> exists* w .
      rel_unit c v ** pts_to out w **
      pure (impl_serialize_post (spec_literal u) v w res)
    )
=
  (pk: _)
  (ck: _)
{
  let res = cbor_det_serialize ck out;
  Cbor.cbor_det_serialize_parse u;
  match res {
    None -> {
      0sz
    }
    Some r -> {
      r
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_literal
  (#ty: Type u#0)
  (#[@@@erasable] vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (#[@@@erasable] u: Ghost.erased cbor)
  (w: with_cbor_literal_t vmatch u)
: impl_serialize #_ #_ #_ (spec_literal u) #_ (rel_unit)
=
  (c: _)
  (#v: _)
  (out: _)
{
  w _ _ _ (impl_serialize_literal_cont cbor_det_serialize c v out)
}

inline_for_extraction noextract [@@noextract_to "krml";
  FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
]
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_bstr
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
  (freeable: Ghost.erased bool)
: impl_serialize #_ #_ #_ spec_bstr #_ (rel_slice_of_seq freeable)
=
  (c: _)
  (#v: _)
  (out: _)
{
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  unfold (rel_slice_of_seq freeable c v);
  S.pts_to_len c.s;
  let len = S.len c.s;
  if (SZ.lte len (SZ.uint64_to_sizet pow2_64_m1)) {
    let g = Ghost.hide (pack (CString cbor_major_type_byte_string v));
    Cbor.cbor_det_serialize_parse g;
    let x = cbor_mk_string cbor_major_type_byte_string c.s;
    let ser = cbor_det_serialize x out;
    Trade.elim _ _;
    fold (rel_slice_of_seq freeable c v);
    match ser {
      None -> {
        0sz
      }
      Some sz -> {
        sz
      }
    }
  } else {
    fold (rel_slice_of_seq freeable c v);
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_tstr
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_utf8_correct: impl_utf8_correct_t)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
  (freeable: Ghost.erased bool)
: impl_serialize #_ #_ #_ spec_tstr #_ (rel_slice_of_seq freeable)
=
  (c: _)
  (#v: _)
  (out: _)
{
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  unfold (rel_slice_of_seq freeable c v);
  S.pts_to_len c.s;
  let len = S.len c.s;
  if (SZ.lte len (SZ.uint64_to_sizet pow2_64_m1)) {
    let correct = cbor_utf8_correct c.s;
    if (correct) {
      let g = Ghost.hide (pack (CString cbor_major_type_text_string v));
      Cbor.cbor_det_serialize_parse g;
      let x = cbor_mk_string cbor_major_type_text_string c.s;
      let ser = cbor_det_serialize x out;
      Trade.elim _ _;
      fold (rel_slice_of_seq freeable c v);
      match ser {
        None -> {
          0sz
        }
        Some sz -> {
          sz
        }
      }
    } else {
      fold (rel_slice_of_seq freeable c v);
      0sz
    }
  } else {
    fold (rel_slice_of_seq freeable c v);
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_str_size
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_utf8_correct: impl_utf8_correct_t)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_string: mk_string_t vmatch)
  (freeable: Ghost.erased bool)
  (mt: major_type_byte_string_or_text_string)
  (lo: U64.t)
  (hi: U64.t)
: impl_serialize #_ #_ #_ (spec_str_size mt lo hi) #_ (rel_slice_of_seq freeable)
=
  (c: _)
  (#v: _)
  (out: _)
{
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  unfold (rel_slice_of_seq freeable c v);
  S.pts_to_len c.s;
  let len = S.len c.s;
  fold (rel_slice_of_seq freeable c v);
  if (SZ.lte (SZ.uint64_to_sizet lo) len && SZ.lte len (SZ.uint64_to_sizet hi)) {
    if (mt = cbor_major_type_byte_string) {
      impl_serialize_bstr cbor_det_serialize cbor_mk_string freeable c out;
    } else {
      impl_serialize_tstr cbor_utf8_correct cbor_det_serialize cbor_mk_string freeable c out;
    }
  } else {
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_simple
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_simple: mk_simple_t vmatch)
  (cbor_elim_simple: elim_simple_t vmatch)
: impl_serialize #_ #_ #_ spec_simple #_ (rel_pure U8.t)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure U8.t c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure U8.t c v);
  if (simple_value_wf c) {
    let g = Ghost.hide (pack (CSimple c));
    Cbor.cbor_det_serialize_parse g;
    let x = cbor_mk_simple c;
    let ser = cbor_det_serialize x out;
    cbor_elim_simple x;
    match ser {
      None -> {
        0sz
      }
      Some sz -> {
        sz
      }
    }
  } else {
    0sz
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_bool
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
  (cbor_mk_simple: mk_simple_t vmatch)
  (cbor_elim_simple: elim_simple_t vmatch)
: impl_serialize #_ #_ #_ spec_bool #_ (rel_pure bool)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_pure bool c v);
  assert (pure (c == Ghost.reveal v)); // FIXME: WHY WHY WHY?
  fold (rel_pure bool c v);
  let c' = c; // FIXME: need `norewrite` on `if`
  if (c') {
    fold (rel_pure U8.t simple_value_true simple_value_true);
    let res = impl_serialize_simple cbor_det_serialize cbor_mk_simple cbor_elim_simple simple_value_true out;
    unfold (rel_pure U8.t simple_value_true simple_value_true);
    res
  } else {
    fold (rel_pure U8.t simple_value_false simple_value_false);
    let res = impl_serialize_simple cbor_det_serialize cbor_mk_simple cbor_elim_simple simple_value_false out;
    unfold (rel_pure U8.t simple_value_false simple_value_false);
    res
  }
}

#push-options "--z3rlimit 32"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_tagged_none
    (cbor_det_serialize_tag: cbor_det_serialize_tag_t)
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize ps1 r1)
: impl_serialize #_ #_ #_ (spec_tag_none ps1) #_ (rel_pair (rel_pure U64.t) r1)
=
    (c: _)
    (#v: _)
    (out: _)
{
  norewrite let (ctag, cpayload) = c;
  Trade.rewrite_with_trade
    (rel_pair (rel_pure U64.t) r1 c v)
    (pure (ctag == fst v) ** r1 cpayload (snd v));
  let tsz = cbor_det_serialize_tag ctag out;
  Classical.forall_intro (Cbor.cbor_det_serialize_tag_correct ctag);
  if (tsz = 0sz) {
    Trade.elim _ _;
    0sz
  } else {
    let (_, out2) = S.split out tsz;
    let psz = i1 cpayload out2;
    S.join _ _ out;
    S.pts_to_len out;
    Trade.elim _ _;
    if (psz = 0sz) {
      0sz
    } else {
      (SZ.add tsz psz)
    }
  }
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_tagged_some
    (cbor_det_serialize_tag: cbor_det_serialize_tag_t)
    (tag: U64.t)
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable] inj1: Ghost.erased bool)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 inj1))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize ps1 r1)
: impl_serialize #_ #_ #_ (spec_tag_some tag ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
{
  let c' = (tag, c);
  rel_pair_eq (rel_pure U64.t) r1 tag c tag v;
  rel_pure_eq tag tag;
  Trade.rewrite_with_trade
    (pure (tag == tag) ** r1 c v)
    (rel_pair (rel_pure U64.t) r1 c' (tag, Ghost.reveal v));
  let res = impl_serialize_tagged_none cbor_det_serialize_tag i1 c' out;
  Trade.elim _ _;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_bstr_cbor_det
  (cbor_det_serialize_string: cbor_det_serialize_string_t)
    (#[@@@erasable]t1: Ghost.erased typ)
    (#[@@@erasable]tgt1: Type0)
    (#[@@@erasable]ps1: Ghost.erased (spec t1 tgt1 true))
    (#impl_tgt1: Type0)
    (#[@@@erasable]r1: rel impl_tgt1 tgt1)
    (i1: impl_serialize ps1 r1)
: impl_serialize #_ #_ #_ (spec_bstr_cbor_det ps1) #_ r1
=
    (c: _)
    (#v: _)
    (out: _)
{
  Classical.forall_intro (Classical.move_requires (Cbor.cbor_det_serialize_string_length_gt cbor_major_type_byte_string));
  let _ : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let sz = i1 c out;
  if (sz = 0sz || SZ.gt sz (SZ.uint64_to_sizet pow2_64_m1)) {
    0sz
  } else {
    cbor_det_serialize_string cbor_major_type_byte_string (SZ.sizet_to_uint64 sz) out;
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_any
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_det_serialize: cbor_det_serialize_t vmatch)
: impl_serialize #_ #_ #_ spec_any #_ (rel_cbor_not_freeable vmatch false)
=
  (c: _)
  (#v: _)
  (out: _)
{
  unfold (rel_cbor_not_freeable vmatch false c v);
  let ser = cbor_det_serialize c.c out;
  Cbor.cbor_det_serialize_parse v;  
  fold (rel_cbor_not_freeable vmatch false c v);
  match ser {
    None -> {
      0sz
    }
    Some sz -> {
      sz
    }
  }
}
