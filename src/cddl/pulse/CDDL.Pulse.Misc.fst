module CDDL.Pulse.Misc
#lang-pulse
include CDDL.Spec.Misc
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U64 = FStar.UInt64

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_uint
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None uint
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_uint64)
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_neg_int
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None nint
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_neg_int64)
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_uint_range
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (lo hi: U64.t)
: impl_typ u#0 #ty vmatch #None (t_int_range (U64.v lo) (U64.v hi))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let test = impl_uint cbor_get_major_type c;
    if (test) {
      let i = cbor_destr_int64 c;
      (U64.lte lo i && U64.lte i hi)
    } else {
      false
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_neg_int_range
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (lo hi: U64.t)
: impl_typ u#0 #ty vmatch #None (t_int_range ((-1) - U64.v lo) ((-1) - U64.v hi))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let test = impl_neg_int cbor_get_major_type c;
    if (test) {
      let i = cbor_destr_int64 c;
      (U64.lte hi i && U64.lte i lo)
    } else {
      false
    }
}

module I64 = FStar.Int64
module Cast = FStar.Int.Cast

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_int_range
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (lo hi: I64.t)
    (sq: squash (I64.v lo < 0 /\ I64.v hi > 0))
: impl_typ u#0 #ty vmatch #None (t_int_range (I64.v lo) (I64.v hi))
=
      impl_ext
        (impl_t_choice
          (impl_neg_int_range cbor_get_major_type cbor_destr_int64 (Cast.int64_to_uint64 (I64.sub (-1L) lo)) 0uL)
          (impl_uint_range cbor_get_major_type cbor_destr_int64 0uL (Cast.int64_to_uint64 hi))
        )
        _

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_uint_literal
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (n: U64.t)
: impl_typ u#0 #ty vmatch #None (t_uint_literal n)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let is_uint = impl_uint cbor_get_major_type c;
    if (is_uint) {
        let i = cbor_destr_int64 c;
        (i = n)
    } else {
        false
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_neg_int_literal
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (n: U64.t)
: impl_typ u#0 #ty vmatch #None (t_literal (pack (CInt64 cbor_major_type_neg_int64 n)))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let is_uint = impl_neg_int cbor_get_major_type c;
    if (is_uint) {
        let i = cbor_destr_int64 c;
        (i = n)
    } else {
        false
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn with_cbor_literal_int
    (#t: Type0)
    (#vmatch: perm -> t -> cbor -> slprop)
    (mk_int64: mk_int64_t vmatch)
    (elim_int64: elim_int64_t vmatch)
    (k: major_type_uint64_or_neg_int64)
    (x: U64.t)
: with_cbor_literal_t #_ vmatch (pack (CInt64 k x))
= (pre: _)
  (t': _)
  (post: _)
  (cont: _)
{
  let c = mk_int64 k x;
  let res : t' = cont _ c;
  elim_int64 c;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_bytes
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None bytes
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_byte_string)
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_text
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None text
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_text_string)
}

let _ = SZ.t // FIXME: WHY WHY WHY? Pulse will complain otherwise

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_str_size
    (#t: Type u#0)
    (#vmatch: perm -> t -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_string: get_string_t vmatch)
    (ty: major_type_byte_string_or_text_string)
    (lo hi: SZ.t)
: impl_typ u#0 #t vmatch #None (str_size ty (SZ.v lo) (SZ.v hi))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    if (mt = ty) {
        let str = cbor_destr_string c;
        S.pts_to_len str;
        let len = S.len str;
        Trade.elim _ _;
        let z = (lo `SZ.lte` len && len `SZ.lte` hi);
        z
    } else {
        false
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_simple
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
: impl_typ u#0 #ty vmatch #None t_simple
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let mt = cbor_get_major_type c;
    (mt = cbor_major_type_simple_value)
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_simple_literal
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_simple: read_simple_value_t vmatch)
    (x: simple_value)
: impl_typ u#0 #ty vmatch #None (t_literal (pack (CSimple x)))
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
    let test = impl_simple cbor_get_major_type c;
    if (test) {
      let v = cbor_destr_simple c;
      (v = x)
    } else {
      false
    }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn with_cbor_literal_simple
    (#t: Type0)
    (#vmatch: perm -> t -> cbor -> slprop)
    (mk_simple: mk_simple_t vmatch)
    (elim_simple: elim_simple_t vmatch)
    (x: simple_value)
: with_cbor_literal_t #_ vmatch (pack (CSimple x))
= (pre: _)
  (t': _)
  (post: _)
  (cont: _)
{
  let c = mk_simple x;
  let res : t' = cont _ c;
  elim_simple c;
  res
}

[@@CMacro]
let cddl_simple_value_false : simple_value = 20uy
[@@CMacro]
let cddl_simple_value_true : simple_value = 21uy

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_bool
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_simple: read_simple_value_t vmatch)
: impl_typ vmatch t_bool
= impl_t_choice
    (impl_simple_literal cbor_get_major_type cbor_destr_simple cddl_simple_value_false)
    (impl_simple_literal cbor_get_major_type cbor_destr_simple cddl_simple_value_true)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_tagged_some
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_get_tagged_tag: get_tagged_tag_t vmatch)
  (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
  (tag: U64.t)
  (#t: Ghost.erased typ)
  (f: impl_typ vmatch t)
: impl_typ u#0 #_ vmatch #None (t_tag (Some tag) t)
= (c: _)
  (#p: _)
  (#v: _)
{
  let k = cbor_get_major_type c;
  if (k = cbor_major_type_tagged) {
    let tag' = cbor_get_tagged_tag c;
    if (tag = tag') {
      let c' = cbor_get_tagged_payload c;
      let res = f c';
      Trade.elim _ _;
      res
    } else {
      false
    }
  } else {
    false
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_tagged_none
  (#ty: Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
  (#t: Ghost.erased typ)
  (f: impl_typ vmatch t)
: impl_typ u#0 #_ vmatch #None (t_tag None t)
= (c: _)
  (#p: _)
  (#v: _)
{
  let k = cbor_get_major_type c;
  if (k = cbor_major_type_tagged) {
     let c' = cbor_get_tagged_payload c;
     let res = f c';
     Trade.elim _ _;
     res
  } else {
    false
  }
}

inline_for_extraction
fn impl_det_cbor
  (#ty #ty': Type u#0)
  (#vmatch: perm -> ty -> cbor -> slprop)
  (#vmatch': perm -> ty' -> cbor -> slprop)
  (cbor_get_major_type: get_major_type_t vmatch)
  (cbor_destr_string: get_string_t vmatch)
  (cbor_det_parse: cbor_det_parse_t vmatch')
  (#t: Ghost.erased typ)
  (f: impl_typ vmatch' t)
: impl_typ u#0 #_ vmatch #None (bstr_cbor_det t)
= (c: _)
  (#p: _)
  (#v: _)
{
  let test = impl_bytes cbor_get_major_type c;
  if (test) {
    let pl = cbor_destr_string c;
    with pm pv . assert (pts_to pl #pm pv);
    let read = cbor_det_parse pl;
    match read {
      None -> {
        unfold (cbor_det_parse_post vmatch' pl pm pv None);
        CBOR.Spec.API.Format.cbor_det_parse_none_equiv pv;
        Trade.elim _ _;
        false
      }
      Some r -> {
        let res, rem = r;
        unfold (cbor_det_parse_post vmatch' pl pm pv (Some (res, rem)));
        unfold (cbor_det_parse_post_some vmatch' pl pm pv res rem);
        Trade.trans _ _ (vmatch p c v);
        with pres vres . assert (vmatch' pres res vres);
        with prem vrem . assert (pts_to rem #prem vrem);
        CBOR.Spec.API.Format.cbor_det_serialize_parse' vres vrem;
        S.pts_to_len rem;
        if (S.len rem = 0sz) {
          Seq.slice_length pv;
          let tres = f res;
          Trade.elim _ _;
          tres
        } else {
          Trade.elim _ _;
          false
        }
      }
    }
  } else {
    false
  }
}

