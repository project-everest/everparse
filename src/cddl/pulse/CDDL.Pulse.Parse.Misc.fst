module CDDL.Pulse.Parse.Misc
#lang-pulse
include CDDL.Pulse.Parse.Base
include CDDL.Spec.Misc
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module U64 = FStar.UInt64

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_uint64_gen
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]ser: Ghost.erased (U64.t -> bool))
    ([@@@erasable]par: Ghost.erased (parser_spec (Ghost.reveal t) U64.t (Ghost.reveal ser)))
    ([@@@erasable]sq: squash (
      forall (x: cbor) . Ghost.reveal t x ==> (CInt64? (unpack x) /\ (Ghost.reveal par x <: U64.t) == CInt64?.v (unpack x))
    ))
: impl_copyful_parse #ty vmatch #(Ghost.reveal t) #U64.t #(Ghost.reveal ser) (Ghost.reveal par) #_ (rel_pure U64.t)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = cbor_destr_int64 c;
  fold (rel_pure U64.t res res);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_uint
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
: impl_copyful_parse #ty vmatch #uint #U64.t #_ spec_uint.parser #_ (rel_pure U64.t)
= impl_copyful_uint64_gen cbor_destr_int64 _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_nint
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
: impl_copyful_parse #ty vmatch #nint #U64.t #_ spec_nint.parser #_ (rel_pure U64.t)
= impl_copyful_uint64_gen cbor_destr_int64 _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_int_range_uint64
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
    (lo hi: Ghost.erased U64.t)
: impl_copyful_parse vmatch (spec_int_range_uint64 lo hi).parser (rel_pure U64.t)
= impl_copyful_ext (impl_copyful_uint cbor_destr_int64) (spec_int_range_uint64 lo hi).parser ()

module I64 = FStar.Int64

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_int_range_int64
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_major_type: get_major_type_t vmatch)
    (cbor_destr_int64: read_uint64_t vmatch)
    (lo hi: Ghost.erased I64.t)
: impl_copyful_parse #ty vmatch #(t_int_range (I64.v lo) (I64.v hi)) #I64.t #_ (spec_int_range_int64 lo hi).parser #_ (rel_pure I64.t)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let mt = cbor_get_major_type c;
  let w1 = cbor_destr_int64 c;
  let w2 = uint64_to_int64 w1;
  let res = (if mt = cbor_major_type_neg_int64 then I64.sub (-1L) w2 else w2);
  fold (rel_pure I64.t res res);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_int_range_neg_int64
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
    (lo hi: Ghost.erased U64.t)
: impl_copyful_parse vmatch (spec_int_range_neg_int64 lo hi).parser (rel_pure U64.t)
= impl_copyful_ext (impl_copyful_nint cbor_destr_int64) (spec_int_range_neg_int64 lo hi).parser ()

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module V = Pulse.Lib.Vec
module A = Pulse.Lib.Array

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_bytes_gen
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (#t: Ghost.erased typ)
    (#ser: Ghost.erased (Seq.seq U8.t -> bool))
    (par: Ghost.erased (parser_spec t (Seq.seq U8.t) ser))
    (sq: squash (
      forall (x: cbor) . Ghost.reveal t x ==> (CString? (unpack x) /\ (Ghost.reveal par x <: Seq.seq U8.t) == CString?.v (unpack x))
    ))
: impl_copyful_parse #ty vmatch #(Ghost.reveal t) #(Seq.seq U8.t) #(Ghost.reveal ser) (Ghost.reveal par) #_ (rel_vec_of_seq)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let s = cbor_destr_string c;
  with ps vs . assert (pts_to s #ps vs);
  let len = S.len s;
  S.pts_to_len s;
  let len64 = SZ.sizet_to_uint64 len;
  let v = V.alloc 0uy len;
  V.to_array_pts_to v;
  let s' = S.from_array (V.vec_to_array v) len;
  S.pts_to_len s';
  S.copy s' s;
  Trade.elim _ _; // release s
  S.to_array s';
  V.to_vec_pts_to v;
  let w : vec U8.t = {
    len = len64;
    v = v;
  };
  rewrite (pts_to v vs) as (pts_to w.v vs);
  fold (rel_vec_of_seq w vs);
  w
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_bytes
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
: impl_copyful_parse #ty vmatch #bstr #(Seq.seq U8.t) #_ spec_bstr.parser #_ (rel_vec_of_seq)
= impl_copyful_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_text
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
: impl_copyful_parse #ty vmatch #tstr #(Seq.seq U8.t) #_ spec_tstr.parser #_ (rel_vec_of_seq)
= impl_copyful_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_str_size
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (mt: Ghost.erased major_type_byte_string_or_text_string)
    (lo hi: Ghost.erased U64.t)
: impl_copyful_parse vmatch (spec_str_size mt lo hi).parser (rel_vec_of_seq)
= impl_copyful_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_bytes_gen
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]ser: Ghost.erased (Seq.seq U8.t -> bool))
    ([@@@erasable]par: Ghost.erased (parser_spec t (Seq.seq U8.t) ser))
    ([@@@erasable]sq: squash (
      forall (x: cbor) . Ghost.reveal t x ==> (CString? (unpack x) /\ (Ghost.reveal par x <: Seq.seq U8.t) == CString?.v (unpack x))
    ))
: impl_zero_copy_parse #ty vmatch #(Ghost.reveal t) #(Seq.seq U8.t) #(Ghost.reveal ser) (Ghost.reveal par) #_ (rel_slice_of_seq false)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let s = cbor_destr_string c;
  with ps vs . assert (pts_to s #ps vs);
  let w : slice U8.t = {
    p = ps;
    s = s;
  };
  rewrite each s as w.s;
  fold (rel_slice_of_seq false w vs);
  intro
    (Trade.trade
      (rel_slice_of_seq false w vs)
      (vmatch p c v)
    )
    #(Trade.trade (pts_to w.s #ps vs) (vmatch p c v))
    fn _
  {
    unfold (rel_slice_of_seq false w vs);
    Trade.elim _ _;
  };
  w
}

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_bytes
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
: impl_zero_copy_parse #ty vmatch #bstr #(Seq.seq U8.t) #_ spec_bstr.parser #_ (rel_slice_of_seq false )
= impl_zero_copy_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_text
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
: impl_zero_copy_parse #ty vmatch #tstr #(Seq.seq U8.t) #_ spec_tstr.parser #_ (rel_slice_of_seq false )
= impl_zero_copy_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_zero_copy_str_size
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (mt: Ghost.erased major_type_byte_string_or_text_string)
    (lo hi: Ghost.erased U64.t)
: impl_zero_copy_parse vmatch (spec_str_size mt lo hi).parser (rel_slice_of_seq false)
= impl_zero_copy_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_simple
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_simple: read_simple_value_t vmatch)
: impl_copyful_parse #ty vmatch #t_simple #U8.t #_ (spec_simple).parser #_ (rel_pure U8.t)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = cbor_destr_simple c;
  fold (rel_pure U8.t res res);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_bool
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_simple: read_simple_value_t vmatch)
: impl_copyful_parse #ty vmatch #t_bool #bool #_ (spec_bool).parser #_ (rel_pure bool)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let w = cbor_destr_simple c;
  let res = (w = simple_value_true);
  fold (rel_pure bool res res);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_tagged_some
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
    (tag: Ghost.erased U64.t)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#ser: Ghost.erased (tgt -> bool))
    (#pl: Ghost.erased (parser_spec (Ghost.reveal t) tgt (Ghost.reveal ser)))
    (#implt: Type0)
    (#r: rel implt tgt)
    (ipl: impl_copyful_parse vmatch pl r)
: impl_copyful_parse #ty vmatch #(t_tag (Some (Ghost.reveal tag)) (Ghost.reveal t)) #tgt #(Ghost.reveal ser) (parser_spec_tag_some (Ghost.reveal tag) (Ghost.reveal pl)) #implt r
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let cpl = cbor_get_tagged_payload c;
  let res = ipl cpl;
  Trade.elim _ _; // release cpl
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_tagged_none
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_tagged_tag: get_tagged_tag_t vmatch)
    (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (#ser: Ghost.erased (tgt -> bool))
    (#pl: Ghost.erased (parser_spec (Ghost.reveal t) tgt (Ghost.reveal ser)))
    (#implt: Type0)
    (#r: rel implt tgt)
    (ipl: impl_copyful_parse vmatch pl r)
: impl_copyful_parse #ty vmatch #(t_tag None (Ghost.reveal t)) #(U64.t & tgt) #(serializable_spec_tag_none (Ghost.reveal ser)) (parser_spec_tag_none (Ghost.reveal pl)) #(U64.t & implt) (rel_pair (rel_pure U64.t) r)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let lhs = cbor_get_tagged_tag c;
  let rhs : implt = impl_copyful_tagged_some cbor_get_tagged_payload lhs ipl c;
  with rv . assert (r rhs rv);
  let resv = Ghost.hide (lhs, rv);
  let res = (lhs, rhs);
  rewrite (r rhs rv) as (r (snd res) (snd resv));
  fold (rel_pure U64.t (fst res) (fst resv));
  fold (rel_pair (rel_pure U64.t) r res resv);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_tagged_some
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
    ([@@@erasable]tag: Ghost.erased U64.t)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]ser: Ghost.erased (tgt -> bool))
    (#[@@@erasable]pl: Ghost.erased (parser_spec (Ghost.reveal t) tgt (Ghost.reveal ser)))
    (#implt: Type0)
    (#[@@@erasable]r: rel implt tgt)
    (ipl: impl_zero_copy_parse vmatch pl r)
: impl_zero_copy_parse #ty vmatch #(t_tag (Some (Ghost.reveal tag)) (Ghost.reveal t)) #tgt #(Ghost.reveal ser) (parser_spec_tag_some (Ghost.reveal tag) (Ghost.reveal pl)) #implt r
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let cpl = cbor_get_tagged_payload c;
  let res = ipl cpl;
  Trade.trans _ _ (vmatch p c v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_tagged_none
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_get_tagged_tag: get_tagged_tag_t vmatch)
    (cbor_get_tagged_payload: get_tagged_payload_t vmatch)
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable]ser: Ghost.erased (tgt -> bool))
    (#[@@@erasable]pl: Ghost.erased (parser_spec (Ghost.reveal t) tgt (Ghost.reveal ser)))
    (#implt: Type0)
    (#[@@@erasable]r: rel implt tgt)
    (ipl: impl_zero_copy_parse vmatch pl r)
: impl_zero_copy_parse #ty vmatch #(t_tag None (Ghost.reveal t)) #(U64.t & tgt) #(serializable_spec_tag_none (Ghost.reveal ser)) (parser_spec_tag_none (Ghost.reveal pl)) #(U64.t & implt) (rel_pair (rel_pure U64.t) r)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let lhs = cbor_get_tagged_tag c;
  let rhs : implt = impl_zero_copy_tagged_some cbor_get_tagged_payload lhs ipl c;
  with rv . assert (r rhs rv);
  let resv = Ghost.hide (lhs, rv);
  let res = (lhs, rhs);
  rewrite (r rhs rv) as (r (snd res) (snd resv));
  fold (rel_pure U64.t (fst res) (fst resv));
  fold (rel_pair (rel_pure U64.t) r res resv);
  intro
    (Trade.trade
      (rel_pair (rel_pure U64.t) r res resv)
      (vmatch p c v)
    )
    #(Trade.trade (r rhs rv) (vmatch p c v))
    fn _
  {
    unfold (rel_pair (rel_pure U64.t) r res resv);
    unfold (rel_pure U64.t (fst res) (fst resv));
    rewrite (r (snd res) (snd resv)) as (r rhs rv);
    Trade.elim _ _
  };
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_copyful_det_cbor
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#ty': Type0)
    (#vmatch': perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (cbor_det_parse: cbor_det_parse_t vmatch')
    (#t: Ghost.erased typ)
    (#tgt: Type0)
    (sp: Ghost.erased (spec t tgt true))
    (#implt: Type0)
    (#r: rel implt tgt)
    (ipl: impl_copyful_parse vmatch' (Ghost.reveal sp).parser r)
: impl_copyful_parse #ty vmatch #(bstr_cbor_det (Ghost.reveal t)) #tgt #(spec_bstr_cbor_det (Ghost.reveal sp)).serializable (spec_bstr_cbor_det (Ghost.reveal sp)).parser #implt r
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let cs = cbor_destr_string c;
  with ps s . assert (pts_to cs #ps s);
  Seq.slice_length s;
  let cp = cbor_det_parse cs;
  match cp {
    Some cp_ -> {
      let cp = fst cp_;
      let rem = Ghost.hide (snd cp_);
      unfold (cbor_det_parse_post vmatch' cs ps s (Some (cp, Ghost.reveal rem)));
      unfold (cbor_det_parse_post_some vmatch' cs ps s cp rem);
      Trade.trans _ _ (vmatch p c v);
      with ps vs . assert (vmatch' ps cp vs);
      CBOR.Spec.API.Format.cbor_det_serialize_parse' vs (Seq.slice s (Seq.length (CBOR.Spec.API.Format.cbor_det_serialize vs)) (Seq.length s));
      let res = ipl cp;
      Trade.elim _ _;
      res
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_zero_copy_det_cbor
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (#ty': Type0)
    (#vmatch': perm -> ty' -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (cbor_det_parse: cbor_det_parse_t vmatch')
    (#[@@@erasable]t: Ghost.erased typ)
    (#[@@@erasable]tgt: Type0)
    ([@@@erasable]sp: Ghost.erased (spec t tgt true))
    (#implt: Type0)
    (#[@@@erasable]r: rel implt tgt)
    (ipl: impl_zero_copy_parse vmatch' (Ghost.reveal sp).parser r)
: impl_zero_copy_parse #ty vmatch #(bstr_cbor_det (Ghost.reveal t)) #tgt #(spec_bstr_cbor_det (Ghost.reveal sp)).serializable (spec_bstr_cbor_det (Ghost.reveal sp)).parser #implt r
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let cs = cbor_destr_string c;
  with ps s . assert (pts_to cs #ps s);
  Seq.slice_length s;
  let cp = cbor_det_parse cs;
  match cp {
    Some cp_ -> {
      let cp = fst cp_;
      let rem = Ghost.hide (snd cp_);
      unfold (cbor_det_parse_post vmatch' cs ps s (Some (cp, Ghost.reveal rem)));
      unfold (cbor_det_parse_post_some vmatch' cs ps s cp rem);
      with ps vs . assert (vmatch' ps cp vs);
      Trade.elim_hyp_r (vmatch' ps cp vs) _ _;
      Trade.trans _ _ (vmatch p c v);
      CBOR.Spec.API.Format.cbor_det_serialize_parse' vs (Seq.slice s (Seq.length (CBOR.Spec.API.Format.cbor_det_serialize vs)) (Seq.length s));
      let res = ipl cp;
      Trade.trans _ _ (vmatch p c v);
      res
    }
  }
}

inline_for_extraction
fn impl_zero_copy_any
    (#ty: Type u#0)
    (vmatch: perm -> ty -> cbor -> slprop)
: impl_zero_copy_parse #ty vmatch #any #cbor #(spec_any).serializable (spec_any).parser #(cbor_with_perm ty) (rel_cbor_not_freeable vmatch false)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res : cbor_with_perm ty = {
    c = c;
    p = p;
  };
  rewrite (vmatch p c v) as (vmatch res.p res.c v);
  fold (rel_cbor_not_freeable vmatch false res v);
  intro
    (Trade.trade
      (rel_cbor_not_freeable vmatch false res v)
      (vmatch p c v)
    )
    #emp
    fn _
  {
    unfold (rel_cbor_not_freeable vmatch false res v);
    rewrite (vmatch res.p res.c v) as (vmatch p c v);
  };
  res
}
