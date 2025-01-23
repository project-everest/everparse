module CDDL.Pulse.Parse.Misc
include CDDL.Pulse.Parse.Base
include CDDL.Spec.Misc
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module U64 = FStar.UInt64

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_copyful_uint
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
: impl_copyful_parse #ty vmatch #uint #U64.t #_ spec_uint.parser #_ (rel_pure U64.t)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = cbor_destr_int64 c;
  fold (rel_pure U64.t res res);
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_copyful_nint
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_int64: read_uint64_t vmatch)
: impl_copyful_parse #ty vmatch #nint #U64.t #_ spec_nint.parser #_ (rel_pure U64.t)
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  let res = cbor_destr_int64 c;
  fold (rel_pure U64.t res res);
  res
}
```

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
```pulse
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
```

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
```pulse
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
: impl_copyful_parse #ty vmatch #(Ghost.reveal t) #(Seq.seq U8.t) #(Ghost.reveal ser) (Ghost.reveal par) #_ (rel_vec_or_slice_of_seq true)
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
  let res : vec_or_slice U8.t = Vec w;
  fold (rel_vec_or_slice_of_seq true res vs);
  res
}
```

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_bytes
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
: impl_copyful_parse #ty vmatch #bstr #(Seq.seq U8.t) #_ spec_bstr.parser #_ (rel_vec_or_slice_of_seq true )
= impl_copyful_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_text
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
: impl_copyful_parse #ty vmatch #tstr #(Seq.seq U8.t) #_ spec_tstr.parser #_ (rel_vec_or_slice_of_seq true )
= impl_copyful_bytes_gen cbor_destr_string _ ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_copyful_str_size
    (#ty: Type u#0)
    (#vmatch: perm -> ty -> cbor -> slprop)
    (cbor_destr_string: get_string_t vmatch)
    (mt: Ghost.erased major_type_byte_string_or_text_string)
    (lo hi: Ghost.erased U64.t)
: impl_copyful_parse vmatch (spec_str_size mt lo hi).parser (rel_vec_or_slice_of_seq true)
= impl_copyful_bytes_gen cbor_destr_string _ ()
