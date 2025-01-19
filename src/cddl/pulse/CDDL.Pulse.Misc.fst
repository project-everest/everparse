module CDDL.Pulse.Misc
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

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn impl_always_false
    (#ty: Type u#0)
    (vmatch: perm -> ty -> cbor -> slprop)
: impl_typ u#0 #ty vmatch #None t_always_false
=
    (c: ty)
    (#p: perm)
    (#v: Ghost.erased cbor)
{
  false
}
```

module U64 = FStar.UInt64

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

let _ = SZ.t // FIXME: WHY WHY WHY? Pulse will complain otherwise

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
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
```

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
