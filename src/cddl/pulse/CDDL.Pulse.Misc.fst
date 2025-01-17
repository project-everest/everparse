module CDDL.Pulse.Misc
include CDDL.Spec.Misc
include CDDL.Pulse.Base
open Pulse.Lib.Pervasives
module Trade = Pulse.Lib.Trade.Util
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base

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

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

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
