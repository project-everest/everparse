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
