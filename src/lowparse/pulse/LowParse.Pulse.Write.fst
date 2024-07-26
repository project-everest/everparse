module LowParse.Pulse.Write
include LowParse.Pulse.Base
open LowParse.Spec.Base
open LowParse.Pulse.Util
open Pulse.Lib.Slice

module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

inline_for_extraction
let l2r_writer
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x': t') ->
  (#x: Ghost.erased t) ->
  (out: slice byte) ->
  (offset: SZ.t) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (S.pts_to out v ** vmatch x' x ** pure (
      SZ.v offset + Seq.length (bare_serialize s x) <= Seq.length v
    ))
    (fun res -> exists* v' .
      S.pts_to out v' ** vmatch x' x ** pure (
      let bs = bare_serialize s x in
      SZ.v offset + Seq.length bs <= Seq.length v /\
      Seq.length v' == Seq.length v /\
      Seq.slice v' 0 (SZ.v offset) == Seq.slice v 0 (SZ.v offset) /\
      Seq.slice v' (SZ.v offset) (SZ.v offset + Seq.length bs) == bs
    ))

```pulse
fn l2r_writer_ext
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (w: l2r_writer vmatch s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 { forall b . parse p1 b == parse p2 b })
: l2r_writer #t' #t vmatch #k2 #p2 s2
= (x': t')
  (#x: Ghost.erased t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  serializer_unique_strong s1 s2 x;
  w x' out offset
}
```

inline_for_extraction
```pulse
fn l2r_writer_lens
  (#t1' #t2' #t: Type0)
  (vmatch1: t1' -> t -> slprop)
  (vmatch2: t2' -> t -> slprop)
  (lens: (x2': t2') -> (x: Ghost.erased t) -> stt t1'
    (vmatch2 x2' x)
    (fun x1' -> vmatch1 x1' x ** trade (vmatch1 x1' x) (vmatch2 x2' x))
  )
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: l2r_writer vmatch1 s)
: l2r_writer #t2' #t vmatch2 #k #p s
= (x2': t2')
  (#x: Ghost.erased t)
  (out: slice byte)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
{
  let x1' = lens x2' _;
  let res = w x1' out offset;
  elim_trade _ _;
  res
}
```

inline_for_extraction
let compute_remaining_size
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
= (x': t') ->
  (#x: Ghost.erased t) ->
  (out: R.ref SZ.t) ->
  (#v: Ghost.erased SZ.t) ->
  stt bool
    (R.pts_to out v ** vmatch x' x)
    (fun res -> exists* v' .
      R.pts_to out v' ** vmatch x' x ** pure (
      let bs = Seq.length (bare_serialize s x) in
      (res == true <==> bs <= SZ.v v) /\
      (res == true ==> bs + SZ.v v' == SZ.v v)
    ))

inline_for_extraction
```pulse
fn compute_size
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (cr: compute_remaining_size vmatch s)
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
  requires
    (R.pts_to out v ** vmatch x' x)
  returns res: bool
  ensures exists* v' .
      R.pts_to out v' ** vmatch x' x ** pure (
      let bs = Seq.length (bare_serialize s x) in
      (res == true <==> bs <= SZ.v v) /\
      (res == true ==> bs == SZ.v v')
    )
{
  let capacity = !out;
  let res = cr x' out;
  if res {
    let remaining = !out;
    out := SZ.sub capacity remaining;
    true
  } else {
    false
  }
}
```

inline_for_extraction
```pulse
fn compute_remaining_size_ext
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (#s1: serializer p1)
  (cr1: compute_remaining_size vmatch s1)
  (#k2: Ghost.erased parser_kind)
  (#p2: parser k2 t)
  (s2: serializer p2 {
    forall b . parse p1 b == parse p2 b
  })
: compute_remaining_size #t' #t vmatch #k2 #p2 s2
=
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  serializer_unique_strong s1 s2 x;
  cr1 x' out
}
```

inline_for_extraction
```pulse
fn compute_remaining_size_lens
  (#t1' #t2' #t: Type0)
  (vmatch1: t1' -> t -> slprop)
  (vmatch2: t2' -> t -> slprop)
  (lens: (x2': t2') -> (x: Ghost.erased t) -> stt t1'
    (vmatch2 x2' x)
    (fun x1' -> vmatch1 x1' x ** trade (vmatch1 x1' x) (vmatch2 x2' x))
  )
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (w: compute_remaining_size vmatch1 s)
: compute_remaining_size #t2' #t vmatch2 #k #p s
=
  (x2': t2')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  let x1' = lens x2' _;
  let res = w x1' out;
  elim_trade _ _;
  res
}
```

inline_for_extraction
```pulse
fn compute_remaining_size_constant_size
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sz: SZ.t {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == SZ.v sz
  })
: compute_remaining_size #t' #t vmatch #k #p s
=
  (x': t')
  (#x: Ghost.erased t)
  (out: R.ref SZ.t)
  (#v: Ghost.erased SZ.t)
{
  serialize_length s x;
  let capacity = !out;
  if (SZ.lt capacity sz) {
    false
  } else {
    out := SZ.sub capacity sz;
    true
  }
}
```
