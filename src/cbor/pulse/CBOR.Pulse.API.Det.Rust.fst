module CBOR.Pulse.API.Det.Rust

module Det = CBOR.Pulse.API.Det.Common

(* Validation, parsing and serialization *)

type cbordet = Det.cbor_det_t

[@@pulse_unfold]
let cbor_det_match = Det.cbor_det_match

open CBOR.Pulse.API.Det.Common

```pulse
fn cbor_det_parse
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (pts_to input #pm v)
returns res: option (cbordet & SZ.t)
ensures
  cbor_det_parse_post input pm v res
{
  let len = cbor_det_validate input;
  if (len = 0sz) {
    fold (cbor_det_parse_post input pm v None);
    None #(cbordet & SZ.t)
  } else {
    let res = Det.cbor_det_parse input len;
    fold (cbor_det_parse_post input pm v (Some (res, len)));
    Some (res, len)
  }
}
```

```pulse
fn cbor_det_size
  (x: cbordet)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (cbor_det_match pm x y)
returns res: option SZ.t
ensures
  cbor_det_match pm x y **
  pure (cbor_det_size_postcond y bound res)
{
  let size = Det.cbor_det_size x bound;
  if (size = 0sz) {
    None #SZ.t
  } else {
    Some size
  }
}
```

```pulse
fn cbor_det_serialize
  (x: cbordet)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
    (cbor_det_match pm x y ** pts_to output v)
returns res: option SZ.t
ensures
    (exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      cbor_det_serialize_postcond y v v' res
    ))
{
  S.pts_to_len output;
  let len = Det.cbor_det_size x (S.len output);
  if (SZ.gt len 0sz) {
    let Mktuple2 out rem = S.split output len;
    S.pts_to_len out;
    let len' = Det.cbor_det_serialize x out;
    S.pts_to_len out;
    S.join out rem output;
    Some len'
  } else {
    None #SZ.t
  }
}
```

(* Constructors *)

```pulse
fn cbor_det_mk_simple_value
  (v: U8.t)
requires emp
returns res: option cbordet
ensures
  cbor_det_mk_simple_value_post v res **
  pure (Some? res <==> simple_value_wf v)
{
  if simple_value_wf v {
    let res = Det.cbor_det_mk_simple_value () v;
    fold (cbor_det_mk_simple_value_post v (Some res));
    Some res
  }
  else {
    fold (cbor_det_mk_simple_value_post v None);
    None #cbordet
  }
}
```

```pulse
fn cbor_det_mk_int64
  (ty: cbor_det_int_kind)
  (v: U64.t)
requires emp
returns res: cbordet
ensures cbor_det_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v))
{
  Det.cbor_det_mk_int64 () (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v
}
```

let uint64_max_prop : squash (pow2 64 - 1 == 18446744073709551615) =
  assert_norm (pow2 64 - 1 == 18446744073709551615)

```pulse
fn cbor_det_mk_string
  (ty: cbor_det_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to s #p v **
  pure (ty == TextString ==> CBOR.Spec.API.UTF8.correct v) // this is true for Rust's str/String
returns res: option cbordet
ensures
  cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v res **
  pure (Some? res <==> FStar.UInt.fits (SZ.v (S.len s)) U64.n)
{
  let sq: squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  if SZ.gt (S.len s) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
    None #cbordet
  } else {
    let res = Det.cbor_det_mk_string () (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s;
    fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v (Some res));
    Some res
  }
}
```

let cbor_det_mk_tagged tag r #pr #v #pv #v' = Det.cbor_det_mk_tagged () tag r #pr #v #pv #v'

let cbor_det_map_entry = Det.cbor_det_map_entry_t

[@@pulse_unfold]
let cbor_det_map_entry_match = Det.cbor_det_map_entry_match

let cbor_det_mk_map_entry xk xv #pk #vk #pv #vv = Det.cbor_det_mk_map_entry () xk xv #pk #vk #pv #vv

```pulse
fn cbor_det_mk_array
  (a: S.slice cbordet)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbordet))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
requires
    pts_to a #pa va **
    PM.seq_list_match va vv (cbor_det_match pv)
returns res: option cbordet
ensures
  cbor_det_mk_array_post a pa va pv vv res **
  pure (Some? res <==> FStar.UInt.fits (SZ.v (S.len a)) U64.n)
{
  let _ : squash SZ.fits_u64 = assume (SZ.fits_u64);
  if SZ.gt (S.len a) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_det_mk_array_post a pa va pv vv None);
    None #cbordet;
  } else {
    let res = Det.cbor_det_mk_array () a;
    fold (cbor_det_mk_array_post a pa va pv vv (Some res));
    Some res
  }
}
```

```pulse
fn cbor_det_mk_map (_: unit) : Base.mk_map_gen_t u#0 #_ #_ cbor_det_match cbor_det_map_entry_match
= (a: _) (#va: _) (#pv: _) (#vv: _)
{
  Det.cbor_det_mk_map_gen () a #va #pv #vv
}
```

(* Destructors *)

let cbor_det_equal x1 x2 #p1 #p2 #v1 #v2 = Det.cbor_det_equal () x1 x2 #p1 #p2 #v1 #v2

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_det_array = {
  array: (array: cbordet { CaseArray? (cbor_det_case array) }) ;
}

let cbor_det_array_match (p: perm) (a: cbor_det_array) (v: Spec.cbor) : Tot slprop =
  cbor_det_match p a.array v **
  pure (Spec.CArray? (Spec.unpack v))

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_det_map = {
  map: (map: cbordet { CaseMap? (cbor_det_case map) });
}

noextract [@@noextract_to "krml"]
let cbor_det_map_match (p: perm) (a: cbor_det_map) (v: Spec.cbor) : Tot slprop =
  cbor_det_match p a.map v **
  pure (Spec.CMap? (Spec.unpack v))

```pulse
fn cbor_det_destruct
  (c: cbordet)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
requires
  cbor_det_match p c v
returns w: cbor_det_view
ensures exists* p' .
  cbor_det_view_match p' w v **
  Trade.trade
    (cbor_det_view_match p' w v)
    (cbor_det_match p c v)
{
  let ty = cbor_det_major_type () c;
  cbor_det_case_correct c;
  if (ty = cbor_major_type_uint64 || ty = cbor_major_type_neg_int64) {
    let k = (if ty = cbor_major_type_uint64 then UInt64 else NegInt64);
    let i = cbor_det_read_uint64 () c;
    fold (cbor_det_view_match p (Int64 k i) v);
    ghost fn aux (_: unit)
      requires cbor_det_match p c v ** cbor_det_view_match p (Int64 k i) v
      ensures cbor_det_match p c v
    {
      unfold (cbor_det_view_match p (Int64 k i) v)
    };
    Trade.intro _ _ _ aux;
    Int64 k i
  }
  else if (ty = cbor_major_type_byte_string || ty = cbor_major_type_text_string) {
    let k = (if ty = cbor_major_type_byte_string then ByteString else TextString);
    let s = cbor_det_get_string () c;
    with p' v' . assert (pts_to s #p' v');
    fold (cbor_det_string_match ty p' s v);
    fold (cbor_det_view_match p' (String k s) v);
    ghost fn aux (_: unit)
    requires emp ** cbor_det_view_match p' (String k s) v
    ensures pts_to s #p' v'
    {
      unfold (cbor_det_view_match p' (String k s) v);
      unfold (cbor_det_string_match ty p' s v);
    };
    Trade.intro _ _ _ aux;
    Trade.trans _ _ (cbor_det_match p c v);
    String k s
  }
  else if (ty = cbor_major_type_array) {
    let res : cbor_det_array = { array = c };
    fold (cbor_det_array_match p res v);
    fold (cbor_det_view_match p (Array res) v);
    ghost fn aux (_: unit)
    requires emp ** cbor_det_view_match p (Array res) v
    ensures cbor_det_match p c v
    {
      unfold (cbor_det_view_match p (Array res) v);
      unfold (cbor_det_array_match p res v);
    };
    Trade.intro _ _ _ aux;
    Array res
  }
  else if (ty = cbor_major_type_map) {
    let res : cbor_det_map = { map = c };
    fold (cbor_det_map_match p res v);
    fold (cbor_det_view_match p (Map res) v);
    ghost fn aux (_: unit)
    requires emp ** cbor_det_view_match p (Map res) v
    ensures cbor_det_match p c v
    {
      unfold (cbor_det_view_match p (Map res) v);
      unfold (cbor_det_map_match p res v);
    };
    Trade.intro _ _ _ aux;
    Map res
  }
  else if (ty = cbor_major_type_tagged) {
    let tag = cbor_det_get_tagged_tag () c;
    let payload = cbor_det_get_tagged_payload () c;
    with p' v' . assert (cbor_det_match p' payload v');
    fold (cbor_det_tagged_match p' tag payload v);
    fold (cbor_det_view_match p' (Tagged tag payload) v);
    ghost fn aux (_: unit)
    requires emp ** cbor_det_view_match p' (Tagged tag payload) v
    ensures cbor_det_match p' payload v'
    {
      unfold (cbor_det_view_match p' (Tagged tag payload) v);
      unfold (cbor_det_tagged_match p' tag payload v);
    };
    Trade.intro _ _ _ aux;
    Trade.trans _ _ (cbor_det_match p c v);
    Tagged tag payload
  }
  else {
    let i = cbor_det_read_simple_value () c;
    fold (cbor_det_view_match p (SimpleValue i) v);
    ghost fn aux (_: unit)
      requires cbor_det_match p c v ** cbor_det_view_match p (SimpleValue i) v
      ensures cbor_det_match p c v
    {
      unfold (cbor_det_view_match p (SimpleValue i) v)
    };
    Trade.intro _ _ _ aux;
    SimpleValue i
  }
}
```

```pulse
fn cbor_det_get_array_length
  (x: cbor_det_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_array_match p x y
returns res: U64.t
ensures
  cbor_det_array_match p x y ** pure (
    get_array_length_post y res
  )
{
  unfold (cbor_det_array_match p x y);
  let res = Det.cbor_det_get_array_length () x.array;
  fold (cbor_det_array_match p x y);
  res
}
```

```pulse
ghost
fn cbor_det_array_match_elim
  (x: cbor_det_array)
  (#p: perm)
  (#y: Spec.cbor)
requires cbor_det_array_match p x y
ensures cbor_det_match p x.array y **
  Trade.trade (cbor_det_match p x.array y) (cbor_det_array_match p x y) **
  pure (Spec.CArray? (Spec.unpack y))
{
  unfold (cbor_det_array_match p x y);
  ghost fn aux (_: unit)
  requires emp ** cbor_det_match p x.array y
  ensures cbor_det_array_match p x y
  {
    fold (cbor_det_array_match p x y);
  };
  Trade.intro _ _ _ aux;
}
```

let cbor_det_array_iterator_t = cbor_det_array_iterator_t

[@@pulse_unfold]
let cbor_det_array_iterator_match = cbor_det_array_iterator_match

```pulse
fn cbor_det_array_iterator_start
  (x: cbor_det_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  (cbor_det_array_match p x y)
returns res: cbor_det_array_iterator_t
ensures
    (exists* p' l' .
      cbor_det_array_iterator_match p' res l' **
      Trade.trade
        (cbor_det_array_iterator_match p' res l')
        (cbor_det_array_match p x y) **
      pure (
        Spec.CArray? (Spec.unpack y) /\
        l' == Spec.CArray?.v (Spec.unpack y)
    ))
{
  cbor_det_array_match_elim x;
  let res = Det.cbor_det_array_iterator_start () x.array;
  Trade.trans _ _ (cbor_det_array_match p x y);
  res
}
```

let cbor_det_array_iterator_is_empty x #p #y = Det.cbor_det_array_iterator_is_empty () x #p #y

let cbor_det_array_iterator_next x #y #py #z = Det.cbor_det_array_iterator_next () x #y #py #z

```pulse
fn cbor_det_get_array_item
  (x: cbor_det_array)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_array_match p x y
returns res: option cbordet
ensures
  safe_get_array_item_post x i p y res
{
  let len = cbor_det_get_array_length x;
  if U64.gte i len {
    fold (safe_get_array_item_post x i p y None);
    None #cbordet
  } else {
    cbor_det_array_match_elim x;
    let res = Det.cbor_det_get_array_item () x.array i;
    Trade.trans _ _ (cbor_det_array_match p x y);
    fold (safe_get_array_item_post x i p y (Some res));
    Some res
  }
}
```

```pulse
fn cbor_det_map_length
  (x: cbor_det_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_map_match p x y
returns res: U64.t
ensures
  cbor_det_map_match p x y ** pure (
    get_map_length_post y res
  )
{
  unfold (cbor_det_map_match p x y);
  let res = Det.cbor_det_get_map_length () x.map;
  fold (cbor_det_map_match p x y);
  res
}
```

```pulse
ghost
fn cbor_det_map_match_elim
  (x: cbor_det_map)
  (#p: perm)
  (#y: Spec.cbor)
requires cbor_det_map_match p x y
ensures cbor_det_match p x.map y **
  Trade.trade (cbor_det_match p x.map y) (cbor_det_map_match p x y) **
  pure (Spec.CMap? (Spec.unpack y))
{
  unfold (cbor_det_map_match p x y);
  ghost fn aux (_: unit)
  requires emp ** cbor_det_match p x.map y
  ensures cbor_det_map_match p x y
  {
    fold (cbor_det_map_match p x y);
  };
  Trade.intro _ _ _ aux;
}
```

let cbor_det_map_iterator_t = Det.cbor_det_map_iterator_t

[@@pulse_unfold]
let cbor_det_map_iterator_match = Det.cbor_det_map_iterator_match

```pulse
fn cbor_det_map_iterator_start
  (x: cbor_det_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  (cbor_det_map_match p x y)
returns res: cbor_det_map_iterator_t
ensures
    (exists* p' l' .
      cbor_det_map_iterator_match p' res l' **
      Trade.trade
        (cbor_det_map_iterator_match p' res l')
        (cbor_det_map_match p x y) **
      pure (
        map_iterator_start_post y l'
    ))
{
  cbor_det_map_match_elim x;
  let res = Det.cbor_det_map_iterator_start () x.map;
  Trade.trans _ _ (cbor_det_map_match p x y);
  res
}
```

let cbor_det_map_iterator_is_empty x #p #y = Det.cbor_det_map_iterator_is_empty () x #p #y

let cbor_det_map_iterator_next x #y #py #z = Det.cbor_det_map_iterator_next () x #y #py #z

let cbor_det_map_entry_key x2 #p #v2 = Det.cbor_det_map_entry_key () x2 #p #v2

let cbor_det_map_entry_value x2 #p #v2 = Det.cbor_det_map_entry_value () x2 #p #v2

```pulse
ghost
fn cbor_det_map_get_post_to_safe
  (x: cbor_det_map)
  (px: perm)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (res: option cbordet)
requires
  map_get_post cbor_det_match x.map px vx vk res **
  Trade.trade (cbor_det_match px x.map vx) (cbor_det_map_match px x vx)
ensures
  safe_map_get_post x px vx vk res
{
  match res {
    None -> {
      unfold (map_get_post cbor_det_match x.map px vx vk None);
      unfold (map_get_post_none cbor_det_match x.map px vx vk);
      Trade.elim _ _;
      fold (safe_map_get_post x px vx vk None);
    }
    Some res' -> {
      unfold (map_get_post cbor_det_match x.map px vx vk (Some res'));
      unfold (map_get_post_some cbor_det_match x.map px vx vk res');
      Trade.trans _ _ (cbor_det_map_match px x vx);
      fold (safe_map_get_post x px vx vk (Some res'));
    }
  }
}
```

```pulse
fn cbor_det_map_get
  (x: cbor_det_map)
  (k: cbordet)
  (#px: perm)
  (#vx: Ghost.erased Spec.cbor)
  (#pk: perm)
  (#vk: Ghost.erased Spec.cbor)
requires
    (cbor_det_map_match px x vx ** cbor_det_match pk k vk)
returns res: option cbordet
ensures
    (
      cbor_det_match pk k vk **
      safe_map_get_post x px vx vk res **
      pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
    )
{
  cbor_det_map_match_elim x;
  let res = Det.cbor_det_map_get () x.map k;
  cbor_det_map_get_post_to_safe x px vx vk res;
  res
}
```
