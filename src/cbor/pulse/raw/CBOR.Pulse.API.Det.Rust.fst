module CBOR.Pulse.API.Det.Rust
#lang-pulse

(* NOTE: this .fst file does not need anything from the Raw namespace,
but it has been moved here to be hidden from verified clients. *)

module Det = CBOR.Pulse.API.Det.Common

module C = C // necessary to pull C.krml into extraction, otherwise Karamel fails with "`C._zero_for_deref`: impossible", believing that it is a non-function external symbol, which Karamel extraction to Rust does not support

(* Validation, parsing and serialization *)

type cbordet = Det.cbor_det_t

[@@pulse_unfold]
let cbor_det_match = Det.cbor_det_match

open CBOR.Pulse.API.Det.Common

let cbor_det_reset_perm () = Det.cbor_det_reset_perm ()

let cbor_det_share () = Det.cbor_det_share ()

let cbor_det_gather () = Det.cbor_det_gather ()

let cbor_det_parse () =
  cbor_det_parse_full (cbor_det_validate ()) (cbor_det_parse_valid ())

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

fn cbor_det_serialize
  (_: unit)
: cbor_det_serialize_t u#0 #_ cbor_det_match
=
  (x: cbordet)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len output;
  let len = Det.cbor_det_size x (S.len output);
  if (SZ.gt len 0sz) {
    let out, rem = S.split output len;
    S.pts_to_len out;
    let len' = Det.cbor_det_serialize x out;
    S.pts_to_len out;
    with v1 . assert (pts_to out v1);
    assert (pure (Seq.equal v1 (Spec.cbor_det_serialize y)));
    S.join out rem output;
    with v' . assert (pts_to output v');
    Seq.lemma_split v' (SZ.v len');
    assert (pure (Seq.equal (Seq.slice v' 0 (SZ.v len')) (Spec.cbor_det_serialize y)));
    assert (pure (Seq.equal (Seq.slice v' (SZ.v len) (Seq.length v)) (Seq.slice v (SZ.v len) (Seq.length v))));
    Some len'
  } else {
    None #SZ.t
  }
}

(* Constructors *)

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

fn cbor_det_mk_int64
  (ty: cbor_det_int_kind)
  (v: U64.t)
requires emp
returns res: cbordet
ensures cbor_det_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v))
{
  Det.cbor_det_mk_int64 () (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v
}

let uint64_max_prop : squash (pow2 64 - 1 == 18446744073709551615) =
  assert_norm (pow2 64 - 1 == 18446744073709551615)

module UTF8 = CBOR.Pulse.Raw.UTF8

fn cbor_impl_utf8_correct () : Base.impl_utf8_correct_t =
  (s: _)
  (#p: _)
  (#v: _)
{
  UTF8.impl_utf8_correct s
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_mk_string_is_correct
  (ty: cbor_det_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to s #p v
returns res: bool
ensures 
  pts_to s #p v **
  pure (res == true <==> (ty == TextString ==> CBOR.Spec.API.UTF8.correct v)) // this is true for Rust's str/String, but we will check anyway
{
  if (ty = TextString) {
    cbor_impl_utf8_correct () s
  } else {
    true
  }
}

fn cbor_det_mk_string
  (ty: cbor_det_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to s #p v
returns res: option cbordet
ensures
  cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v res **
  pure (Some? res <==> (FStar.UInt.fits (SZ.v (S.len s)) U64.n /\ (ty == TextString ==> CBOR.Spec.API.UTF8.correct v))) // this is true for Rust's str/String, but we will check anyway
{
  let sq: squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  if SZ.gt (S.len s) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
    None #cbordet
  } else {
    let correct = cbor_det_mk_string_is_correct ty s;
    if correct {
      let res = Det.cbor_det_mk_string () (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s;
      fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v (Some res));
      Some res
    } else {
      fold (cbor_det_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
      None #cbordet
    }
  }
}

let cbor_det_mk_tagged tag r #pr #v #pv #v' = Det.cbor_det_mk_tagged () tag r #pr #v #pv #v'

let cbor_det_map_entry = Det.cbor_det_map_entry_t

[@@pulse_unfold]
let cbor_det_map_entry_match = Det.cbor_det_map_entry_match

let cbor_det_mk_map_entry xk xv #pk #vk #pv #vv = Det.cbor_det_mk_map_entry () xk xv #pk #vk #pv #vv

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

fn cbor_det_mk_map (_: unit) : Base.mk_map_gen_t u#0 #_ #_ cbor_det_match cbor_det_map_entry_match
= (a: _) (#va: _) (#pv: _) (#vv: _)
{
   Base.mk_map_gen (dummy_cbor_det_t ()) (Det.cbor_det_mk_map_gen ()) a #va #pv #vv
}

(* Destructors *)

let cbor_det_equal x1 x2 #p1 #p2 #v1 #v2 = Det.cbor_det_equal () x1 x2 #p1 #p2 #v1 #v2

let cbor_det_major_type _ x #p #v = Det.cbor_det_major_type () x #p #v

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
    (cbor_det_match p c v) **
  pure (cbor_det_destruct_postcond w v)
{
  let ty = cbor_det_major_type () c;
  cbor_det_case_correct c;
  if (ty = cbor_major_type_uint64 || ty = cbor_major_type_neg_int64) {
    let k = (if ty = cbor_major_type_uint64 then UInt64 else NegInt64);
    let i = cbor_det_read_uint64 () c;
    fold (cbor_det_view_match p (Int64 k i) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (Int64 k i) v)
        (cbor_det_match p c v)
      )
      #(cbor_det_match p c v)
      fn _
    {
      unfold (cbor_det_view_match p (Int64 k i) v)
    };
    Int64 k i
  }
  else if (ty = cbor_major_type_byte_string || ty = cbor_major_type_text_string) {
    let k = (if ty = cbor_major_type_byte_string then ByteString else TextString);
    let s = cbor_det_get_string () c;
    with p' v' . assert (pts_to s #p' v');
    fold (cbor_det_string_match ty p' s v);
    rewrite (cbor_det_string_match ty p' s v) as (cbor_det_view_match p' (String k s) v);
    intro
      (Trade.trade
        (cbor_det_view_match p' (String k s) v)
        (pts_to s #p' v')
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p' (String k s) v);
      with ty . unfold (cbor_det_string_match ty p' s v);
    };
    Trade.trans _ _ (cbor_det_match p c v);
    String k s
  }
  else if (ty = cbor_major_type_array) {
    let res : cbor_det_array = { array = c };
    rewrite Det.cbor_det_match p c v as Det.cbor_det_match p res.array v;
    fold (cbor_det_array_match p res v);
    fold (cbor_det_view_match p (Array res) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (Array res) v)
        (cbor_det_match p c v)
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p (Array res) v);
      unfold (cbor_det_array_match p res v);
      rewrite Det.cbor_det_match p res.array v as Det.cbor_det_match p c v;
    };
    Array res
  }
  else if (ty = cbor_major_type_map) {
    let res : cbor_det_map = { map = c };
    rewrite Det.cbor_det_match p c v as Det.cbor_det_match p res.map v;
    fold (cbor_det_map_match p res v);
    fold (cbor_det_view_match p (Map res) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (Map res) v)
        (cbor_det_match p c v)
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p (Map res) v);
      unfold (cbor_det_map_match p res v);
      rewrite Det.cbor_det_match p res.map v as Det.cbor_det_match p c v;
    };
    Map res
  }
  else if (ty = cbor_major_type_tagged) {
    let tag = cbor_det_get_tagged_tag () c;
    let payload = cbor_det_get_tagged_payload () c;
    with p' v' . assert (cbor_det_match p' payload v');
    fold (cbor_det_tagged_match p' tag payload v);
    fold (cbor_det_view_match p' (Tagged tag payload) v);
    intro
      (Trade.trade
        (cbor_det_view_match p' (Tagged tag payload) v)
        (cbor_det_match p' payload v')
      )
      #emp
      fn _
    {
      unfold (cbor_det_view_match p' (Tagged tag payload) v);
      unfold (cbor_det_tagged_match p' tag payload v);
      with v_ . rewrite Det.cbor_det_match p' payload v_ as Det.cbor_det_match p' payload v'
    };
    Trade.trans _ _ (cbor_det_match p c v);
    Tagged tag payload
  }
  else {
    let i = cbor_det_read_simple_value () c;
    fold (cbor_det_view_match p (SimpleValue i) v);
    intro
      (Trade.trade
        (cbor_det_view_match p (SimpleValue i) v)
        (cbor_det_match p c v)
      )
      #(cbor_det_match p c v)
      fn _
    {
      unfold (cbor_det_view_match p (SimpleValue i) v)
    };
    SimpleValue i
  }
}

let cbor_det_elim_int64 = cbor_det_elim_int64

let cbor_det_elim_simple_value = cbor_det_elim_simple

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
  intro
    (Trade.trade
      (cbor_det_match p x.array y)
      (cbor_det_array_match p x y)
    )
    #emp
    fn _
  {
    fold (cbor_det_array_match p x y);
  };
}

let cbor_det_array_iterator_t = cbor_det_array_iterator_t

[@@pulse_unfold]
let cbor_det_array_iterator_match = cbor_det_array_iterator_match

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

let cbor_det_array_iterator_is_empty x #p #y = Det.cbor_det_array_iterator_is_empty () x #p #y

let cbor_det_array_iterator_next x #y #py #z = Det.cbor_det_array_iterator_next () x #y #py #z

let cbor_det_array_iterator_share = Det.cbor_det_array_iterator_share ()

let cbor_det_array_iterator_gather = Det.cbor_det_array_iterator_gather ()

let cbor_det_array_iterator_length = Det.cbor_det_array_iterator_length ()

let cbor_det_array_iterator_truncate = Det.cbor_det_array_iterator_truncate ()

fn cbor_det_get_array_item
  (x: cbor_det_array)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_det_array_match p x y
returns res: option cbordet
ensures
  safe_get_array_item_post x i p y res **
  pure (cbor_det_get_array_item_postcond i y res)
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
  intro
    (Trade.trade
      (cbor_det_match p x.map y)
      (cbor_det_map_match p x y)
    )
    #emp
    fn _
  {
    fold (cbor_det_map_match p x y);
  };
}

let cbor_det_map_iterator_t = Det.cbor_det_map_iterator_t

[@@pulse_unfold]
let cbor_det_map_iterator_match = Det.cbor_det_map_iterator_match

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

let cbor_det_map_iterator_is_empty x #p #y = Det.cbor_det_map_iterator_is_empty () x #p #y

let cbor_det_map_iterator_next x #y #py #z = Det.cbor_det_map_iterator_next () x #y #py #z

let cbor_det_map_iterator_share = Det.cbor_det_map_iterator_share ()

let cbor_det_map_iterator_gather = Det.cbor_det_map_iterator_gather ()

let cbor_det_map_entry_key x2 #p #v2 = Det.cbor_det_map_entry_key () x2 #p #v2

let cbor_det_map_entry_value x2 #p #v2 = Det.cbor_det_map_entry_value () x2 #p #v2

let cbor_det_map_entry_share = Det.cbor_det_map_entry_share ()

let cbor_det_map_entry_gather = Det.cbor_det_map_entry_gather ()

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
      rewrite (safe_map_get_post x px vx vk None) as (safe_map_get_post x px vx vk res)
    }
    Some res' -> {
      unfold (map_get_post cbor_det_match x.map px vx vk (Some res'));
      unfold (map_get_post_some cbor_det_match x.map px vx vk res');
      Trade.trans _ _ (cbor_det_map_match px x vx);
      fold (safe_map_get_post x px vx vk (Some res'));
      rewrite (safe_map_get_post x px vx vk (Some res')) as (safe_map_get_post x px vx vk res)
    }
  }
}

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
  let res = Base.map_get_as_option (Det.cbor_det_map_get ()) x.map k;
  cbor_det_map_get_post_to_safe x px vx vk res;
  res
}

let cbor_det_serialize_string = Det.cbor_det_serialize_string ()
let cbor_det_serialize_tag = Det.cbor_det_serialize_tag ()
let cbor_det_serialize_array = Det.cbor_det_serialize_array ()
let cbor_det_serialize_map_insert = Det.cbor_det_serialize_map_insert ()
let cbor_det_serialize_map = Det.cbor_det_serialize_map ()

let dummy_cbor_det_t () = Det.dummy_cbor_det_t ()
