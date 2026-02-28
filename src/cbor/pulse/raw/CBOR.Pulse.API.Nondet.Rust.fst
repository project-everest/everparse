module CBOR.Pulse.API.Nondet.Rust
#lang-pulse

(* NOTE: this .fst file does not need anything from the Raw namespace,
but it has been moved here to be hidden from verified clients. *)

module Nondet = CBOR.Pulse.Raw.Nondet

module C = C // necessary to pull C.krml into extraction, otherwise Karamel fails with "`C._zero_for_deref`: impossible", believing that it is a non-function external symbol, which Karamel extraction to Rust does not support

(* Validation, parsing and serialization *)

type cbornondet = Nondet.cbor_nondet_t

[@@pulse_unfold]
let cbor_nondet_match = Nondet.cbor_nondet_match

open CBOR.Pulse.Raw.Nondet

let cbor_nondet_reset_perm () = Nondet.cbor_nondet_reset_perm ()

let cbor_nondet_share () = Nondet.cbor_nondet_share ()

let cbor_nondet_gather () = Nondet.cbor_nondet_gather ()

let cbor_nondet_parse () map_key_bound strict_check input #pm #v = Nondet.cbor_nondet_parse () map_key_bound strict_check input #pm #v

let cbor_nondet_match_with_size = Nondet.cbor_nondet_match_with_size

let cbor_nondet_match_with_size_intro = Nondet.cbor_nondet_match_with_size_intro

let cbor_nondet_size () x bound #p #x' #v = Nondet.cbor_nondet_size () x bound #p #x' #v

let cbor_nondet_serialize () x output #size #y #pm #v = Nondet.cbor_nondet_serialize () x output #size #y #pm #v

(* Constructors *)

fn cbor_nondet_mk_simple_value
  (v: U8.t)
requires emp
returns res: option cbornondet
ensures
  cbor_nondet_mk_simple_value_post v res **
  pure (Some? res <==> simple_value_wf v)
{
  if simple_value_wf v {
    let res = Nondet.cbor_nondet_mk_simple_value () v;
    fold (cbor_nondet_mk_simple_value_post v (Some res));
    Some res
  }
  else {
    fold (cbor_nondet_mk_simple_value_post v None);
    None #cbornondet
  }
}

fn cbor_nondet_mk_int64
  (ty: cbor_nondet_int_kind)
  (v: U64.t)
requires emp
returns res: cbornondet
ensures cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v))
{
  if (ty = UInt64) {
    let res = Nondet.cbor_nondet_mk_uint64 () v;
    with v' . rewrite cbor_nondet_match 1.0R res v' as cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v));
    res
  } else {
    let res = Nondet.cbor_nondet_mk_neg_int64 () v;
    with v' . rewrite cbor_nondet_match 1.0R res v' as cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v));
    res
  }
}

let uint64_max_prop : squash (pow2 64 - 1 == 18446744073709551615) =
  assert_norm (pow2 64 - 1 == 18446744073709551615)

module UTF8 = CBOR.Pulse.API.UTF8

fn cbor_impl_utf8_correct () : Base.impl_utf8_correct_t =
  (s: _)
  (#p: _)
  (#v: _)
{
  UTF8.impl_utf8_correct s
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_mk_string_is_correct
  (ty: cbor_nondet_string_kind)
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

fn cbor_nondet_mk_string
  (ty: cbor_nondet_string_kind)
  (s: S.slice U8.t)
  (#p: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires pts_to s #p v
returns res: option cbornondet
ensures
  cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v res **
  pure (Some? res <==> (FStar.UInt.fits (SZ.v (S.len s)) U64.n /\ (ty == TextString ==> CBOR.Spec.API.UTF8.correct v))) // this is true for Rust's str/String, but we will check anyway
{
  let sq: squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  if SZ.gt (S.len s) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
    None #cbornondet
  } else {
    let correct = cbor_nondet_mk_string_is_correct ty s;
    if correct {
      let res = Nondet.cbor_nondet_mk_string () (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s;
      fold (cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v (Some res));
      Some res
    } else {
      fold (cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
      None #cbornondet
    }
  }
}

let cbor_nondet_mk_tagged tag r #pr #v #pv #v' = Nondet.cbor_nondet_mk_tagged () tag r #pr #v #pv #v'

let cbor_nondet_map_entry = Nondet.cbor_nondet_map_entry_t

[@@pulse_unfold]
let cbor_nondet_map_entry_match = Nondet.cbor_nondet_map_entry_match

let cbor_nondet_mk_map_entry xk xv #pk #vk #pv #vv = Nondet.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

fn cbor_nondet_mk_array
  (a: S.slice cbornondet)
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbornondet))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
requires
    pts_to a #pa va **
    PM.seq_list_match va vv (cbor_nondet_match pv)
returns res: option cbornondet
ensures
  cbor_nondet_mk_array_post a pa va pv vv res **
  pure (Some? res <==> FStar.UInt.fits (SZ.v (S.len a)) U64.n)
{
  let _ : squash SZ.fits_u64 = assume (SZ.fits_u64);
  if SZ.gt (S.len a) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_nondet_mk_array_post a pa va pv vv None);
    None #cbornondet;
  } else {
    let res = Nondet.cbor_nondet_mk_array () a;
    fold (cbor_nondet_mk_array_post a pa va pv vv (Some res));
    Some res
  }
}

fn cbor_nondet_mk_map (_: unit) : Base.mk_map_gen_t u#0 #_ #_ cbor_nondet_match cbor_nondet_map_entry_match
= (a: _) (#va: _) (#pv: _) (#vv: _)
{
  Nondet.cbor_nondet_mk_map () a
}

(* Destructors *)

let cbor_nondet_equal x1 x2 #p1 #p2 #v1 #v2 = Nondet.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

let cbor_nondet_major_type _ x #p #v = Nondet.cbor_nondet_major_type () x #p #v

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_nondet_array = {
  array: (array: cbornondet { CaseArray? (cbor_nondet_case array) }) ;
}

let cbor_nondet_array_match (p: perm) (a: cbor_nondet_array) (v: Spec.cbor) : Tot slprop =
  cbor_nondet_match p a.array v **
  pure (Spec.CArray? (Spec.unpack v))

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_nondet_map = {
  map: (map: cbornondet { CaseMap? (cbor_nondet_case map) });
}

noextract [@@noextract_to "krml"]
let cbor_nondet_map_match (p: perm) (a: cbor_nondet_map) (v: Spec.cbor) : Tot slprop =
  cbor_nondet_match p a.map v **
  pure (Spec.CMap? (Spec.unpack v))

fn cbor_nondet_destruct
  (c: cbornondet)
  (#p: perm)
  (#v: Ghost.erased Spec.cbor)
requires
  cbor_nondet_match p c v
returns w: cbor_nondet_view
ensures exists* p' .
  cbor_nondet_view_match p' w v **
  Trade.trade
    (cbor_nondet_view_match p' w v)
    (cbor_nondet_match p c v) **
  pure (cbor_nondet_destruct_postcond w v)
{
  let ty = cbor_nondet_major_type () c;
  cbor_nondet_case_correct c;
  if (ty = cbor_major_type_uint64 || ty = cbor_major_type_neg_int64) {
    let k = (if ty = cbor_major_type_uint64 then UInt64 else NegInt64);
    let i = cbor_nondet_read_uint64 () c;
    fold (cbor_nondet_view_match p (Int64 k i) v);
    intro
      (Trade.trade
        (cbor_nondet_view_match p (Int64 k i) v)
        (cbor_nondet_match p c v)
      )
      #(cbor_nondet_match p c v)
      fn _
    {
      unfold (cbor_nondet_view_match p (Int64 k i) v)
    };
    Int64 k i
  }
  else if (ty = cbor_major_type_byte_string || ty = cbor_major_type_text_string) {
    let k = (if ty = cbor_major_type_byte_string then ByteString else TextString);
    let s = cbor_nondet_get_string () c;
    with p' v' . assert (pts_to s #p' v');
    fold (cbor_nondet_string_match ty p' s v);
    rewrite each ty as (if ByteString? k then cbor_major_type_byte_string else cbor_major_type_text_string);
    fold (cbor_nondet_view_match p' (String k s) v);
    intro
      (Trade.trade
        (cbor_nondet_view_match p' (String k s) v)
        (pts_to s #p' v')
      )
      #emp
      fn _
    {
      unfold (cbor_nondet_view_match p' (String k s) v);
      rewrite each (if ByteString? k then cbor_major_type_byte_string else cbor_major_type_text_string) as ty;
      unfold (cbor_nondet_string_match ty p' s v);
    };
    Trade.trans _ _ (cbor_nondet_match p c v);
    String k s
  }
  else if (ty = cbor_major_type_array) {
    let res : cbor_nondet_array = { array = c };
    rewrite each c as res.array;
    fold (cbor_nondet_array_match p res v);
    fold (cbor_nondet_view_match p (Array res) v);
    intro
      (Trade.trade
        (cbor_nondet_view_match p (Array res) v)
        (cbor_nondet_match p c v)
      )
      #emp
      fn _
    {
      unfold (cbor_nondet_view_match p (Array res) v);
      unfold (cbor_nondet_array_match p res v);
      rewrite each res.array as c;
    };
    Array res
  }
  else if (ty = cbor_major_type_map) {
    let res : cbor_nondet_map = { map = c };
    rewrite each c as res.map;
    fold (cbor_nondet_map_match p res v);
    fold (cbor_nondet_view_match p (Map res) v);
    intro
      (Trade.trade
        (cbor_nondet_view_match p (Map res) v)
        (cbor_nondet_match p c v)
      )
      #emp
      fn _
    {
      unfold (cbor_nondet_view_match p (Map res) v);
      unfold (cbor_nondet_map_match p res v);
      rewrite each res.map as c;
    };
    Map res
  }
  else if (ty = cbor_major_type_tagged) {
    let tag = cbor_nondet_get_tagged_tag () c;
    let payload = cbor_nondet_get_tagged_payload () c;
    with p' v' . assert (cbor_nondet_match p' payload v');
    fold (cbor_nondet_tagged_match p' tag payload v);
    fold (cbor_nondet_view_match p' (Tagged tag payload) v);
    intro
      (Trade.trade
        (cbor_nondet_view_match p' (Tagged tag payload) v)
        (cbor_nondet_match p' payload v')
      )
      #emp
      fn _
    {
      unfold (cbor_nondet_view_match p' (Tagged tag payload) v);
      unfold (cbor_nondet_tagged_match p' tag payload v);
      with v_ . rewrite (cbor_nondet_match p' payload v_) as (cbor_nondet_match p' payload v')
    };
    Trade.trans _ _ (cbor_nondet_match p c v);
    Tagged tag payload
  }
  else {
    let i = cbor_nondet_read_simple_value () c;
    fold (cbor_nondet_view_match p (SimpleValue i) v);
    intro
      (Trade.trade
        (cbor_nondet_view_match p (SimpleValue i) v)
        (cbor_nondet_match p c v)
      )
      #(cbor_nondet_match p c v)
      fn _
    {
      unfold (cbor_nondet_view_match p (SimpleValue i) v)
    };
    SimpleValue i
  }
}

let cbor_nondet_elim_int64 = cbor_nondet_elim_int64

let cbor_nondet_elim_simple_value = cbor_nondet_elim_simple

fn cbor_nondet_get_array_length
  (x: cbor_nondet_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_nondet_array_match p x y
returns res: U64.t
ensures
  cbor_nondet_array_match p x y ** pure (
    Base.get_array_length_post y res
  )
{
  unfold (cbor_nondet_array_match p x y);
  let res = Nondet.cbor_nondet_get_array_length () x.array;
  fold (cbor_nondet_array_match p x y);
  res
}

ghost
fn cbor_nondet_array_match_elim
  (x: cbor_nondet_array)
  (#p: perm)
  (#y: Spec.cbor)
requires cbor_nondet_array_match p x y
ensures cbor_nondet_match p x.array y **
  Trade.trade (cbor_nondet_match p x.array y) (cbor_nondet_array_match p x y) **
  pure (Spec.CArray? (Spec.unpack y))
{
  unfold (cbor_nondet_array_match p x y);
  intro
    (Trade.trade
      (cbor_nondet_match p x.array y)
      (cbor_nondet_array_match p x y)
    )
    #emp
    fn _
  {
    fold (cbor_nondet_array_match p x y);
  };
}

let cbor_nondet_array_iterator_t = cbor_nondet_array_iterator_t

[@@pulse_unfold]
let cbor_nondet_array_iterator_match = cbor_nondet_array_iterator_match

fn cbor_nondet_array_iterator_start
  (x: cbor_nondet_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  (cbor_nondet_array_match p x y)
returns res: cbor_nondet_array_iterator_t
ensures
    (exists* p' l' .
      cbor_nondet_array_iterator_match p' res l' **
      Trade.trade
        (cbor_nondet_array_iterator_match p' res l')
        (cbor_nondet_array_match p x y) **
      pure (
        Spec.CArray? (Spec.unpack y) /\
        l' == Spec.CArray?.v (Spec.unpack y)
    ))
{
  cbor_nondet_array_match_elim x;
  let res = Nondet.cbor_nondet_array_iterator_start () x.array;
  Trade.trans _ _ (cbor_nondet_array_match p x y);
  res
}

let cbor_nondet_array_iterator_is_empty x #p #y = Nondet.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_next x #y #py #z = Nondet.cbor_nondet_array_iterator_next () x #y #py #z

let cbor_nondet_array_iterator_share = Nondet.cbor_nondet_array_iterator_share ()

let cbor_nondet_array_iterator_gather = Nondet.cbor_nondet_array_iterator_gather ()

let cbor_nondet_array_iterator_length = Nondet.cbor_nondet_array_iterator_length ()

let cbor_nondet_array_iterator_truncate = Nondet.cbor_nondet_array_iterator_truncate ()

fn cbor_nondet_get_array_item
  (x: cbor_nondet_array)
  (i: U64.t)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_nondet_array_match p x y
returns res: option cbornondet
ensures
  safe_get_array_item_post x i p y res **
  pure (cbor_nondet_get_array_item_postcond i y res)
{
  let len = cbor_nondet_get_array_length x;
  if U64.gte i len {
    fold (safe_get_array_item_post x i p y None);
    None #cbornondet
  } else {
    cbor_nondet_array_match_elim x;
    let res = Nondet.cbor_nondet_get_array_item () x.array i;
    Trade.trans _ _ (cbor_nondet_array_match p x y);
    fold (safe_get_array_item_post x i p y (Some res));
    Some res
  }
}

fn cbor_nondet_map_length
  (x: cbor_nondet_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_nondet_map_match p x y
returns res: U64.t
ensures
  cbor_nondet_map_match p x y ** pure (
    Base.get_map_length_post y res
  )
{
  unfold (cbor_nondet_map_match p x y);
  let res = Nondet.cbor_nondet_get_map_length () x.map;
  fold (cbor_nondet_map_match p x y);
  res
}

ghost
fn cbor_nondet_map_match_elim
  (x: cbor_nondet_map)
  (#p: perm)
  (#y: Spec.cbor)
requires cbor_nondet_map_match p x y
ensures cbor_nondet_match p x.map y **
  Trade.trade (cbor_nondet_match p x.map y) (cbor_nondet_map_match p x y) **
  pure (Spec.CMap? (Spec.unpack y))
{
  unfold (cbor_nondet_map_match p x y);
  intro
    (Trade.trade
      (cbor_nondet_match p x.map y)
      (cbor_nondet_map_match p x y)
    )
    #emp
    fn _
  {
    fold (cbor_nondet_map_match p x y);
  };
}

let cbor_nondet_map_iterator_t = Nondet.cbor_nondet_map_iterator_t

[@@pulse_unfold]
let cbor_nondet_map_iterator_match = Nondet.cbor_nondet_map_iterator_match

fn cbor_nondet_map_iterator_start
  (x: cbor_nondet_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  (cbor_nondet_map_match p x y)
returns res: cbor_nondet_map_iterator_t
ensures
    (exists* p' l' .
      cbor_nondet_map_iterator_match p' res l' **
      Trade.trade
        (cbor_nondet_map_iterator_match p' res l')
        (cbor_nondet_map_match p x y) **
      pure (
        Base.map_iterator_start_post y l'
    ))
{
  cbor_nondet_map_match_elim x;
  let res = Nondet.cbor_nondet_map_iterator_start () x.map;
  Trade.trans _ _ (cbor_nondet_map_match p x y);
  res
}

let cbor_nondet_map_iterator_is_empty x #p #y = Nondet.cbor_nondet_map_iterator_is_empty () x #p #y

let cbor_nondet_map_iterator_next x #y #py #z = Nondet.cbor_nondet_map_iterator_next () x #y #py #z

let cbor_nondet_map_iterator_share = Nondet.cbor_nondet_map_iterator_share ()

let cbor_nondet_map_iterator_gather = Nondet.cbor_nondet_map_iterator_gather ()

let cbor_nondet_map_entry_key x2 #p #v2 = Nondet.cbor_nondet_map_entry_key () x2 #p #v2

let cbor_nondet_map_entry_value x2 #p #v2 = Nondet.cbor_nondet_map_entry_value () x2 #p #v2

let cbor_nondet_map_entry_share = Nondet.cbor_nondet_map_entry_share ()

let cbor_nondet_map_entry_gather = Nondet.cbor_nondet_map_entry_gather ()

ghost
fn cbor_nondet_map_get_post_to_safe
  (x: cbor_nondet_map)
  (px: perm)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (res: option cbornondet)
requires
  pure (Spec.CMap? (Spec.unpack vx) /\ Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res) **
  Base.map_get_post cbor_nondet_match x.map px vx vk res **
  Trade.trade (cbor_nondet_match px x.map vx) (cbor_nondet_map_match px x vx)
ensures
  safe_map_get_post x px vx vk res
{
  match res {
    None -> {
      unfold (Base.map_get_post cbor_nondet_match x.map px vx vk None);
      unfold (Base.map_get_post_none cbor_nondet_match x.map px vx vk);
      Trade.elim _ _;
      fold (safe_map_get_post x px vx vk None);
      rewrite (safe_map_get_post x px vx vk None) as (safe_map_get_post x px vx vk res)
    }
    Some res' -> {
      unfold (Base.map_get_post cbor_nondet_match x.map px vx vk (Some res'));
      unfold (Base.map_get_post_some cbor_nondet_match x.map px vx vk res');
      Trade.trans _ _ (cbor_nondet_map_match px x vx);
      fold (safe_map_get_post x px vx vk (Some res'));
      rewrite (safe_map_get_post x px vx vk (Some res')) as (safe_map_get_post x px vx vk res);
    }
  }
}

fn cbor_nondet_map_get
  (x: cbor_nondet_map)
  (k: cbornondet)
  (#px: perm)
  (#vx: Ghost.erased Spec.cbor)
  (#pk: perm)
  (#vk: Ghost.erased Spec.cbor)
requires
    (cbor_nondet_map_match px x vx ** cbor_nondet_match pk k vk)
returns res: option cbornondet
ensures
    (
      cbor_nondet_match pk k vk **
      safe_map_get_post x px vx vk res **
      pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
    )
{
  cbor_nondet_map_match_elim x;
  let res = Nondet.cbor_nondet_map_get () x.map k;
  cbor_nondet_map_get_post_to_safe x px vx vk res;
  res
}

let dummy_cbor_nondet_t () = Nondet.dummy_cbor_nondet
