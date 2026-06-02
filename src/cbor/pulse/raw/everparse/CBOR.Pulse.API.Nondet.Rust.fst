module CBOR.Pulse.API.Nondet.Rust
#lang-pulse

friend CBOR.Pulse.API.Nondet.Type
friend CBOR.Pulse.API.Nondet.Common

(* Implementation of CBOR.Pulse.API.Nondet.Rust.fsti using
   CBOR.Pulse.API.Nondet.Common (which is itself built on top of the
   EverParse-based stack). *)

module ImplND = CBOR.Pulse.API.Nondet.Common
module RawType = CBOR.Pulse.Raw.EverParse.Type
module SU = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module PM = Pulse.Lib.SeqMatch
module UTF8 = CBOR.Pulse.API.UTF8
module NondetAB = CBOR.Pulse.Raw.EverParse.Nondet.ArrayBuilder
module IT = LowParse.PulseParse.Iterator.Type
module L = FStar.List.Tot

module C = C // necessary to pull C.krml into extraction, otherwise Karamel fails with "`C._zero_for_deref`: impossible", believing that it is a non-function external symbol, which Karamel extraction to Rust does not support

open CBOR.Spec.Constants
open CBOR.Pulse.API.Base

(* ======== Types and match relation ======== *)

type cbornondet = CBOR.Pulse.API.Nondet.Type.cbor_nondet_t

[@@pulse_unfold]
let cbor_nondet_match = ImplND.cbor_nondet_match

let cbor_nondet_reset_perm () = ImplND.cbor_nondet_reset_perm ()

let cbor_nondet_share () = ImplND.cbor_nondet_share ()
let cbor_nondet_gather () = ImplND.cbor_nondet_gather ()

(* ======== Validate, parse, size, serialize ======== *)

let seq_length_append_l_n
  (#t: Type)
  (v1 v2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append v1 v2) 0 (Seq.length v1) == v1)
= assert (Seq.slice (Seq.append v1 v2) 0 (Seq.length v1) `Seq.equal` v1)

fn cbor_nondet_parse (_: unit) : Base.cbor_nondet_parse_t cbor_nondet_match
=
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let len = ImplND.cbor_nondet_validate () map_key_bound strict_check input;
  if (len = 0sz) {
    fold (cbor_nondet_parse_post cbor_nondet_match input pm v None);
    None #(cbornondet & S.slice U8.t)
  } else {
    S.pts_to_len input;
    Seq.lemma_split v (SZ.v len);
    let inl, inr = SU.split_trade input len;
    Classical.forall_intro_2 (seq_length_append_l_n #U8.t);
    S.pts_to_len inl;
    Spec.cbor_parse_prefix v (Seq.slice v 0 (SZ.v len));
    let res = ImplND.cbor_nondet_parse_valid () inl len;
    Trade.trans_hyp_l _ _ _ (pts_to input #pm v);
    fold (cbor_nondet_parse_post_some cbor_nondet_match input pm v res inr);
    fold (cbor_nondet_parse_post cbor_nondet_match input pm v (Some (res, inr)));
    Some (res, inr)
  }
}

[@@pulse_unfold]
let cbor_nondet_match_with_size = ImplND.cbor_nondet_match_with_size

let cbor_nondet_match_with_size_intro () = ImplND.cbor_nondet_match_with_size_intro ()

let cbor_nondet_size () x bound #p #x' #v = ImplND.cbor_nondet_size () x bound #p #x' #v

fn cbor_nondet_serialize
  (_: unit)
: Base.cbor_nondet_serialize_t #cbornondet cbor_nondet_match_with_size
=
  (x: cbornondet)
  (output: S.slice U8.t)
  (#size: Ghost.erased nat)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  ImplND.cbor_nondet_serialize_inner () x output #size #y #pm #v
}

(* ======== Constructors ======== *)

fn cbor_nondet_mk_simple_value
  (v: U8.t)
requires emp
returns res: option cbornondet
ensures
  cbor_nondet_mk_simple_value_post v res **
  pure (Some? res <==> simple_value_wf v)
{
  if simple_value_wf v {
    let res = ImplND.cbor_nondet_mk_simple_value_unsafe () v;
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
    let res = ImplND.cbor_nondet_mk_uint64 () v;
    with v' . rewrite cbor_nondet_match 1.0R res v' as cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v));
    res
  } else {
    let res = ImplND.cbor_nondet_mk_neg_int64 () v;
    with v' . rewrite cbor_nondet_match 1.0R res v' as cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 (if ty = UInt64 then cbor_major_type_uint64 else cbor_major_type_neg_int64) v));
    res
  }
}

let uint64_max_prop : squash (pow2 64 - 1 == 18446744073709551615) =
  assert_norm (pow2 64 - 1 == 18446744073709551615)

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
  pure (res == true <==> (ty == TextString ==> CBOR.Spec.API.UTF8.correct v))
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
  pure (Some? res <==> (FStar.UInt.fits (SZ.v (S.len s)) U64.n /\ (ty == TextString ==> CBOR.Spec.API.UTF8.correct v)))
{
  let sq: squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  if SZ.gt (S.len s) (SZ.uint64_to_sizet 18446744073709551615uL) {
    fold (cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
    None #cbornondet
  } else {
    let correct = cbor_nondet_mk_string_is_correct ty s;
    if correct {
      let res = ImplND.cbor_nondet_mk_string () (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s;
      fold (cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v (Some res));
      Some res
    } else {
      fold (cbor_nondet_mk_string_post (if ty = ByteString then cbor_major_type_byte_string else cbor_major_type_text_string) s p v None);
      None #cbornondet
    }
  }
}

let cbor_nondet_mk_tagged tag r #pr #v #pv #v' = ImplND.cbor_nondet_mk_tagged_unsafe () tag r #pr #v #pv #v'

(* ======== Map entry ======== *)

let cbor_nondet_map_entry = CBOR.Pulse.API.Nondet.Type.cbor_nondet_map_entry_t

[@@pulse_unfold]
let cbor_nondet_map_entry_match = ImplND.cbor_nondet_map_entry_match

let cbor_nondet_mk_map_entry xk xv #pk #vk #pv #vv = ImplND.cbor_nondet_mk_map_entry () xk xv #pk #vk #pv #vv

(* ======== mk_array ======== *)

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
    let res = ImplND.cbor_nondet_mk_array_inner () a;
    fold (cbor_nondet_mk_array_post a pa va pv vv (Some res));
    Some res
  }
}

(* ======== mk_map ======== *)

let cbor_nondet_mk_map (_: unit) : Base.mk_map_gen_t u#0 #_ #_ cbor_nondet_match cbor_nondet_map_entry_match
= Base.mk_map_gen (RawType.CBOR_Case_Invalid <: cbornondet) (ImplND.cbor_nondet_mk_map_gen ())

(* ======== Destructors ======== *)

let cbor_nondet_equal x1 x2 #p1 #p2 #v1 #v2 = ImplND.cbor_nondet_equal x1 #p1 #v1 x2 #p2 #v2

let cbor_nondet_major_type _ x #p #v = ImplND.cbor_nondet_major_type () x #p #v

(* ======== Array and Map wrapper types ======== *)

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_nondet_array = {
  array: cbornondet;
}

let cbor_nondet_array_match (p: perm) (a: cbor_nondet_array) (v: Spec.cbor) : Tot slprop =
  cbor_nondet_match p a.array v **
  pure (Spec.CArray? (Spec.unpack v))

[@@CAbstractStruct; no_auto_projectors]
noeq
type cbor_nondet_map = {
  map: cbornondet;
}

noextract [@@noextract_to "krml"]
let cbor_nondet_map_match (p: perm) (a: cbor_nondet_map) (v: Spec.cbor) : Tot slprop =
  cbor_nondet_match p a.map v **
  pure (Spec.CMap? (Spec.unpack v))

(* ======== cbor_nondet_destruct ======== *)

#push-options "--z3rlimit 64"

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
  let ty = ImplND.cbor_nondet_major_type () c;
  if (ty = cbor_major_type_uint64 || ty = cbor_major_type_neg_int64) {
    let k = (if ty = cbor_major_type_uint64 then UInt64 else NegInt64);
    let i = ImplND.cbor_nondet_read_uint64_unsafe () c;
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
    let s = ImplND.cbor_nondet_get_string_unsafe () c;
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
    rewrite cbor_nondet_match p c v as cbor_nondet_match p res.array v;
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
      rewrite cbor_nondet_match p res.array v as cbor_nondet_match p c v;
    };
    Array res
  }
  else if (ty = cbor_major_type_map) {
    let res : cbor_nondet_map = { map = c };
    rewrite cbor_nondet_match p c v as cbor_nondet_match p res.map v;
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
      rewrite cbor_nondet_match p res.map v as cbor_nondet_match p c v;
    };
    Map res
  }
  else if (ty = cbor_major_type_tagged) {
    let tag = ImplND.cbor_nondet_get_tagged_tag () c;
    let payload = ImplND.cbor_nondet_get_tagged_payload () c;
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
      with v_ . rewrite cbor_nondet_match p' payload v_ as cbor_nondet_match p' payload v'
    };
    Trade.trans _ _ (cbor_nondet_match p c v);
    Tagged tag payload
  }
  else {
    let i = ImplND.cbor_nondet_read_simple_value_unsafe () c;
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

#pop-options

(* ======== elim_int64, elim_simple_value ======== *)

let cbor_nondet_elim_int64 () = ImplND.cbor_nondet_elim_int64 ()

let cbor_nondet_elim_simple_value () = ImplND.cbor_nondet_elim_simple ()

(* ======== Array: get_array_length ======== *)

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

fn cbor_nondet_get_array_length
  (x: cbor_nondet_array)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_nondet_array_match p x y
returns res: U64.t
ensures
  cbor_nondet_array_match p x y ** pure (
    get_array_length_post y res
  )
{
  unfold (cbor_nondet_array_match p x y);
  let res = ImplND.cbor_nondet_get_array_length_unsafe () x.array;
  fold (cbor_nondet_array_match p x y);
  res
}

(* ======== Array iterator ======== *)

let cbor_nondet_array_iterator_t = CBOR.Pulse.API.Nondet.Type.cbor_nondet_array_iterator_t

[@@pulse_unfold]
let cbor_nondet_array_iterator_match = ImplND.cbor_nondet_array_iterator_match

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
  let res = ImplND.cbor_nondet_array_iterator_start_unsafe () x.array;
  Trade.trans _ _ (cbor_nondet_array_match p x y);
  res
}

let cbor_nondet_array_iterator_is_empty x #p #y = ImplND.cbor_nondet_array_iterator_is_empty () x #p #y

let cbor_nondet_array_iterator_next = Base.array_iterator_next_by_value (ImplND.cbor_nondet_array_iterator_next_unsafe ())

let cbor_nondet_array_iterator_share = ImplND.cbor_nondet_array_iterator_share ()

let cbor_nondet_array_iterator_gather = ImplND.cbor_nondet_array_iterator_gather ()

let cbor_nondet_array_iterator_length x #p #y = ImplND.cbor_nondet_array_iterator_length () x #p #y

let cbor_nondet_array_iterator_truncate x len #p #y = ImplND.cbor_nondet_array_iterator_truncate () x len #p #y

(* ======== cbor_nondet_get_array_item ======== *)

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
    let res = ImplND.cbor_nondet_get_array_item_unsafe () x.array i;
    Trade.trans _ _ (cbor_nondet_array_match p x y);
    fold (safe_get_array_item_post x i p y (Some res));
    Some res
  }
}

(* ======== Structural array builder ops ======== *)

let cbor_nondet_array_append_cell_t = IT.mixed_list cbornondet

[@@pulse_unfold]
let cbor_nondet_array_owned (a: cbor_nondet_array) (l: list Spec.cbor) : Tot slprop =
  NondetAB.cbor_nondet_array_owned a.array l

fn cbor_nondet_array_empty (_: unit)
requires emp
returns res: cbor_nondet_array
ensures cbor_nondet_array_owned res []
{
  let inner = NondetAB.cbor_nondet_array_empty ();
  let res : cbor_nondet_array = { array = inner };
  rewrite (NondetAB.cbor_nondet_array_owned inner []) as (NondetAB.cbor_nondet_array_owned res.array []);
  res
}

fn cbor_nondet_array_singleton
  (x: cbornondet) (ry: R.ref cbornondet)
  (#pm: perm) (#v: Ghost.erased Spec.cbor) (#w0: Ghost.erased cbornondet)
requires cbor_nondet_match pm x v ** R.pts_to ry w0
returns res: cbor_nondet_array
ensures
  cbor_nondet_array_owned res [Ghost.reveal v] **
  Trade.trade
    (cbor_nondet_array_owned res [Ghost.reveal v])
    (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w))
{
  let inner = NondetAB.cbor_nondet_array_singleton x ry;
  let res : cbor_nondet_array = { array = inner };
  rewrite
    (NondetAB.cbor_nondet_array_owned inner [Ghost.reveal v] **
     Trade.trade
       (NondetAB.cbor_nondet_array_owned inner [Ghost.reveal v])
       (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w)))
  as
    (NondetAB.cbor_nondet_array_owned res.array [Ghost.reveal v] **
     Trade.trade
       (NondetAB.cbor_nondet_array_owned res.array [Ghost.reveal v])
       (cbor_nondet_match pm x v ** (exists* w. R.pts_to ry w)));
  res
}

fn cbor_nondet_array_append
  (x1 x2: cbor_nondet_array)
  (r_before r_after: R.ref cbor_nondet_array_append_cell_t)
  (#l1 #l2: Ghost.erased (list Spec.cbor))
  (#vb0 #va0: Ghost.erased cbor_nondet_array_append_cell_t)
requires
  cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
  R.pts_to r_before vb0 ** R.pts_to r_after va0
returns res: option cbor_nondet_array
ensures
  (match res with
   | None ->
     cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)
   | Some r ->
     cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
     Trade.trade
       (cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
       (cbor_nondet_array_owned x1 l1 ** cbor_nondet_array_owned x2 l2 **
        (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
{
  let res = NondetAB.cbor_nondet_array_append x1.array x2.array r_before r_after;
  match res {
    None -> { None #cbor_nondet_array }
    Some r -> {
      let resa : cbor_nondet_array = { array = r };
      rewrite
        (NondetAB.cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
         Trade.trade
           (NondetAB.cbor_nondet_array_owned r (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
           (NondetAB.cbor_nondet_array_owned x1.array l1 ** NondetAB.cbor_nondet_array_owned x2.array l2 **
            (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)))
      as
        (NondetAB.cbor_nondet_array_owned resa.array (L.append (Ghost.reveal l1) (Ghost.reveal l2)) **
         Trade.trade
           (NondetAB.cbor_nondet_array_owned resa.array (L.append (Ghost.reveal l1) (Ghost.reveal l2)))
           (NondetAB.cbor_nondet_array_owned x1.array l1 ** NondetAB.cbor_nondet_array_owned x2.array l2 **
            (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)));
      Some #cbor_nondet_array resa
    }
  }
}

ghost
fn cbor_nondet_array_owned_length_fits
  (a: cbor_nondet_array) (#l: Ghost.erased (list Spec.cbor))
requires cbor_nondet_array_owned a l
ensures cbor_nondet_array_owned a l ** pure (FStar.UInt.fits (L.length (Ghost.reveal l)) U64.n)
{
  NondetAB.cbor_nondet_array_owned_length_fits a.array;
}

fn cbor_nondet_array_to_cbor
  (a: cbor_nondet_array)
  (#l: Ghost.erased (l': list Spec.cbor { FStar.UInt.fits (L.length l') U64.n }))
requires cbor_nondet_array_owned a l
returns res: cbornondet
ensures
  cbor_nondet_match 1.0R res (Spec.pack (Spec.CArray (Ghost.reveal l))) **
  Trade.trade
    (cbor_nondet_match 1.0R res (Spec.pack (Spec.CArray (Ghost.reveal l))))
    (cbor_nondet_array_owned a l)
{
  NondetAB.cbor_nondet_array_finalize a.array;
  a.array
}

(* ======== Map: length ======== *)

fn cbor_nondet_map_length
  (x: cbor_nondet_map)
  (#p: perm)
  (#y: Ghost.erased Spec.cbor)
requires
  cbor_nondet_map_match p x y
returns res: U64.t
ensures
  cbor_nondet_map_match p x y ** pure (
    get_map_length_post y res
  )
{
  unfold (cbor_nondet_map_match p x y);
  let res = ImplND.cbor_nondet_get_map_length_unsafe () x.map;
  fold (cbor_nondet_map_match p x y);
  res
}

(* ======== Map iterator ======== *)

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

let cbor_nondet_map_iterator_t = CBOR.Pulse.API.Nondet.Type.cbor_nondet_map_iterator_t

[@@pulse_unfold]
let cbor_nondet_map_iterator_match = ImplND.cbor_nondet_map_iterator_match

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
        map_iterator_start_post y l'
    ))
{
  cbor_nondet_map_match_elim x;
  let res = ImplND.cbor_nondet_map_iterator_start_unsafe () x.map;
  Trade.trans _ _ (cbor_nondet_map_match p x y);
  res
}

let cbor_nondet_map_iterator_is_empty x #p #y = ImplND.cbor_nondet_map_iterator_is_empty () x #p #y

let cbor_nondet_map_iterator_next = Base.map_iterator_next_by_value (ImplND.cbor_nondet_map_iterator_next_unsafe ())

let cbor_nondet_map_iterator_share = ImplND.cbor_nondet_map_iterator_share ()

let cbor_nondet_map_iterator_gather = ImplND.cbor_nondet_map_iterator_gather ()

(* ======== Map entry ======== *)

let cbor_nondet_map_entry_key x2 #p #v2 = ImplND.cbor_nondet_map_entry_key () x2 #p #v2

let cbor_nondet_map_entry_value x2 #p #v2 = ImplND.cbor_nondet_map_entry_value () x2 #p #v2

let cbor_nondet_map_entry_share = ImplND.cbor_nondet_map_entry_share ()

let cbor_nondet_map_entry_gather = ImplND.cbor_nondet_map_entry_gather ()

(* ======== cbor_nondet_map_get ======== *)

ghost
fn cbor_nondet_map_get_post_to_safe
  (x: cbor_nondet_map)
  (px: perm)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (res: option cbornondet)
requires
  pure (Spec.CMap? (Spec.unpack vx) /\ Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res) **
  map_get_post cbor_nondet_match x.map px vx vk res **
  Trade.trade (cbor_nondet_match px x.map vx) (cbor_nondet_map_match px x vx)
ensures
  safe_map_get_post x px vx vk res
{
  match res {
    None -> {
      unfold (map_get_post cbor_nondet_match x.map px vx vk None);
      unfold (map_get_post_none cbor_nondet_match x.map px vx vk);
      Trade.elim _ _;
      fold (safe_map_get_post x px vx vk None);
      rewrite (safe_map_get_post x px vx vk None) as (safe_map_get_post x px vx vk res)
    }
    Some res' -> {
      unfold (map_get_post cbor_nondet_match x.map px vx vk (Some res'));
      unfold (map_get_post_some cbor_nondet_match x.map px vx vk res');
      Trade.trans _ _ (cbor_nondet_map_match px x vx);
      fold (safe_map_get_post x px vx vk (Some res'));
      rewrite (safe_map_get_post x px vx vk (Some res')) as (safe_map_get_post x px vx vk res)
    }
  }
}

(* The map_get loop uses the map iterator pattern; reuse Det.Rust template. *)

let cbor_nondet_mg_inv_none
  (px: perm) (x: cbornondet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_nondet_map_iterator_t) (cont: bool)
: Tot slprop
= exists* p_i l .
    cbor_nondet_map_iterator_match p_i i l **
    Trade.trade
      (cbor_nondet_map_iterator_match p_i i l)
      (cbor_nondet_match px x vx) **
    pure (
      Spec.cbor_map_get m vk == (if cont then List.Tot.assoc vk l else None) /\
      (cont ==> Cons? l)
    )

let cbor_nondet_mg_inv_some
  (px: perm) (x: cbornondet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (x': cbornondet)
: Tot slprop
= exists* p' vx' .
    cbor_nondet_match p' x' vx' **
    Trade.trade
      (cbor_nondet_match p' x' vx')
      (cbor_nondet_match px x vx) **
    pure (Spec.cbor_map_get m vk == Some vx')

let cbor_nondet_mg_inv
  (cont: bool) (px: perm) (x: cbornondet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_nondet_map_iterator_t) (res: option cbornondet)
: Tot slprop
= match res with
  | None -> cbor_nondet_mg_inv_none px x vx vk m i cont
  | Some x' -> cbor_nondet_mg_inv_some px x vx vk m x'

ghost
fn cbor_nondet_mg_inv_false_elim
  (#gb: bool)
  (px: perm) (x: cbornondet) (vx: Spec.cbor) (vk: Spec.cbor)
  (m: Spec.cbor_map) (i: cbor_nondet_map_iterator_t)
  (res: option cbornondet)
requires
  cbor_nondet_mg_inv gb px x vx vk m i res **
  pure (gb == false /\ Spec.CMap? (Spec.unpack vx) /\ m == Spec.CMap?.c (Spec.unpack vx))
ensures
  map_get_post cbor_nondet_match x px vx vk res **
  pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
{
  rewrite each gb as false;
  match res {
    None -> {
      unfold (cbor_nondet_mg_inv false px x vx vk m i None);
      unfold (cbor_nondet_mg_inv_none px x vx vk m i false);
      Trade.elim _ _;
      fold (map_get_post_none cbor_nondet_match x px vx vk);
      fold (map_get_post cbor_nondet_match x px vx vk None);
      rewrite (map_get_post cbor_nondet_match x px vx vk None)
        as (map_get_post cbor_nondet_match x px vx vk res);
    }
    Some x' -> {
      unfold (cbor_nondet_mg_inv false px x vx vk m i (Some x'));
      unfold (cbor_nondet_mg_inv_some px x vx vk m x');
      fold (map_get_post_some cbor_nondet_match x px vx vk x');
      fold (map_get_post cbor_nondet_match x px vx vk (Some x'));
      rewrite (map_get_post cbor_nondet_match x px vx vk (Some x'))
        as (map_get_post cbor_nondet_match x px vx vk res);
    }
  }
}

#push-options "--z3rlimit 64"

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
  let m : Ghost.erased Spec.cbor_map = Ghost.hide (Spec.CMap?.c (Spec.unpack vx));
  let it = ImplND.cbor_nondet_map_iterator_start_unsafe () x.map;
  with p_it l_it . assert (cbor_nondet_map_iterator_match p_it it l_it);
  let mut pit = it;
  let mut pres = None #cbornondet;
  let is_empty = ImplND.cbor_nondet_map_iterator_is_empty () it;
  let cont0 = not is_empty;
  let mut pcont = cont0;
  fold (cbor_nondet_mg_inv_none px x.map vx vk m it cont0);
  fold (cbor_nondet_mg_inv cont0 px x.map vx vk m it None);
  while (
    !pcont
  )
  invariant exists* i_val cont res_val .
    R.pts_to pit i_val **
    R.pts_to pcont cont **
    R.pts_to pres res_val **
    cbor_nondet_match pk k vk **
    cbor_nondet_mg_inv cont px x.map vx vk m i_val res_val **
    pure (cont == true ==> None? res_val)
  {
    with gi gcont gres . assert (cbor_nondet_mg_inv gcont px x.map vx vk m gi gres);
    rewrite (cbor_nondet_mg_inv gcont px x.map vx vk m gi gres)
      as (cbor_nondet_mg_inv gcont px x.map vx vk m gi None);
    unfold (cbor_nondet_mg_inv gcont px x.map vx vk m gi None);
    unfold (cbor_nondet_mg_inv_none px x.map vx vk m gi gcont);
    let entry = ImplND.cbor_nondet_map_iterator_next_unsafe () pit;
    Trade.trans _ _ (cbor_nondet_match px x.map vx);
    with pentry ventry . assert (cbor_nondet_map_entry_match pentry entry ventry);
    let key = ImplND.cbor_nondet_map_entry_key () entry;
    with pk_key . assert (cbor_nondet_match pk_key key (fst ventry));
    let eq = ImplND.cbor_nondet_equal key #pk_key #(fst ventry) k #pk #vk;
    Trade.elim (cbor_nondet_match pk_key key (fst ventry)) (cbor_nondet_map_entry_match pentry entry ventry);
    with p_iter' iter' z_tl . assert (cbor_nondet_map_iterator_match p_iter' iter' z_tl);
    if eq {
      Trade.elim_hyp_r
        (cbor_nondet_map_entry_match pentry entry ventry)
        (cbor_nondet_map_iterator_match p_iter' iter' z_tl)
        (cbor_nondet_match px x.map vx);
      let value = ImplND.cbor_nondet_map_entry_value () entry;
      Trade.trans _ _ (cbor_nondet_match px x.map vx);
      pres := Some value;
      pcont := false;
      fold (cbor_nondet_mg_inv_some px x.map vx vk m value);
      fold (cbor_nondet_mg_inv false px x.map vx vk m iter' (Some value))
    } else {
      Trade.elim_hyp_l
        (cbor_nondet_map_entry_match pentry entry ventry)
        (cbor_nondet_map_iterator_match p_iter' iter' z_tl)
        (cbor_nondet_match px x.map vx);
      let i' = !pit;
      Trade.rewrite_with_trade
        (cbor_nondet_map_iterator_match p_iter' iter' z_tl)
        (cbor_nondet_map_iterator_match p_iter' i' z_tl);
      Trade.trans _ _ (cbor_nondet_match px x.map vx);
      let is_empty' = ImplND.cbor_nondet_map_iterator_is_empty () i';
      let cont' = not is_empty';
      pcont := cont';
      fold (cbor_nondet_mg_inv_none px x.map vx vk m i' cont');
      assert (R.pts_to pres None);
      fold (cbor_nondet_mg_inv cont' px x.map vx vk m i' None)
    }
  };
  with gi gcont gres . assert (cbor_nondet_mg_inv gcont px x.map vx vk m gi gres);
  cbor_nondet_mg_inv_false_elim px x.map vx vk m gi gres;
  cbor_nondet_map_get_post_to_safe x px vx vk gres;
  let res = !pres;
  rewrite (safe_map_get_post x px vx vk gres) as (safe_map_get_post x px vx vk res);
  res
}

#pop-options

(* ======== dummy ======== *)

let dummy_cbor_nondet_t () = RawType.CBOR_Case_Invalid

let dummy_cbor_nondet_array_append_cell () : cbor_nondet_array_append_cell_t =
  IT.Base IT.Empty
