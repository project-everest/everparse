module CBOR.Pulse.API.Det.Rust.Macros
#lang-pulse
include CBOR.Pulse.API.Det.Rust
open CBOR.Spec.Constants
open Pulse.Lib.Pervasives
module Spec = CBOR.Spec.API.Format
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Base = CBOR.Pulse.API.Base

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_mk_int64'
  (_: unit)
: Base.mk_int64_t u#0 #_ cbor_det_match
= (ty: _)
  (v: _)
{
  let mty = (if ty = cbor_major_type_uint64 then UInt64 else NegInt64);
  cbor_det_mk_int64 mty v
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_mk_simple'
  (_: unit)
: Base.mk_simple_t u#0 #_ cbor_det_match
= (v: _)
{
  let Some res = cbor_det_mk_simple_value v;
  unfold (cbor_det_mk_simple_value_post v (Some res));
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_mk_string0
  (_: unit)
: Base.mk_string_t u#0 #_ cbor_det_match
= (ty: _)
  (s: _)
  (#p: _)
  (#v: _)
{
  S.pts_to_len s;
  let mty = (if ty = cbor_major_type_byte_string then ByteString else TextString);
  let res = cbor_det_mk_string mty s;
  let Some c = res;
  unfold (cbor_det_mk_string_post ty s p v (Some c));
  c
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_string_from_array = Base.mk_string_from_array (cbor_det_mk_string0 ())

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_mk_array0
  (_: unit)
: Base.mk_array_t #_ cbor_det_match
= (a: _)
  (#pa: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  S.pts_to_len a;
  let res = cbor_det_mk_array a;
  let Some c = res;
  unfold (cbor_det_mk_array_post a pa va pv vv (Some c));
  c
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_array_from_array = Base.mk_array_from_array (cbor_det_mk_array0 ())

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_read_uint64 () : Base.read_uint64_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Int64 ty res = v;
  unfold (cbor_det_view_match p' (Int64 ty res) y);
  fold (cbor_det_view_match p' (Int64 ty res) y);
  Trade.elim _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_read_simple_value () : Base.read_simple_value_t u#0 #_ cbor_det_match
= (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let SimpleValue res = v;
  unfold (cbor_det_view_match p' (SimpleValue res) y);
  fold (cbor_det_view_match p' (SimpleValue res) y);
  Trade.elim _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_get_string'
  (_: unit)
: Base.get_string_t u#0 #_ cbor_det_match
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let String kd a = v;
  let t' : Ghost.erased major_type_byte_string_or_text_string = Ghost.hide (if ByteString? kd then cbor_major_type_byte_string else cbor_major_type_text_string);
  Trade.rewrite_with_trade
    (cbor_det_view_match p' (String kd a) y)
    (cbor_det_string_match t' p' a y);
  Trade.trans _ _ (cbor_det_match p x y);
  unfold (cbor_det_string_match t' p' a y);
  with v' . assert (pts_to a #p' v');
  intro
    (Trade.trade
      (pts_to a #p' v')
      (cbor_det_string_match t' p' a y)
    )
    #emp
    fn _
  {
    fold (cbor_det_string_match t' p' a y);
  };
  Trade.trans _ _ (cbor_det_match p x y);
  a
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_get_tagged_tag'
  (_: unit)
: Base.get_tagged_tag_t u#0 #_ cbor_det_match
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Tagged tag a = v;
  unfold (cbor_det_view_match p' (Tagged tag a) y);
  unfold (cbor_det_tagged_match p' tag a y);
  fold (cbor_det_tagged_match p' tag a y);
  fold (cbor_det_view_match p' (Tagged tag a) y);
  Trade.elim _ _;
  tag
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_get_tagged_payload'
  (_: unit)
: Base.get_tagged_payload_t u#0 #_ cbor_det_match
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Tagged tag a = v;
  unfold (cbor_det_view_match p' (Tagged tag a) y);
  unfold (cbor_det_tagged_match p' tag a y);
  with v' . assert (cbor_det_match p' a v');
  intro
    (Trade.trade
      (cbor_det_match p' a v')
      (cbor_det_view_match p' (Tagged tag a) y)
    )
    #emp
    fn _
  {
    fold (cbor_det_tagged_match p' tag a y);
    fold (cbor_det_view_match p' (Tagged tag a) y);
  };
  Trade.trans _ _ (cbor_det_match p x y);
  a
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_get_array_length'
  (_: unit)
: Base.get_array_length_t u#0 #_ cbor_det_match
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Array a = v;
  unfold (cbor_det_view_match p' (Array a) y);
  let res = cbor_det_get_array_length a;
  fold (cbor_det_view_match p' (Array a) y);
  Trade.elim _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_array_iterator_start'
  (_: unit)
: Base.array_iterator_start_t u#0 u#0 #_ #_ cbor_det_match cbor_det_array_iterator_match
= (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Array a = v;
  Trade.rewrite_with_trade
    (cbor_det_view_match p' v y)
    (cbor_det_array_match p' a y);
  Trade.trans _ _ (cbor_det_match p x y);
  let res = cbor_det_array_iterator_start a;
  Trade.trans _ _ (cbor_det_match p x y);
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_get_array_item'
  (_: unit)
: Base.get_array_item_t u#0 #_ cbor_det_match
= (x: _)
  (i: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Array a = v;
  Trade.rewrite_with_trade
    (cbor_det_view_match p' v y)
    (cbor_det_array_match p' a y);
  Trade.trans _ _ (cbor_det_match p x y);
  let ores = cbor_det_get_array_item a i;
  let Some res = ores;
  unfold (safe_get_array_item_post a i p' y (Some res));
  Trade.trans _ _ (cbor_det_match p x y);
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_get_map_length'
  (_: unit)
: Base.get_map_length_t u#0 #_ cbor_det_match
=
  (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Map a = v;
  unfold (cbor_det_view_match p' (Map a) y);
  let res = cbor_det_map_length a;
  fold (cbor_det_view_match p' (Map a) y);
  Trade.elim _ _;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_map_iterator_start'
  (_: unit)
: Base.map_iterator_start_t u#0 u#0 #_ #_ cbor_det_match cbor_det_map_iterator_match
= (x: _)
  (#p: _)
  (#y: _)
{
  let v = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' v y);
  let Map a = v;
  Trade.rewrite_with_trade
    (cbor_det_view_match p' v y)
    (cbor_det_map_match p' a y);
  Trade.trans _ _ (cbor_det_match p x y);
  let res = cbor_det_map_iterator_start a;
  Trade.trans _ _ (cbor_det_match p x y);
  res
}

ghost
fn cbor_det_map_get'_aux
  (x: cbordet)
  (m: cbor_det_map)
  (res: option cbordet)
  (#px: perm)
  (#vx: Spec.cbor)
  (#vk: Spec.cbor)
  (#p': perm)
requires
  safe_map_get_post m p' vx vk res **
  Trade.trade
    (cbor_det_map_match p' m vx)
    (cbor_det_match px x vx)
ensures
  Base.map_get_post cbor_det_match x px vx vk res **
  pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res))
{
  match res {
    None -> {
      unfold (safe_map_get_post m p' vx vk None);
      Trade.elim _ _;
      fold (Base.map_get_post_none cbor_det_match x px vx vk);
      fold (Base.map_get_post cbor_det_match x px vx vk None)
    }
    Some x' -> {
      unfold (safe_map_get_post m p' vx vk (Some x'));
      Trade.trans _ _ (cbor_det_match px x vx);
      fold (Base.map_get_post_some cbor_det_match x px vx vk x');
      fold (Base.map_get_post cbor_det_match x px vx vk (Some x'))
    }
  }
}

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_map_get'
  (_: unit)
: Base.map_get_t u#0 #_ cbor_det_match
= (x: _)
  (k: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
{
  let x' = cbor_det_destruct x;
  with p' . assert (cbor_det_view_match p' x' vx);
  let Map m = x';
  Trade.rewrite_with_trade
    (cbor_det_view_match p' x' vx)
    (cbor_det_map_match p' m vx);
  Trade.trans _ _ (cbor_det_match px x vx);
  let res = cbor_det_map_get m k;
  cbor_det_map_get'_aux x m res;
  res
}
