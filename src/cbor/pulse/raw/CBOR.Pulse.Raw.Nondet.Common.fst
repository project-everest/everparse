module CBOR.Pulse.Raw.Nondet.Common
#lang-pulse
friend CBOR.Pulse.API.Det.Type
friend CBOR.Spec.API.Format
open CBOR.Pulse.Raw.Match
open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base

module Spec = CBOR.Spec.API.Format
module Raw = CBOR.Pulse.Raw.Match
module SpecRaw = CBOR.Spec.Raw
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util

type cbor_nondet_t = cbor_raw

let cbor_nondet_match
  (p: perm)
  (c: cbor_raw)
  (v: Spec.cbor)
: Tot slprop
= exists* v' . Raw.cbor_match p c v' ** pure (
    SpecRaw.valid_raw_data_item v' /\
    SpecRaw.mk_cbor v' == v
  )

ghost fn cbor_nondet_match_elim
  (c: cbor_raw)
  (#p: perm)
  (#v: Spec.cbor)
requires
  cbor_nondet_match p c v
returns v': Ghost.erased SpecRaw.raw_data_item
ensures
  Raw.cbor_match p c v' **
  Trade.trade
    (Raw.cbor_match p c v')
    (cbor_nondet_match p c v) **
  pure (
    SpecRaw.valid_raw_data_item v' /\
    SpecRaw.mk_cbor v' == v
  )
{
  unfold (cbor_nondet_match p c v);
  with v' . assert (Raw.cbor_match p c v');
  intro
    (Trade.trade
      (Raw.cbor_match p c v')
      (cbor_nondet_match p c v)
    )
    fn _ {
      fold (cbor_nondet_match p c v)
    };
    v'
}

ghost fn cbor_nondet_match_intro
  (c: cbor_raw)
  (#p: perm)
  (#v: SpecRaw.raw_data_item)
requires
  Raw.cbor_match p c v **
  pure (
    SpecRaw.valid_raw_data_item v
  )
ensures 
  cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v) **
  Trade.trade
    (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v))
    (Raw.cbor_match p c v)
{
  CBOR.Pulse.Raw.Match.Perm.cbor_raw_share _ c _;
  fold (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v));
  intro
    (Trade.trade
      (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v))
      (cbor_match p c v)
    )
    #(cbor_match (p /. 2.0R) c v)
    fn _ {
      unfold (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v));
      CBOR.Pulse.Raw.Match.Perm.cbor_raw_gather (p /. 2.0R) c v _ _;
    };
}

ghost
fn cbor_nondet_share
  (_: unit)
: CBOR.Pulse.API.Base.share_t u#0 u#0 #_ #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  CBOR.Pulse.Raw.Match.Perm.cbor_raw_share _ x _;
  fold (cbor_nondet_match (p /. 2.0R) x v);
  fold (cbor_nondet_match (p /. 2.0R) x v);
}

ghost
fn cbor_nondet_gather
  (_: unit)
: CBOR.Pulse.API.Base.gather_t u#0 u#0 #_ #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
  (#p': _)
  (#v': _)
{
  unfold (cbor_nondet_match p x v);
  unfold (cbor_nondet_match p' x v');
  CBOR.Pulse.Raw.Match.Perm.cbor_raw_gather p x _ _ _;
  fold (cbor_nondet_match (p +. p') x v);
}

noextract [@@noextract_to "krml"]
let cbor_nondet_validate_post
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
  let r = Spec.cbor_parse v in
  if SZ.v res = 0
  then (Some? r ==> (Some? map_key_bound /\ Spec.cbor_map_key_depth (fst (Some?.v r)) > SZ.v (Some?.v map_key_bound)))
  else (
    Some? r /\
    SZ.v res == snd (Some?.v r) /\
    ((Some? map_key_bound /\ strict_check) ==> Spec.cbor_map_key_depth (fst (Some?.v r)) <= SZ.v (Some?.v map_key_bound))
  )

let cbor_nondet_validate_post_weaken
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Lemma
  (requires cbor_nondet_validate_post map_key_bound strict_check v res /\
    SZ.v res > 0)
  (ensures cbor_nondet_validate_post None false v res)
= ()

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_validate_t
=
  (map_key_bound: option SZ.t) ->
  (strict_check: bool) ->
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_nondet_validate_post map_key_bound strict_check v res
    ))

fn cbor_nondet_validate (_: unit) : cbor_nondet_validate_t = 
  (map_key_bound: _)
  (strict_check: _)
  (input: _)
  (#pm: _)
  (#v: _)
{
  Classical.forall_intro (Classical.move_requires SpecRaw.mk_cbor_map_key_depth);
  CBOR.Pulse.Raw.Format.Nondet.Validate.cbor_validate_nondet map_key_bound strict_check input;
}

noextract [@@noextract_to "krml"]
let cbor_nondet_parse_valid_post
  (v: Seq.seq U8.t)
  (v': Spec.cbor)
: Tot prop
= let w = Spec.cbor_parse v in
  Some? w /\
  v' == fst (Some?.v w)

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_parse_valid_t
  (#cbor_nondet_t: Type)
  (cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
=
  (input: S.slice U8.t) ->
  (len: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_nondet_t
    (pts_to input #pm v ** pure (
      cbor_nondet_validate_post None false v len /\
      SZ.v len > 0
    ))
    (fun res -> exists* p' v' .
      cbor_nondet_match p' res v' **
      Trade.trade (cbor_nondet_match p' res v') (pts_to input #pm v) ** pure (
        cbor_nondet_parse_valid_post v v'
    ))

fn cbor_nondet_parse_valid (_: unit) : cbor_nondet_parse_valid_t #cbor_nondet_t cbor_nondet_match =
  (input: S.slice U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len input;
  Seq.lemma_split v (SZ.v len);
  let res = CBOR.Pulse.Raw.Format.Parse.cbor_parse input len;
  with v1 . assert (cbor_match 1.0R res v1);
  CBOR.Spec.Raw.Format.serialize_parse_cbor v1;
  CBOR.Spec.Raw.Format.parse_cbor_prefix (CBOR.Spec.Raw.Format.serialize_cbor v1) v;
  cbor_nondet_match_intro res;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

noextract [@@noextract_to "krml"]
let cbor_nondet_serialize_postcond
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: option SZ.t)
: Tot prop
= match res with
  | None -> True // TODO: specify maximum length
  | Some len ->
    SZ.v len <= Seq.length v' /\
    Seq.length v' == Seq.length v /\
    Seq.equal (Seq.slice v' (SZ.v len) (Seq.length v)) (Seq.slice v (SZ.v len) (Seq.length v)) /\
    Spec.cbor_parse v' == Some (y, SZ.v len)

noextract [@@noextract_to "krml"]
let cbor_nondet_serialize_postcond_c
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= cbor_nondet_serialize_postcond y v v' (if res = 0sz then None else Some res)

inline_for_extraction
let cbor_nondet_serialize_t
  (#cbordet: Type)
  (cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop)
=
  (x: cbordet) ->
  (output: S.slice U8.t) ->
  (#y: Ghost.erased Spec.cbor) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (option SZ.t)
    (cbor_det_match pm x y ** pts_to output v)
    (fun res -> exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      cbor_nondet_serialize_postcond y v v' res
    ))

fn cbor_nondet_serialize
  (_: unit)
: cbor_nondet_serialize_t #cbor_nondet_t cbor_nondet_match
=
  (x: _)
  (output: _)
  (#y: _)
  (#pm: _)
  (#v: _)
{
  unfold (cbor_nondet_match pm x y);
  with pm' w . assert (CBOR.Pulse.Raw.Match.cbor_match pm' x w);
  S.pts_to_len output;
  let len = CBOR.Pulse.Raw.Format.Serialize.cbor_size x (S.len output);
  if (len = 0sz) {
    fold (cbor_nondet_match pm x y);
    None
  } else {
    Seq.lemma_split v (SZ.v len);
    let (out, outr) = S.split output len;
    S.pts_to_len out;
    let res = CBOR.Pulse.Raw.Format.Serialize.cbor_serialize x out;
    with vl . assert (pts_to out vl);
    S.pts_to_len out;
    S.join out outr output;
    with v' . assert (pts_to output v');
    S.pts_to_len output;
    Seq.lemma_split v' (SZ.v len);
    CBOR.Spec.Raw.Format.serialize_parse_cbor w;
    CBOR.Spec.Raw.Format.parse_cbor_prefix (CBOR.Spec.Raw.Format.serialize_cbor w) v';
    fold (cbor_nondet_match pm x y);
    Some res
  }
}

(* Destructors *)

fn cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  SpecRaw.mk_cbor_eq v';
  let res = CBOR.Pulse.Raw.Compare.impl_major_type x;
  fold (cbor_nondet_match p x v);
  res
}

fn cbor_nondet_read_simple_value (_: unit) : read_simple_value_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_simple_elim x;
  fold (cbor_nondet_match p x v);
  res
}

fn cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  Raw.cbor_match_cases x;
  SpecRaw.mk_cbor_eq v';
  rewrite (Raw.cbor_match p x v')
    as (Raw.cbor_match_simple (Raw.CBOR_Case_Simple?.v x) v');
  unfold (Raw.cbor_match_simple (Raw.CBOR_Case_Simple?.v x) v')
}

fn cbor_nondet_read_uint64 (_: unit) : read_uint64_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_int_elim_value x;
  fold (cbor_nondet_match p x v);
  res.value
}

fn cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  Raw.cbor_match_cases x;
  SpecRaw.mk_cbor_eq v';
  rewrite (Raw.cbor_match p x v')
    as (Raw.cbor_match_int (Raw.CBOR_Case_Int?.v x) v');
  unfold (Raw.cbor_match_int (Raw.CBOR_Case_Int?.v x) v')
}

fn cbor_nondet_get_string_length (_: unit) : get_string_length_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_string_elim_length x;
  fold (cbor_nondet_match p x v);
  res.value
}

fn cbor_nondet_get_string (_: unit) : get_string_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_string_elim_payload x;
  Trade.trans _ _ (cbor_nondet_match p x v);
  res
}

fn cbor_nondet_get_tagged_tag (_: unit) : get_tagged_tag_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_tagged_get_tag x;
  fold (cbor_nondet_match p x v);
  res.value
}

fn cbor_nondet_get_tagged_payload (_: unit) : get_tagged_payload_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  SpecRaw.valid_eq SpecRaw.basic_data_model v';
  let res = CBOR.Pulse.Raw.Read.cbor_match_tagged_get_payload x;
  Trade.trans _ _ (cbor_nondet_match p x v);
  cbor_nondet_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p x v);
  res
}

fn cbor_nondet_get_array_length (_: unit) : get_array_length_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with p' v' . assert (cbor_match p' x v');
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_array_get_length x;
  fold (cbor_nondet_match p x v);
  res.value
}

let cbor_nondet_array_iterator_t = CBOR.Pulse.Raw.Read.cbor_array_iterator

let cbor_nondet_array_iterator_match
  (p: perm)
  (i: cbor_nondet_array_iterator_t)
  (l: list Spec.cbor)
: Tot slprop
= exists* l' .
    CBOR.Pulse.Raw.Read.cbor_array_iterator_match p i l' **
    pure (List.Tot.for_all SpecRaw.valid_raw_data_item l' /\
      l == List.Tot.map SpecRaw.mk_cbor l'
    )

module Read = CBOR.Pulse.Raw.Read

ghost fn cbor_nondet_array_iterator_match_elim
  (i: cbor_nondet_array_iterator_t)
  (#p: perm)
  (#l: list Spec.cbor)
requires
  cbor_nondet_array_iterator_match p i l
returns l': Ghost.erased (list SpecRaw.raw_data_item)
ensures
    CBOR.Pulse.Raw.Read.cbor_array_iterator_match p i l' **
    Trade.trade
      (CBOR.Pulse.Raw.Read.cbor_array_iterator_match p i l')
      (cbor_nondet_array_iterator_match p i l) **
    pure (List.Tot.for_all SpecRaw.valid_raw_data_item l' /\
      l == List.Tot.map SpecRaw.mk_cbor l'
    )
{
  unfold (cbor_nondet_array_iterator_match p i l);
  with l' . assert (
    CBOR.Pulse.Raw.Read.cbor_array_iterator_match p i l' 
  );
  intro
    (Trade.trade
      (CBOR.Pulse.Raw.Read.cbor_array_iterator_match p i l')
      (cbor_nondet_array_iterator_match p i l)
    )
    fn _ {
      fold (cbor_nondet_array_iterator_match p i l)
    };
  l'
}

ghost fn cbor_nondet_array_iterator_match_intro
  (i: cbor_nondet_array_iterator_t)
  (#p: perm)
  (#v: list SpecRaw.raw_data_item)
requires
  Read.cbor_array_iterator_match p i v **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item v
  )
ensures 
  cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v) **
  Trade.trade
    (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v))
    (Read.cbor_array_iterator_match p i v)
{
  Read.cbor_array_iterator_share i;
  fold (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v));
  intro
    (Trade.trade
      (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v))
      (Read.cbor_array_iterator_match p i v)
    )
    #(Read.cbor_array_iterator_match (p /. 2.0R) i v)
    fn _ {
      unfold (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v));
      Read.cbor_array_iterator_gather i #(p /. 2.0R) #v;
    };
}

fn cbor_nondet_array_iterator_start (_: unit) : array_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v'; 
  SpecRaw.valid_eq SpecRaw.basic_data_model v';
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_array_iterator_init f64 x;
  Trade.trans _ _ (cbor_nondet_match p x v);
  with p' l . assert (Read.cbor_array_iterator_match p' res l);
  cbor_nondet_array_iterator_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p x v);
  res
}

fn cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_array_iterator_match p x v);
  let res = Read.cbor_array_iterator_is_empty x;
  fold (cbor_nondet_array_iterator_match p x v);
  res
}

fn cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_array_iterator_match p x v);
  let res = Read.cbor_array_iterator_length x;
  fold (cbor_nondet_array_iterator_match p x v);
  res
}

fn cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_t u#0 #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
= (x: _)
  (#y: _)
  (#py: _)
  (#z: _)
{
  let l' = cbor_nondet_array_iterator_match_elim y;
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_array_iterator_next f64 x;
  Trade.trans _ _ (cbor_nondet_array_iterator_match py y z);
  with y' z' . assert (pts_to x y' ** Read.cbor_array_iterator_match py y' z');
  cbor_nondet_array_iterator_match_intro y';
  Trade.trans_hyp_r _ _ _ (cbor_nondet_array_iterator_match py y z);
  Trade.rewrite_with_trade
    (cbor_nondet_array_iterator_match (py /. 2.0R) y' _)
    (cbor_nondet_array_iterator_match (py /. 2.0R) y' (List.Tot.tl z));
  Trade.trans_hyp_r _ _ _ (cbor_nondet_array_iterator_match py y z);
  cbor_nondet_match_intro res;
  Trade.trans_hyp_l _ _ _ (cbor_nondet_array_iterator_match py y z);
  with p' v' . assert (cbor_nondet_match p' res v');
  Trade.rewrite_with_trade
    (cbor_nondet_match p' res v')
    (cbor_nondet_match p' res (List.Tot.hd z));
  Trade.trans_hyp_l _ _ _ (cbor_nondet_array_iterator_match py y z);
  res
}

module U64 = FStar.UInt64

fn cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match
= (x: _)
  (len: _)
  (#py: _)
  (#z: _)
{
  let l' = cbor_nondet_array_iterator_match_elim x;
  let res = Read.cbor_array_iterator_truncate x len;
  Trade.trans _ _ (cbor_nondet_array_iterator_match py x z);
  CBOR.Spec.Util.list_map_splitAt SpecRaw.mk_cbor l' (U64.v len);
  CBOR.Spec.Util.list_for_all_splitAt SpecRaw.valid_raw_data_item l' (U64.v len);
  cbor_nondet_array_iterator_match_intro res;
  Trade.trans _ _ (cbor_nondet_array_iterator_match py x z);
  res
}

ghost
fn cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match
= (x: _)
  (#py: _)
  (#z: _)
{
  unfold (cbor_nondet_array_iterator_match py x z);
  Read.cbor_array_iterator_share x;
  fold (cbor_nondet_array_iterator_match (py /. 2.0R) x z);
  fold (cbor_nondet_array_iterator_match (py /. 2.0R) x z);
}

ghost
fn cbor_nondet_array_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match
= (x: _)
  (#py1: _)
  (#z1: _)
  (#py2: _)
  (#z2: _)
{
  unfold (cbor_nondet_array_iterator_match py1 x z1);
  unfold (cbor_nondet_array_iterator_match py2 x z2);
  Read.cbor_array_iterator_gather x #py1 #_ #py2 #_;
  fold (cbor_nondet_array_iterator_match (py1 +. py2) x z1);
}

fn cbor_nondet_get_array_item (_: unit) : get_array_item_t u#0 #_ cbor_nondet_match
= (x: _)
  (i: _)
  (#p: _)
  (#v: _)
{
  let l : Ghost.erased (list Spec.cbor) = Ghost.hide (Spec.CArray?.v (Spec.unpack v));
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  SpecRaw.valid_eq SpecRaw.basic_data_model v';
  let l' : Ghost.erased (list SpecRaw.raw_data_item) = Ghost.hide (SpecRaw.Array?.v v');
  let res = Read.cbor_array_item (assume (SZ.fits_u64)) x i;
  Trade.trans _ _ (cbor_nondet_match p x v);
  List.Tot.lemma_index_memP l' (U64.v i);
  List.Tot.for_all_mem SpecRaw.valid_raw_data_item l';
  CBOR.Spec.Util.list_index_map SpecRaw.mk_cbor l' (U64.v i);
  cbor_nondet_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p x v);
  res
}

fn cbor_nondet_get_map_length (_: unit) : get_map_length_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  let res = Raw.cbor_match_map_get_length x;
  Trade.elim _ _;
  res.value
}

let cbor_nondet_map_iterator_t = CBOR.Pulse.Raw.Read.cbor_map_iterator

let cbor_nondet_map_iterator_match
  (p: perm)
  (i: cbor_nondet_map_iterator_t)
  (l: list (Spec.cbor & Spec.cbor))
: Tot slprop
= exists* l' . Read.cbor_map_iterator_match p i l' **
  pure (
    List.Tot.for_all (SpecRaw.valid_raw_data_item) (List.Tot.map fst l') /\
    List.Tot.for_all (SpecRaw.valid_raw_data_item) (List.Tot.map snd l') /\
    CBOR.Spec.Util.list_no_setoid_repeats (SpecRaw.raw_equiv) (List.Tot.map fst l') /\
    l == List.Tot.map SpecRaw.mk_cbor_map_entry l'
  )

ghost fn cbor_nondet_map_iterator_match_intro
  (i: cbor_nondet_map_iterator_t)
  (#p: perm)
  (#l': list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
requires
  Read.cbor_map_iterator_match p i l' **
  pure (
    List.Tot.for_all (SpecRaw.valid_raw_data_item) (List.Tot.map fst l') /\
    List.Tot.for_all (SpecRaw.valid_raw_data_item) (List.Tot.map snd l') /\
    CBOR.Spec.Util.list_no_setoid_repeats (SpecRaw.raw_equiv) (List.Tot.map fst l')
  )
ensures
  cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry l') **
  Trade.trade
    (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry l'))
    (Read.cbor_map_iterator_match p i l')
{
  Read.cbor_map_iterator_share i;
  fold (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry l'));
  intro
    (Trade.trade
      (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry l'))
      (Read.cbor_map_iterator_match p i l')
    )
    #(Read.cbor_map_iterator_match (p /. 2.0R) i l')
  fn _ {
    unfold (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry l'));
    Read.cbor_map_iterator_gather i #_ #l'
  }
}

ghost fn cbor_nondet_map_iterator_match_elim
  (i: cbor_nondet_map_iterator_t)
  (#p: perm)
  (#l: list (Spec.cbor & Spec.cbor))
requires
  cbor_nondet_map_iterator_match p i l
returns l' : Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
ensures
  Read.cbor_map_iterator_match p i l' **
  Trade.trade
    (Read.cbor_map_iterator_match p i l')
    (cbor_nondet_map_iterator_match p i l) **
  pure (
    List.Tot.for_all (SpecRaw.valid_raw_data_item) (List.Tot.map fst l') /\
    List.Tot.for_all (SpecRaw.valid_raw_data_item) (List.Tot.map snd l') /\
    CBOR.Spec.Util.list_no_setoid_repeats (SpecRaw.raw_equiv) (List.Tot.map fst l') /\
    l == List.Tot.map SpecRaw.mk_cbor_map_entry l'
  )
{
  unfold (cbor_nondet_map_iterator_match p i l);
  with l' . assert (Read.cbor_map_iterator_match p i l');
  intro
    (Trade.trade
      (Read.cbor_map_iterator_match p i l')
      (cbor_nondet_map_iterator_match p i l)
    )
    fn _ {
      fold (cbor_nondet_map_iterator_match p i l)
    };
  l'
}

let rec cbor_nondet_map_iterator_start_assoc'
  (l': list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
  (x: SpecRaw.raw_data_item)
: Lemma
  (requires (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l') /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l') /\
    SpecRaw.valid_raw_data_item x
  ))
  (ensures (
    let l = List.Tot.map SpecRaw.mk_cbor_map_entry l' in
    begin match CBOR.Spec.Util.list_setoid_assoc SpecRaw.raw_equiv x l', List.Tot.assoc (SpecRaw.mk_cbor x) l with
    | None, None -> True
    | Some y', Some y -> SpecRaw.valid_raw_data_item y' /\ y == SpecRaw.mk_cbor y'
    | _ -> False
    end
  ))
  (decreases l')
= match l' with
  | [] -> ()
  | (k', v') :: q' ->
    SpecRaw.mk_cbor_equiv x k';
    if SpecRaw.raw_equiv x k'
    then ()
    else cbor_nondet_map_iterator_start_assoc' q' x

let cbor_nondet_map_iterator_start_assoc
  (m: Spec.cbor_map)
  (l': list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
  (sq: squash (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l') /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l') /\
    SpecRaw.mk_cbor_match_map l' m
  ))
  (x: Spec.cbor)
: Lemma
  (ensures (
    let l = List.Tot.map SpecRaw.mk_cbor_map_entry l' in
    Spec.cbor_map_get m x == List.Tot.assoc x l
  ))
= assert (SpecRaw.mk_cbor_match_map_elem l' m (SpecRaw.mk_det_raw_cbor x));
  cbor_nondet_map_iterator_start_assoc' l' (SpecRaw.mk_det_raw_cbor x)

let rec cbor_nondet_map_iterator_start_no_repeats'
  (l': list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
  (x: SpecRaw.raw_data_item)
: Lemma
  (requires (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l') /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l') /\
    SpecRaw.valid_raw_data_item x /\
    List.Tot.memP (SpecRaw.mk_cbor x) (List.Tot.map fst (List.Tot.map SpecRaw.mk_cbor_map_entry l'))
  ))
  (ensures (
    List.Tot.existsb (SpecRaw.raw_equiv x) (List.Tot.map fst l')
  ))
  (decreases l')
= match l' with
  | [] -> ()
  | (k', _) :: q ->
    SpecRaw.mk_cbor_equiv x k';
    Classical.move_requires (cbor_nondet_map_iterator_start_no_repeats' q) x

let rec cbor_nondet_map_iterator_start_no_repeats
  (l': list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l') /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd l') /\
    CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l')
  ))
  (ensures (
    List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.map SpecRaw.mk_cbor_map_entry l'))
  ))
  (decreases l')
= match l' with
  | [] -> ()
  | (k', v') :: q ->
    Classical.move_requires (cbor_nondet_map_iterator_start_no_repeats' q) k';
    cbor_nondet_map_iterator_start_no_repeats q

fn cbor_nondet_map_iterator_start (_: unit) : map_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match
= (x: _)
  (#p: _)
  (#y: _)
{
  let y' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq y';
  SpecRaw.valid_eq SpecRaw.basic_data_model y';
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_map_iterator_init f64 x;
  Trade.trans _ _ (cbor_nondet_match p x y);
  cbor_nondet_map_iterator_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p x y);
  let m : Ghost.erased Spec.cbor_map = Spec.CMap?.c (Spec.unpack y);
  let l' : Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item)) = SpecRaw.Map?.v y';
  let l : Ghost.erased (list (Spec.cbor & Spec.cbor)) = List.Tot.map SpecRaw.mk_cbor_map_entry l';
  Classical.forall_intro (cbor_nondet_map_iterator_start_assoc m l' ());
  assert (pure (forall k . Spec.cbor_map_get m k == List.Tot.assoc k l));
  cbor_nondet_map_iterator_start_no_repeats l';
  assert (pure (List.Tot.no_repeats_p (List.Tot.map fst l)));
  res
}

fn cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_map_iterator_match p x v);
  let res = Read.cbor_map_iterator_is_empty x;
  fold (cbor_nondet_map_iterator_match p x v);
  res
}

let cbor_nondet_map_entry_t = Raw.cbor_map_entry

let cbor_nondet_map_entry_match
  (p: perm)
  (x: cbor_nondet_map_entry_t)
  (y: Spec.cbor & Spec.cbor)
: Tot slprop
= cbor_nondet_match p x.cbor_map_entry_key (fst y) **
  cbor_nondet_match p x.cbor_map_entry_value (snd y)

ghost
fn cbor_nondet_map_entry_match_intro
  (res: cbor_nondet_map_entry_t)
  (#p: perm)
  (#a: SpecRaw.raw_data_item & SpecRaw.raw_data_item)
requires
  Raw.cbor_match_map_entry p res a **
  pure (
    SpecRaw.valid_raw_data_item (fst a) /\
    SpecRaw.valid_raw_data_item (snd a)
  )
ensures
  cbor_nondet_map_entry_match (p /. 2.0R) res (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)) **
  Trade.trade
    (cbor_nondet_map_entry_match (p /. 2.0R) res (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)))
    (Raw.cbor_match_map_entry p res a)
{
  Trade.rewrite_with_trade
    (Raw.cbor_match_map_entry p res a)
    (Raw.cbor_match p res.cbor_map_entry_key (fst a) ** Raw.cbor_match p res.cbor_map_entry_value (snd a));
  cbor_nondet_match_intro res.cbor_map_entry_key;
  Trade.trans_hyp_l _ _ _ (Raw.cbor_match_map_entry p res a);
  cbor_nondet_match_intro res.cbor_map_entry_value;
  Trade.trans_hyp_r _ _ _ (Raw.cbor_match_map_entry p res a);
  Trade.rewrite_with_trade
    (cbor_nondet_match (p /. 2.0R) res.cbor_map_entry_key (SpecRaw.mk_cbor (fst a)) **
      cbor_nondet_match (p /. 2.0R) res.cbor_map_entry_value (SpecRaw.mk_cbor (snd a))
    )
    (cbor_nondet_map_entry_match (p /. 2.0R) res (SpecRaw.mk_cbor_map_entry a));
  Trade.trans _ _ (Raw.cbor_match_map_entry p res a)
}

fn cbor_nondet_map_iterator_next (_: unit) : map_iterator_next_t u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_map_iterator_match
= (x: _)
  (#y: _)
  (#py: _)
  (#z: _)
{
  let l' = cbor_nondet_map_iterator_match_elim y;
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let res = Read.cbor_map_iterator_next f64 x;
  Trade.trans _ _ (cbor_nondet_map_iterator_match py y z);
  cbor_nondet_map_entry_match_intro res;
  Trade.trans_hyp_l _ _ _ (cbor_nondet_map_iterator_match py y z);
  with y' z' . assert (Read.cbor_map_iterator_match py y' z');
  cbor_nondet_map_iterator_match_intro y';
  Trade.trans_hyp_r _ _ _ (cbor_nondet_map_iterator_match py y z);
  res
}

ghost
fn cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match
= (x: _)
  (#py: _)
  (#z: _)
{
  unfold (cbor_nondet_map_iterator_match py x z);
  Read.cbor_map_iterator_share x;
  fold (cbor_nondet_map_iterator_match (py /. 2.0R) x z);
  fold (cbor_nondet_map_iterator_match (py /. 2.0R) x z);
}

ghost
fn cbor_nondet_map_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match
= (x: _)
  (#py1: _)
  (#z1: _)
  (#py2: _)
  (#z2: _)
{
  unfold (cbor_nondet_map_iterator_match py1 x z1);
  unfold (cbor_nondet_map_iterator_match py2 x z2);
  Read.cbor_map_iterator_gather x #py1 #_ #py2 #_;
  fold (cbor_nondet_map_iterator_match (py1 +. py2) x z1);
}

fn cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match
= (x2: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_nondet_map_entry_match p x2 v2);
  intro
    (Trade.trade
      (cbor_nondet_match p x2.cbor_map_entry_key (fst v2))
      (cbor_nondet_map_entry_match p x2 v2)
    )
    #(cbor_nondet_match p x2.cbor_map_entry_value (snd v2))
    fn _
  {
    fold (cbor_nondet_map_entry_match p x2 v2);
  };
  x2.cbor_map_entry_key
}

fn cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match
= (x2: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_nondet_map_entry_match p x2 v2);
  intro
    (Trade.trade
      (cbor_nondet_match p x2.cbor_map_entry_value (snd v2))
      (cbor_nondet_map_entry_match p x2 v2)
    )
    #(cbor_nondet_match p x2.cbor_map_entry_key (fst v2))
    fn _
  {
    fold (cbor_nondet_map_entry_match p x2 v2);
  };
  x2.cbor_map_entry_value
}

ghost
fn cbor_nondet_map_entry_share
  (_: unit)
: share_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_map_entry_match p x v);
  cbor_nondet_share () x.cbor_map_entry_key;
  cbor_nondet_share () x.cbor_map_entry_value;
  fold (cbor_nondet_map_entry_match (p /. 2.0R) x v);
  fold (cbor_nondet_map_entry_match (p /. 2.0R) x v);
}

ghost
fn cbor_nondet_map_entry_gather
  (_: unit)
: gather_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match
= (x: _)
  (#p: _)
  (#v: _)
  (#p': _)
  (#v': _)
{
  unfold (cbor_nondet_map_entry_match p x v);
  unfold (cbor_nondet_map_entry_match p' x v');
  cbor_nondet_gather () x.cbor_map_entry_key #p;
  cbor_nondet_gather () x.cbor_map_entry_value #p;
  fold (cbor_nondet_map_entry_match (p +. p') x v);
}
