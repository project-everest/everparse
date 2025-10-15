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
