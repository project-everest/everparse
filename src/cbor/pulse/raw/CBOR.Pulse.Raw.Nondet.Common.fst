module CBOR.Pulse.Raw.Nondet.Common
#lang-pulse
friend CBOR.Pulse.API.Nondet.Type
friend CBOR.Spec.API.Format
open CBOR.Pulse.Raw.Match

module Raw = CBOR.Pulse.Raw.Match
module SpecRaw = CBOR.Spec.Raw

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

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_reset_perm (_: unit) : reset_perm_t #_ cbor_nondet_match
=
  (c: cbor_nondet_t)
  (#p: perm)
  (#r: Ghost.erased Spec.cbor)
  (q: perm)
{
  let r' = cbor_nondet_match_elim c;
  let res = Raw.cbor_raw_reset_perm _ c _ (2.0R *. q);
  Trade.trans _ _ (cbor_nondet_match p c r);
  cbor_nondet_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p c r);
  res
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
  Classical.forall_intro (SpecRaw.list_assoc_map_mk_cbor_map_entry m l' ());
  assert (pure (forall k . Spec.cbor_map_get m k == List.Tot.assoc k l));
  SpecRaw.list_no_repeats_map_fst_mk_cbor_map_entry l';
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

(* Equality *)

fn cbor_nondet_equal
  (x1: cbor_nondet_t)
  (#p1: perm)
  (#v1: Ghost.erased Spec.cbor)
  (x2: cbor_nondet_t)
  (#p2: perm)
  (#v2: Ghost.erased Spec.cbor)
requires
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2
returns res: bool
ensures
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2 **
  pure (res == true <==> Ghost.reveal v1 == Ghost.reveal v2)
{
  let v1' = cbor_nondet_match_elim x1;
  let v2' = cbor_nondet_match_elim x2;
  SpecRaw.mk_cbor_equiv v1' v2';
  let res = CBOR.Pulse.Raw.Nondet.Compare.cbor_nondet_equiv x1 x2;
  Trade.elim _ (cbor_nondet_match p1 x1 v1);
  Trade.elim _ _;
  res
}

let cbor_nondet_map_get_invariant_true_postcond
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (vv: Spec.cbor)
: Tot prop
= Spec.CMap? (Spec.unpack vx) /\
  Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk == Some vv

let cbor_nondet_map_get_invariant_true
  (px: perm)
  (x: cbor_nondet_t)
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (vdest: cbor_nondet_t)
: Tot slprop
= exists* pv vv .
    cbor_nondet_match pv vdest vv **
    Trade.trade
      (cbor_nondet_match pv vdest vv)
      (cbor_nondet_match px x vx) **
    pure (
      cbor_nondet_map_get_invariant_true_postcond vx vk vv
    )

let cbor_nondet_map_get_invariant_false_postcond
  (vx: Spec.cbor)
  (vk: Spec.cbor)
  (l: list (Spec.cbor & Spec.cbor))
: Tot prop
= Spec.CMap? (Spec.unpack vx) /\
  Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk == List.Tot.assoc vk l

let cbor_nondet_map_get_invariant_false
  (px: perm)
  (x: cbor_nondet_t)
  (vx: Spec.cbor)
  (vdest0: cbor_nondet_t)
  (vk: Spec.cbor)
  (vdest: cbor_nondet_t)
  (i: cbor_nondet_map_iterator_t)
  (cont: bool)
: Tot slprop
= exists* p' l .
    cbor_nondet_map_iterator_match p' i l **
    Trade.trade
      (cbor_nondet_map_iterator_match p' i l)
      (cbor_nondet_match px x vx) **
    pure (
      cbor_nondet_map_get_invariant_false_postcond vx vk l /\
      vdest == vdest0 /\
      cont == Cons? l
    )

let cbor_nondet_map_get_invariant
  (px: perm)
  (x: cbor_nondet_t)
  (vx: Spec.cbor)
  (vdest0: cbor_nondet_t)
  (vk: Spec.cbor)
  (vdest: cbor_nondet_t)
  (i: cbor_nondet_map_iterator_t)
  (cont: bool)
  (res: bool)
: Tot slprop
= if res
  then cbor_nondet_map_get_invariant_true px x vx vk vdest
  else cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i cont

ghost fn cbor_nondet_map_get_concl
  (px: perm)
  (x: cbor_nondet_t)
  (vx: Spec.cbor)
  (vdest0: cbor_nondet_t)
  (vk: Spec.cbor)
  (vdest: cbor_nondet_t)
  (i: cbor_nondet_map_iterator_t)
  (bres: bool)
requires
  cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i false bres
ensures
  exists* res .
      map_get_post cbor_nondet_match x px vx vk res **
      pure (Spec.CMap? (Spec.unpack vx) /\ (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res) /\
        mk_map_gen_by_ref_postcond (Ghost.reveal vdest0) res vdest bres
      )
{
  if bres {
    rewrite (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i false bres)
      as (cbor_nondet_map_get_invariant_true px x vx vk vdest);
    unfold (cbor_nondet_map_get_invariant_true px x vx vk vdest);
    fold (map_get_post_some cbor_nondet_match x px vx vk vdest);
    fold (map_get_post cbor_nondet_match x px vx vk (Some vdest));
  } else {
    rewrite (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i false bres)
      as (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i false);
    unfold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i false);
    Trade.elim _ _;
    fold (map_get_post_none cbor_nondet_match x px vx vk);
    fold (map_get_post cbor_nondet_match x px vx vk None);
  }
}

fn cbor_nondet_map_get (_: unit)
: map_get_by_ref_t #_ cbor_nondet_match
= (x: _)
  (k: _)
  (dest: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
  (#vdest0: _)
{
  let i = cbor_nondet_map_iterator_start () x;
  with p0 l0 . assert (cbor_nondet_map_iterator_match p0 i l0);
  let mut pi = i;
  let mut pres = false;
  let cont = not (cbor_nondet_map_iterator_is_empty () i);
  let mut pcont = cont;
  fold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest0 i cont);
  rewrite (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest0 i cont)
    as (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest0 i cont false);
  while (
    let res = !pres;
    let cont = !pcont;
    (cont && not res)
  ) invariant b . exists* i vdest res cont . (
    pts_to pi i **
    pts_to dest vdest **
    pts_to pres res **
    pts_to pcont cont **
    cbor_nondet_match pk k vk **
    cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i cont res **
    pure (b == (cont && not res))
  ) {
    with gi vdest gres gcont . assert (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest gi gcont gres);
    rewrite (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest gi gcont gres)
      as (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest gi true);
    unfold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest gi true);
    let y = cbor_nondet_map_iterator_next () pi;
    Trade.trans _ _ (cbor_nondet_match px x vx);
    with py y vy . assert (cbor_nondet_map_entry_match py y vy);
    Trade.rewrite_with_trade
      (cbor_nondet_map_entry_match py y vy)
      (cbor_nondet_match py y.cbor_map_entry_key (fst vy) ** cbor_nondet_match py y.cbor_map_entry_value (snd vy));
    if (cbor_nondet_equal y.cbor_map_entry_key k) {
      Trade.elim_hyp_l _ _ (cbor_nondet_map_entry_match py y vy);
      Trade.trans_hyp_l _ _ _ (cbor_nondet_match px x vx);
      Trade.elim_hyp_r _ _ _;
      dest := y.cbor_map_entry_value;
      pres := true;
      fold (cbor_nondet_map_get_invariant_true px x vx vk y.cbor_map_entry_value);
      with i . assert (pts_to pi i);
      rewrite (cbor_nondet_map_get_invariant_true px x vx vk y.cbor_map_entry_value)
        as (cbor_nondet_map_get_invariant px x vx vdest0 vk y.cbor_map_entry_value i true true);
    } else {
      Trade.elim _ (cbor_nondet_map_entry_match py y vy);
      Trade.elim_hyp_l _ _ _;
      let i = !pi;
      let cont = not (cbor_nondet_map_iterator_is_empty () i);
      pcont := cont;
      fold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i cont);
      rewrite (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i cont)
        as (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i cont gres)
    }
  };
  let res = !pres;
  with vdest . assert (pts_to dest vdest);
  with i . assert (pts_to pi i);
  cbor_nondet_map_get_concl px x vx vdest0 vk vdest i res;
  res
}

(* Constructors *)

fn cbor_nondet_mk_simple_value (_: unit) : mk_simple_t u#0 #_ cbor_nondet_match
= (v: _)
{
  let res = Raw.cbor_match_simple_intro v;
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Simple v);
  SpecRaw.mk_cbor_eq (SpecRaw.Simple v);
  fold (cbor_nondet_match 1.0R res (Spec.pack (Spec.CSimple v)));
  res
}

fn cbor_nondet_mk_int64 (_: unit) : mk_int64_t u#0 #_ cbor_nondet_match
= (ty: _)
  (v: _)
{
  let res = Raw.cbor_match_int_intro ty (SpecRaw.mk_raw_uint64 v);
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Int64 ty (SpecRaw.mk_raw_uint64 v));
  SpecRaw.mk_cbor_eq (SpecRaw.Int64 ty (SpecRaw.mk_raw_uint64 v));
  fold (cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 ty v)));
  res
}

fn cbor_nondet_mk_string (_: unit) : mk_string_t u#0 #_ cbor_nondet_match
= (ty: _)
  (s: _)
  (#p: _)
  (#v: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len s;
  let len64 = SpecRaw.mk_raw_uint64 (SZ.sizet_to_uint64 (S.len s));
  let res1 = Raw.cbor_match_string_intro ty len64 s;
  with r. assert Raw.cbor_match 1.0R res1 r;
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.String ty len64 v);
  SpecRaw.mk_cbor_eq (SpecRaw.String ty len64 v);
  cbor_nondet_match_intro res1;
  Trade.trans _ _ (S.pts_to s #p v);
  let res = cbor_nondet_reset_perm () res1 1.0R;
  Trade.trans _ _ (S.pts_to s #p v);
  Trade.rewrite_with_trade
    (cbor_nondet_match 1.0R res (SpecRaw.mk_cbor (SpecRaw.String ty len64 v)))
    (cbor_nondet_match 1.0R res (Spec.pack (Spec.CString ty v)));
  Trade.trans _ _ (S.pts_to s #p v);
  res
}

fn cbor_nondet_mk_tagged (_: unit) : mk_tagged_t #_ cbor_nondet_match
= (tag: _)
  (r: _)
  (#pr: _)
  (#v: _)
  (#pv: _)
  (#v': _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let tag64 = SpecRaw.mk_raw_uint64 tag;
  let w' = cbor_nondet_match_elim v;
  let res1 = Raw.cbor_match_tagged_intro tag64 r;
  Trade.trans_concl_r _ _ _ _;
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Tagged tag64 w');
  SpecRaw.mk_cbor_eq (SpecRaw.Tagged tag64 w');
  cbor_nondet_match_intro res1;
  Trade.trans _ _ (_ ** _);
  let res = cbor_nondet_reset_perm () res1 1.0R;
  Trade.trans _ _ (_ ** _);
  res
}

ghost
fn rec seq_list_array_cbor_nondet_match_elim
  (p: perm)
  (c: Seq.seq cbor_nondet_t)
  (v: list (Spec.cbor))
requires
  SM.seq_list_match c v (cbor_nondet_match p)
returns v': Ghost.erased (list SpecRaw.raw_data_item)
ensures
  SM.seq_list_match c v' (Raw.cbor_match p) **
  Trade.trade
    (SM.seq_list_match c v' (Raw.cbor_match p))
    (SM.seq_list_match c v (cbor_nondet_match p)) **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item v' /\
      Ghost.reveal v == List.Tot.map SpecRaw.mk_cbor v'
    )
decreases v
{
  SM.seq_list_match_length (cbor_nondet_match p) c v;
  if (Nil? v) {
    SM.seq_list_match_nil_elim c v (cbor_nondet_match p);
    SM.seq_list_match_nil_intro c [] (Raw.cbor_match p);
    intro
      (Trade.trade
        (SM.seq_list_match c [] (Raw.cbor_match p))
        (SM.seq_list_match c v (cbor_nondet_match p))
      )
      #emp
      fn _
    {
      SM.seq_list_match_nil_elim c [] (Raw.cbor_match p);
      SM.seq_list_match_nil_intro c v (cbor_nondet_match p);
    };
    []
  } else {
    SM.seq_list_match_cons_elim_trade c v (cbor_nondet_match p);
    let h = cbor_nondet_match_elim (Seq.head c);
    Trade.trans_hyp_l _ _ _ (SM.seq_list_match c v (cbor_nondet_match p));
    let q = seq_list_array_cbor_nondet_match_elim p (Seq.tail c) (List.Tot.tl v);
    Trade.trans_hyp_r _ _ _ (SM.seq_list_match c v (cbor_nondet_match p));
    SM.seq_list_match_cons_intro_trade (Seq.head c) (Ghost.reveal h) (Seq.tail c) q (Raw.cbor_match p);
    Trade.trans _ _ (SM.seq_list_match c v (cbor_nondet_match p));
    rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
    (Ghost.reveal h :: q);
  }
}

fn cbor_nondet_mk_array (_: unit) : mk_array_t #_ cbor_nondet_match
= (a: _)
  (#pa: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
{
  S.pts_to_len a;
  SM.seq_list_match_length (cbor_nondet_match pv) va vv;
  let len64 = SpecRaw.mk_raw_uint64 (SZ.sizet_to_uint64 (S.len a));
  let v' = seq_list_array_cbor_nondet_match_elim _ _ _;
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Array len64 v');
  SpecRaw.mk_cbor_eq (SpecRaw.Array len64 v');
  let res1 = Raw.cbor_match_array_intro len64 a;
  Trade.trans_concl_r _ _ _ _;
  cbor_nondet_match_intro res1;
  Trade.trans _ _ (_ ** _);
  let res = cbor_nondet_reset_perm () res1 1.0R;
  Trade.trans _ _ (_ ** _);
  Trade.rewrite_with_trade
    (cbor_nondet_match 1.0R res _)
    (cbor_nondet_match 1.0R res (Spec.pack (Spec.CArray (List.Tot.map SpecRaw.mk_cbor v'))));
  Trade.trans _ _ (_ ** _);
  res
}

ghost
fn rec seq_list_map_cbor_nondet_match_elim
  (p: perm)
  (c: Seq.seq cbor_nondet_map_entry_t)
  (v: list (Spec.cbor & Spec.cbor))
requires
  SM.seq_list_match c v (cbor_nondet_map_entry_match p)
returns v': Ghost.erased (list (SpecRaw.raw_data_item & SpecRaw.raw_data_item))
ensures
  SM.seq_list_match c v' (Raw.cbor_match_map_entry p) **
  Trade.trade
    (SM.seq_list_match c v' (Raw.cbor_match_map_entry p))
    (SM.seq_list_match c v (cbor_nondet_map_entry_match p)) **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v') /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v') /\
      Ghost.reveal v == List.Tot.map SpecRaw.mk_cbor_map_entry v'
    )
decreases v
{
  SM.seq_list_match_length (cbor_nondet_map_entry_match p) c v;
  if (Nil? v) {
    SM.seq_list_match_nil_elim c v (cbor_nondet_map_entry_match p);
    SM.seq_list_match_nil_intro c [] (Raw.cbor_match_map_entry p);
    intro
      (Trade.trade
        (SM.seq_list_match c [] (Raw.cbor_match_map_entry p))
        (SM.seq_list_match c v (cbor_nondet_map_entry_match p))
      )
      #emp
      fn _
    {
      SM.seq_list_match_nil_elim c [] (Raw.cbor_match_map_entry p);
      SM.seq_list_match_nil_intro c v (cbor_nondet_map_entry_match p);
    };
    []
  } else {
    SM.seq_list_match_cons_elim_trade c v (cbor_nondet_map_entry_match p);
    with w . assert (cbor_nondet_map_entry_match p (Seq.head c) w);
    Trade.rewrite_with_trade
      (cbor_nondet_map_entry_match p (Seq.head c) w)
      (cbor_nondet_match p (Seq.head c).cbor_map_entry_key (fst w) ** cbor_nondet_match p (Seq.head c).cbor_map_entry_value (snd w));
    let hfst = cbor_nondet_match_elim (Seq.head c).cbor_map_entry_key;
    let hsnd = cbor_nondet_match_elim (Seq.head c).cbor_map_entry_value;
    Trade.prod _ (cbor_nondet_match p (Seq.head c).cbor_map_entry_key _) _ (cbor_nondet_match p (Seq.head c).cbor_map_entry_value _);
    Trade.trans _ (cbor_nondet_match p (Seq.head c).cbor_map_entry_key (fst w) ** cbor_nondet_match p (Seq.head c).cbor_map_entry_value (snd w)) _;
    let h = (Ghost.reveal hfst, Ghost.reveal hsnd);
    Trade.rewrite_with_trade
      (Raw.cbor_match p (Seq.head c).cbor_map_entry_key hfst ** Raw.cbor_match p (Seq.head c).cbor_map_entry_value hsnd)
      (Raw.cbor_match_map_entry p (Seq.head c) h);
    Trade.trans (Raw.cbor_match_map_entry p (Seq.head c) h) _ _;
    Trade.trans_hyp_l _ _ _ (SM.seq_list_match c v (cbor_nondet_map_entry_match p));
    let q = seq_list_map_cbor_nondet_match_elim p (Seq.tail c) (List.Tot.tl v);
    Trade.trans_hyp_r _ _ _ (SM.seq_list_match c v (cbor_nondet_map_entry_match p));
    SM.seq_list_match_cons_intro_trade (Seq.head c) (Ghost.reveal h) (Seq.tail c) q (Raw.cbor_match_map_entry p);
    Trade.trans _ _ (SM.seq_list_match c v (cbor_nondet_map_entry_match p));
    rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
    (h :: q);
  }
}

let fits_mod (x: nat) (n: pos) : Lemma
    (requires (FStar.UInt.fits x n))
    (ensures (x % pow2 n == x))
= FStar.Math.Lemmas.small_mod x (pow2 n)

let _ : squash (pow2 64 - 1 == 18446744073709551615) = assert (pow2 64 - 1 == 18446744073709551615)

noextract [@@noextract_to "krml"]
let nlist_intro
  (#t: eqtype)
  (l: list t)
  (n: nat)
  (sq: squash (List.Tot.length l == n))
: Tot (SpecRaw.nlist t n)
= l

fn cbor_nondet_mk_map_entry (_: unit) : mk_map_entry_t #_ #_ cbor_nondet_match cbor_nondet_map_entry_match
=
  (xk: _)
  (xv: _)
  (#pk: perm)
  (#vk: _)
  (#pv: perm)
  (#vv: _)
{
  let xk' = cbor_nondet_reset_perm () xk 1.0R;
  let xv' = cbor_nondet_reset_perm () xv 1.0R;
  Trade.prod (cbor_nondet_match 1.0R xk' vk) _ (cbor_nondet_match 1.0R xv' vv) _;
  let res : cbor_nondet_map_entry_t = { cbor_map_entry_key = xk'; cbor_map_entry_value = xv' };
  Trade.rewrite_with_trade
    (cbor_nondet_match 1.0R xk' vk ** cbor_nondet_match 1.0R xv' vv)
    (cbor_nondet_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv));
  Trade.trans (cbor_nondet_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv)) _ _;
  res
}

fn cbor_nondet_mk_map_gen (_: unit)
: mk_map_gen_by_ref_t #cbor_nondet_t #cbor_nondet_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match
= (a: _)
  (dest: _)
  (#va: _)
  (#pv: _)
  (#vv: _)
  (#vdest0: _)
{
  S.pts_to_len a;
  SM.seq_list_match_length (cbor_nondet_map_entry_match pv) va vv;
  let _ : squash SZ.fits_u64 = assume (SZ.fits_u64);
  if (SZ.gt (S.len a) (SZ.uint64_to_sizet 18446744073709551615uL)) {
    Trade.refl (SM.seq_list_match va vv (cbor_nondet_map_entry_match pv));
    fold (mk_map_gen_post cbor_nondet_match cbor_nondet_map_entry_match a va pv vv None);
    false
  } else {
    let v' = seq_list_map_cbor_nondet_match_elim _ va vv;
    SpecRaw.list_no_repeats_map_fst_mk_cbor_map_entry v';
    let correct = CBOR.Pulse.Raw.Nondet.Compare.cbor_nondet_no_setoid_repeats a;
    if (correct) {
      SM.seq_list_match_length (Raw.cbor_match_map_entry pv) va v';
      let raw_len = SpecRaw.mk_raw_uint64 (SZ.sizet_to_uint64 (S.len a));
      fits_mod (SZ.v (S.len a)) U64.n;
      let sq : squash (List.Tot.length v' == U64.v raw_len.value) = ();
      let v'' : Ghost.erased (SpecRaw.nlist (SpecRaw.raw_data_item & SpecRaw.raw_data_item) (U64.v raw_len.value)) =
        nlist_intro v' (U64.v raw_len.value) sq
      ;
      let cr : Ghost.erased SpecRaw.raw_data_item = SpecRaw.Map raw_len v'';
      SpecRaw.valid_eq SpecRaw.basic_data_model cr;
      SpecRaw.mk_cbor_eq cr;
      let res1 = Raw.cbor_match_map_intro raw_len a;
      Trade.trans_concl_r _ _ _ _;
      cbor_nondet_match_intro res1;
      Trade.trans _ _ (_ ** _);
      let res = cbor_nondet_reset_perm () res1 1.0R;
      Trade.trans _ _ (_ ** _);
      let m : Ghost.erased Spec.cbor_map = Ghost.hide (Spec.CMap?.c (Spec.unpack (SpecRaw.mk_cbor cr)));
      Trade.rewrite_with_trade
        (cbor_nondet_match 1.0R res _)
        (cbor_nondet_match 1.0R res (Spec.pack (Spec.CMap m)));
      Trade.trans _ _ (_ ** _);
      Classical.forall_intro (SpecRaw.list_assoc_map_mk_cbor_map_entry m v' ());
      fold (mk_map_gen_post cbor_nondet_match cbor_nondet_map_entry_match a va pv vv (Some res));
      dest := res;
      true
    } else {
      Trade.elim _ _;
      Trade.refl (SM.seq_list_match va vv (cbor_nondet_map_entry_match pv));
      fold (mk_map_gen_post cbor_nondet_match cbor_nondet_map_entry_match a va pv vv None);
      false
    }
  }
}
