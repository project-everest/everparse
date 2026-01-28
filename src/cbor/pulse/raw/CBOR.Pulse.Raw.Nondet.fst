module CBOR.Pulse.Raw.Nondet
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
      rewrite each (p /. 2.0R +. p /. 2.0R) as p
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
  rewrite each (2.0R *. q /. 2.0R) as q;
  rewrite each (SpecRaw.mk_cbor r') as r;
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

fn cbor_nondet_parse (_: unit) : cbor_nondet_parse_t #cbor_nondet_t cbor_nondet_match =
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let len = cbor_nondet_validate () map_key_bound strict_check input;
  if (len = 0sz) {
    fold (cbor_nondet_parse_post cbor_nondet_match input pm v None);
    None
  } else {
    S.pts_to_len input;
    Seq.lemma_split v (SZ.v len);
    let (inl, inr) = S.split_trade input len;
    S.pts_to_len inl;
    S.pts_to_len inr;
    Spec.cbor_parse_prefix v (Seq.slice v 0 (SZ.v len));
    let resl = cbor_nondet_parse_valid () inl len;
    Trade.trans_hyp_l _ _ _ _;
    fold (cbor_nondet_parse_post_some cbor_nondet_match input pm v resl inr);
    fold (cbor_nondet_parse_post cbor_nondet_match input pm v (Some (resl, inr)));
    Some (resl, inr);
  }
}

let cbor_nondet_match_with_size
  (size: nat)
  (p: perm)
  (c: cbor_raw)
  (v: Spec.cbor)
: Tot slprop
= exists* v' . Raw.cbor_match p c v' ** pure (
    SpecRaw.valid_raw_data_item v' /\
    size == Seq.length (CBOR.Spec.Raw.Format.serialize_cbor v') /\
    SpecRaw.mk_cbor v' == v
  )

ghost fn cbor_nondet_match_with_size_intro (_: unit) : ghost_get_size_t #_ cbor_nondet_match cbor_nondet_match_with_size
= (x: _)
  (#p: _)
  (#x': _)
{
  unfold (cbor_nondet_match p x x');
  with y . assert (Raw.cbor_match p x y);
  let size = Seq.length (CBOR.Spec.Raw.Format.serialize_cbor y);
  fold (cbor_nondet_match_with_size size p x x');
  intro
    (Trade.trade
      (cbor_nondet_match_with_size size p x x')
      (cbor_nondet_match p x x')
    )
    fn _ {
      unfold (cbor_nondet_match_with_size size p x x');
      fold (cbor_nondet_match p x x')
    }
}

fn cbor_nondet_size (_: unit) : get_size_t #_ cbor_nondet_match_with_size
= (x: _)
  (bound: _)
  (#p: _)
  (#x': _)
  (#v: _)
{
  unfold (cbor_nondet_match_with_size v p x x');
  let res = CBOR.Pulse.Raw.Format.Serialize.cbor_size x bound;
  fold (cbor_nondet_match_with_size v p x x');
  res
}

fn cbor_nondet_serialize
  (_: unit)
: cbor_nondet_serialize_t #cbor_nondet_t cbor_nondet_match_with_size
=
  (x: _)
  (output: _)
  (#size: _)
  (#y: _)
  (#pm: _)
  (#v: _)
{
  unfold (cbor_nondet_match_with_size size pm x y);
  with pm' w . assert (CBOR.Pulse.Raw.Match.cbor_match pm' x w);
  S.pts_to_len output;
  let len = CBOR.Pulse.Raw.Format.Serialize.cbor_size x (S.len output);
  if (len = 0sz) {
    fold (cbor_nondet_match_with_size size pm x y);
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
    fold (cbor_nondet_match_with_size size pm x y);
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
      rewrite each (p /. 2.0R +. p /. 2.0R) as p
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

inline_for_extraction
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

fn cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
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

inline_for_extraction
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

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_map_get_by_ref (_: unit)
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

let cbor_nondet_map_get () = map_get_as_option (cbor_nondet_map_get_by_ref ())

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

fn cbor_nondet_mk_int64_gen (_: unit) : mk_int64_t u#0 #_ cbor_nondet_match
= (ty: _)
  (v: _)
{
  let res = Raw.cbor_match_int_intro ty (SpecRaw.mk_raw_uint64 v);
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Int64 ty (SpecRaw.mk_raw_uint64 v));
  SpecRaw.mk_cbor_eq (SpecRaw.Int64 ty (SpecRaw.mk_raw_uint64 v));
  fold (cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 ty v)));
  res
}

let cbor_nondet_mk_uint64 () v = cbor_nondet_mk_int64_gen () Spec.cbor_major_type_uint64 v

let cbor_nondet_mk_neg_int64 () v = cbor_nondet_mk_int64_gen () Spec.cbor_major_type_neg_int64 v

let cbor_nondet_mk_int64 () = mk_signed_int64 (cbor_nondet_mk_int64_gen ())

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

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_mk_map_gen_by_ref (_: unit)
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

inline_for_extraction
let dummy_cbor_nondet = CBOR_Case_Simple 0uy

let cbor_nondet_mk_map () = mk_map_gen dummy_cbor_nondet (cbor_nondet_mk_map_gen_by_ref ())

noextract [@noextract_to "krml"]
let set_snd_None
  (t1 t2: Type)
  (x: (t1 & option t2))
: Tot (t1 & option t2)
= (fst x, None)

module PM = Pulse.Lib.SeqMatch.Util

ghost fn trade_assoc_hyp_r2l
  (a b c d: slprop)
requires
  Trade.trade (a ** (b ** c)) d
ensures
  Trade.trade ((a ** b) ** c) d
{
  slprop_equivs ();
  rewrite Trade.trade (a ** (b ** c)) d as Trade.trade ((a ** b) ** c) d
}

ghost fn trade_assoc_hyp_l2r
  (a b c d: slprop)
requires
  Trade.trade ((a ** b) ** c) d
ensures
  Trade.trade (a ** (b ** c)) d
{
  slprop_equivs ();
  rewrite Trade.trade ((a ** b) ** c) d as Trade.trade (a ** (b ** c)) d
}

ghost fn trade_assoc_concl_r2l
  (a b c d: slprop)
requires
  Trade.trade a (b ** (c ** d))
ensures
  Trade.trade a ((b ** c) ** d)
{
  slprop_equivs ();
  rewrite Trade.trade a (b ** (c ** d)) as Trade.trade a ((b ** c) ** d)
}

ghost fn trade_assoc_concl_l2r
  (a b c d: slprop)
requires
  Trade.trade a ((b ** c) ** d)
ensures
  Trade.trade a (b ** (c ** d))
{
  slprop_equivs ();
  rewrite Trade.trade a ((b ** c) ** d) as Trade.trade a (b ** (c ** d))
}

let list_memP_map_intro_forall
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
: Lemma
  (requires True)
  (ensures (forall x . List.Tot.memP x l ==> List.Tot.memP (f x) (List.Tot.map f l)))
= let prf
    (x: a)
  : Lemma
    (ensures List.Tot.memP x l ==> List.Tot.memP (f x) (List.Tot.map f l))
  = List.Tot.memP_map_intro f x l
  in
  Classical.forall_intro prf

ghost fn lemma_trade_ab_cd_e
  (a b1 b2 c d1 d2 e: slprop)
requires
  Trade.trade (b1 ** d1) (b2 ** d2) **
  Trade.trade ((a ** b2) ** (c ** d2)) e
ensures
  Trade.trade ((a ** b1) ** (c ** d1)) e
{
  slprop_equivs ();
  rewrite (Trade.trade ((a ** b2) ** (c ** d2)) e) as Trade.trade ((a ** c) ** (b2 ** d2)) e;
  Trade.trans_hyp_r (a ** c) _ _ _;
  rewrite Trade.trade ((a ** c) ** (b1 ** d1)) e as (Trade.trade ((a ** b1) ** (c ** d1)) e)
}

ghost fn trade_prod_cancel_hyp_r_concl_l
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (b ** e)
ensures
  Trade.trade (a ** d) (c ** e)
{
  intro
    (Trade.trade (a ** d) (c ** e))
    #(Trade.trade (a ** b) c ** Trade.trade d (b ** e))
    fn _ {
      Trade.elim d _;
      Trade.elim (a ** b) _
    }
}

ghost fn trade_prod_cancel_hyp_l_concl_l
  (b #a #c #d #e: slprop)
requires
  Trade.trade (b ** a) c ** Trade.trade d (b ** e)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (b ** a) c as Trade.trade (a ** b) c;
  trade_prod_cancel_hyp_r_concl_l b
}

ghost fn trade_prod_cancel_hyp_r_concl_r
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade d (e ** b) as Trade.trade d (b ** e);
  trade_prod_cancel_hyp_r_concl_l b
}

ghost fn trade_prod_cancel_hyp_l_concl_r
  (b #a #c #d #e: slprop)
requires
  Trade.trade (b ** a) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (b ** a) c as Trade.trade (a ** b) c;
  trade_prod_cancel_hyp_r_concl_r b;
}

ghost fn trade_prod_cancel_concl_r_hyp_l
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (c ** d) e as Trade.trade (d ** c) e;
  trade_prod_cancel_hyp_r_concl_r c;
  rewrite Trade.trade (d ** a) (e ** b) as Trade.trade (a ** d) (b ** e)
}

ghost fn trade_prod_cancel_concl_l_hyp_l
  (#a c #b #d #e: slprop)
requires
  Trade.trade a (c ** b) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade a (c ** b) as Trade.trade a (b ** c);
  trade_prod_cancel_concl_r_hyp_l c;
}

ghost fn trade_prod_cancel_concl_r_hyp_r
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (d ** c) e as Trade.trade (c ** d) e;
  trade_prod_cancel_concl_r_hyp_l c
}

ghost fn trade_prod_cancel_concl_l_hyp_r
  (#a c #b #d #e: slprop)
requires
  Trade.trade a (c ** b) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade a (c ** b) as Trade.trade a (b ** c);
  trade_prod_cancel_concl_r_hyp_r c
}

ghost fn trade_comm_concl
  (a b c: slprop)
requires Trade.trade a (b ** c)
ensures Trade.trade a (c ** b)
{
  slprop_equivs();
  rewrite Trade.trade a (b ** c) as Trade.trade a (c ** b)
}

let lemma_seq_assoc_cons
  (#t: Type)
  (a: Seq.seq t)
  (b: t)
  (c: Seq.seq t)
: Lemma
  (Seq.equal (Seq.append a (Seq.cons b c)) (Seq.append (Seq.append a (Seq.cons b Seq.empty)) c))
= ()

let lemma_seq_assoc_cons_upd
  (#t: Type)
  (a: Seq.seq t)
  (c: Seq.seq t)
  (b': t)
: Lemma
  (requires Seq.length c > 0)
  (ensures Seq.equal
    (Seq.upd (Seq.append a c) (Seq.length a) b')
    (Seq.append (Seq.append a (Seq.cons b' Seq.empty)) (Seq.tail c))
  )
= ()

ghost fn lemma_trade_rewrite5
  (a b c d ef: slprop)
requires
   Trade.trade (((a **
        b) **
        c) **
        d)
      (ef)
ensures
   Trade.trade (a ** (d ** b ** c))
      (ef)
{
  slprop_equivs ();
  rewrite
   Trade.trade (((a **
        b) **
        c) **
        d)
      (ef)
  as Trade.trade (a ** (d ** b ** c))
      (ef)
}

ghost fn cbor_map_get_multiple_entry_match_snd_prop
  (#t: Type0)
  (vmatch: perm -> t -> Spec.cbor -> slprop)
  (x: cbor_map_get_multiple_entry_t t)
  (y: option Spec.cbor)
requires
  cbor_map_get_multiple_entry_match_snd vmatch true x y
ensures
  cbor_map_get_multiple_entry_match_snd vmatch true x y **
  pure (x.found == Some? y)
{
  if (x.found <> Some? y) {
    rewrite cbor_map_get_multiple_entry_match_snd vmatch true x y as pure False;
    rewrite emp as cbor_map_get_multiple_entry_match_snd vmatch true x y
  }
}

#push-options "--z3rlimit 64"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_map_get_multiple (_: unit) : cbor_map_get_multiple_t #_ cbor_nondet_match
=
  (map: _)
  (dest: _)
  (#pmap: _)
  (#vmap: _)
  (#s: _)
  (#ps: _)
  (#v: _)
{
  PM.seq_list_match_nil_intro
    Seq.empty
    (List.Tot.map (set_snd_None Spec.cbor Spec.cbor) [])
    (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
  intro
    (Trade.trade
      (PM.seq_list_match
        Seq.empty
        (List.Tot.map (set_snd_None Spec.cbor Spec.cbor) [])
        (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
        (PM.seq_list_match s v (cbor_map_get_multiple_entry_match cbor_nondet_match false ps))
      )
      (PM.seq_list_match s v (cbor_map_get_multiple_entry_match cbor_nondet_match false ps))
    )
    fn _ {
      PM.seq_list_match_nil_elim Seq.empty _ (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
      ()
    };
  S.pts_to_len dest;
  let mut pi = 0sz;
  while (
    let i = !pi;
    (SZ.lt i (S.len dest))
  ) invariant b . exists* i s' s1 s2 l1 l2 . (
    pts_to pi i **
    pts_to dest s' **
    PM.seq_list_match s1 l1 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
    PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps) **
    Trade.trade
      (PM.seq_list_match s1 l1 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
        PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps))
      (PM.seq_list_match s v (cbor_map_get_multiple_entry_match cbor_nondet_match false ps)) **
    pure (
      Seq.length s == Seq.length s' /\
      Seq.equal s' (Seq.append s1 s2) /\
      List.Tot.map fst v == List.Tot.map fst (List.Tot.append l1 l2) /\
      Seq.equal (seq_map Mkcbor_map_get_multiple_entry_t?.key s') (seq_map Mkcbor_map_get_multiple_entry_t?.key s) /\
      (forall x . List.Tot.memP x l1 ==> snd x == None) /\
      List.Tot.count None (List.Tot.map snd l1) == List.Tot.length l1 /\
      SZ.v i == Seq.length s1 /\
      b == (SZ.v i < Seq.length s)
    )
  ) {
    with s1 s2 l1 l2 . assert (
      PM.seq_list_match s1 l1 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
      PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps)
    );
    PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _;
    PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match false ps) _ _;
    PM.seq_list_match_cons_elim_trade s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps);
    let i = !pi;
    let x = S.op_Array_Access dest i;
    assert (pure (x == Seq.head s2));
    let x' = { x with found = false };
    S.op_Array_Assignment dest i x';
    slprop_equivs ();
    let y' : Ghost.erased (Spec.cbor & option Spec.cbor) = Ghost.hide (set_snd_None _ _ (List.Tot.hd l2));
    Trade.rewrite_with_trade
      (cbor_map_get_multiple_entry_match cbor_nondet_match false ps (Seq.head s2) (List.Tot.hd l2))
      (cbor_map_get_multiple_entry_match cbor_nondet_match true ps x' y');
    Trade.trans_hyp_l _ _ _ (PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps));
    PM.seq_list_match_singleton_intro_trade x' (Ghost.reveal y') (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
    Trade.trans_hyp_l _ _ _ (PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps));
    Trade.trans_hyp_r _ _ _ (PM.seq_list_match s v (cbor_map_get_multiple_entry_match cbor_nondet_match false ps));
    trade_assoc_hyp_r2l _ _ _ _;
    PM.seq_list_match_append_intro_trade (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) s1 l1 _ _;
    Trade.trans_hyp_l _ _ _ _;
    List.Tot.map_append fst l1 l2;
    List.Tot.append_assoc (List.Tot.map fst l1) [fst y'] (List.Tot.map fst (List.Tot.tl l2));
    List.Tot.map_append fst l1 [(Ghost.reveal y')];
    List.Tot.append_memP_forall l1 [Ghost.reveal y'];
    List.Tot.map_append fst (List.Tot.append l1 [Ghost.reveal y']) (List.Tot.tl l2);
    List.Tot.map_append snd l1 [Ghost.reveal y'];
    List.Tot.append_count (List.Tot.map snd l1) [snd y'] None;
    pi := SZ.add i 1sz;
  };
  with s1_ s2_ l1_ l2_ . assert (
    PM.seq_list_match s1_ l1_ (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
    PM.seq_list_match s2_ l2_ (cbor_map_get_multiple_entry_match cbor_nondet_match false ps)
  );
  PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _;
  PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match false ps) _ _;
  List.Tot.append_l_nil l1_;
  Trade.elim_hyp_r _ _ _;
  with s' . assert (S.pts_to dest s');
  assert (pure (Seq.equal s' s1_));
  rewrite (S.pts_to dest s') as (S.pts_to dest s1_);
  let m = Ghost.hide (Spec.CMap?.c (Spec.unpack vmap));
  let iter = cbor_nondet_map_iterator_start () map;
  Trade.prod _ (cbor_nondet_match pmap map vmap) _ _;
  let mut piter = iter;
  while (
    let i = !pi;
    if (i = 0sz) {
      false
    } else {
      let iter = !piter;
      not (cbor_nondet_map_iterator_is_empty () iter)
    }
  ) invariant b . exists* i iter l s0 l0 pmi . (
    pts_to pi i **
    pts_to piter iter **
    S.pts_to dest s0 **
    cbor_nondet_map_iterator_match pmi iter l **
    PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
    Trade.trade
      (cbor_nondet_map_iterator_match pmi iter l **
        PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
      )
      (cbor_nondet_match pmap map vmap ** 
        PM.seq_list_match s v (cbor_map_get_multiple_entry_match cbor_nondet_match false ps)
      ) **
    pure (
      Seq.equal (seq_map Mkcbor_map_get_multiple_entry_t?.key s0) (seq_map Mkcbor_map_get_multiple_entry_t?.key s) /\
      List.Tot.map fst l0 == List.Tot.map fst v /\
      List.Tot.count None (List.Tot.map snd l0) == SZ.v i /\
      List.Tot.no_repeats_p (List.Tot.map fst l) /\
      (forall x . Some? (List.Tot.assoc x l) ==> Spec.cbor_map_get m x == List.Tot.assoc x l) /\
      (forall x . List.Tot.memP x l0 ==> Spec.cbor_map_get m (fst x) == (match snd x with None -> List.Tot.assoc (fst x) l | Some z -> Some z)) /\
      b == (Cons? l && SZ.v i > 0)
    )
  ) {
    let entry = cbor_nondet_map_iterator_next () piter;
    Trade.trans_hyp_l _ (cbor_nondet_map_iterator_match _ _ _) _ _;
    trade_assoc_hyp_l2r _ _ _ _;
    with pentry ventry . assert (cbor_nondet_map_entry_match pentry entry ventry);
    Trade.rewrite_with_trade
      (cbor_nondet_map_entry_match pentry entry ventry)
      (cbor_nondet_match pentry entry.cbor_map_entry_key (fst ventry) **
        cbor_nondet_match pentry entry.cbor_map_entry_value (snd ventry)
      );
    Trade.trans_hyp_l _ (cbor_nondet_map_entry_match _ _ _) _ _;
    with s0 l0 . assert (PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
    Seq.append_empty_l s0;
    Trade.rewrite_with_trade
      (cbor_nondet_match pentry entry.cbor_map_entry_value (snd ventry) ** PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps))
      (cbor_nondet_match pentry entry.cbor_map_entry_value (snd ventry) ** PM.seq_list_match (Seq.append Seq.empty s0) (List.Tot.append [] l0) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
    let mut pj = 0sz;
    S.pts_to_len dest;
    with iter pmi l . assert (cbor_nondet_map_iterator_match pmi iter l);
    List.Tot.assoc_mem (fst ventry) l;
    while (
      let j = !pj;
      let i = !pi;
      (SZ.lt j (S.len dest) && SZ.gt i 0sz)
    ) invariant b . exists* i j pvalue s' s1 l1 s2 l2 . (
      pts_to pi i **
      pts_to pj j **
      S.pts_to dest s' **
      cbor_nondet_match pvalue entry.cbor_map_entry_value (snd ventry) ** 
      PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
      Trade.trade
        (cbor_nondet_match pvalue entry.cbor_map_entry_value (snd ventry) ** 
          PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
        )
        (cbor_nondet_match pentry entry.cbor_map_entry_value (snd ventry) ** 
          PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
        ) **
      cbor_nondet_match pentry entry.cbor_map_entry_key (fst ventry) ** 
      pure (b == (SZ.v j < SZ.v (S.len dest) && SZ.v i > 0) /\
        List.Tot.map fst (List.Tot.append l1 l2) == List.Tot.map fst v /\
        List.Tot.count None (List.Tot.map snd (List.Tot.append l1 l2)) == SZ.v i /\
        Seq.equal (seq_map Mkcbor_map_get_multiple_entry_t?.key s') (seq_map Mkcbor_map_get_multiple_entry_t?.key s) /\
        Seq.equal s' (Seq.append s1 s2) /\
        Seq.length s' == SZ.v (S.len dest) /\
        SZ.v j <= SZ.v (S.len dest) /\
        (forall x . List.Tot.memP x l1 ==> Spec.cbor_map_get m (fst x) == (match snd x with None -> List.Tot.assoc (fst x) l | Some z -> Some z)) /\
        (forall x . List.Tot.memP x l2 ==> Spec.cbor_map_get m (fst x) == (match snd x with None -> List.Tot.assoc (fst x) (Ghost.reveal ventry :: l) | Some z -> Some z)) /\
        SZ.v j == Seq.length s1 /\
        Seq.length s1 == List.Tot.length l1
      )
    ) {
      with pvalue . assert (cbor_nondet_match pvalue entry.cbor_map_entry_value (snd ventry));
      S.pts_to_len dest;
      PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _;
      with s1 s2 l1 l2 . assert (PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
      List.Tot.append_length l1 l2;
      PM.seq_list_match_append_elim_trade (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _ _ _;
      PM.seq_list_match_cons_elim_trade s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
      let j = !pj;
      pj := SZ.add j 1sz;
      let dest_entry = S.op_Array_Access dest j;
      Trade.rewrite_with_trade
        (cbor_map_get_multiple_entry_match cbor_nondet_match true ps (Seq.head s2) (List.Tot.hd l2))
        (cbor_nondet_match ps dest_entry.key (fst (List.Tot.hd l2)) **
          cbor_map_get_multiple_entry_match_snd cbor_nondet_match true dest_entry (snd (List.Tot.hd l2)));
      cbor_map_get_multiple_entry_match_snd_prop cbor_nondet_match dest_entry (snd (List.Tot.hd l2));
      Trade.elim_hyp_r _ (cbor_map_get_multiple_entry_match_snd cbor_nondet_match true dest_entry (snd (List.Tot.hd l2))) _;
      if (cbor_nondet_equal dest_entry.key entry.cbor_map_entry_key) {
        let pvalue' = share_gather_trade (cbor_nondet_share ()) (cbor_nondet_gather ()) entry.cbor_map_entry_value;
        let entry_value = cbor_nondet_reset_perm () entry.cbor_map_entry_value 1.0R;
        Trade.trans_hyp_r _ (cbor_nondet_match 1.0R entry_value _) _ _;
        let dest_entry' = { dest_entry with found = true; value = entry_value };
        S.op_Array_Assignment dest j dest_entry';
        Trade.rewrite_with_trade
          (cbor_nondet_match ps dest_entry.key (fst (List.Tot.hd l2)) **
            cbor_nondet_match 1.0R entry_value (snd ventry)
          )
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps dest_entry' (fst (List.Tot.hd l2), Some (snd ventry)));
        PM.seq_list_match_cons_intro_trade _ _ (Seq.tail s2) (List.Tot.tl l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
        PM.seq_list_match_append_intro_trade (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) s1 l1 _ _;
        lemma_seq_assoc_cons s1 dest_entry' (Seq.tail s2);
        List.Tot.append_assoc l1 [(fst (List.Tot.hd l2), Some (snd ventry))] (List.Tot.tl l2);
        Trade.rewrite_with_trade
          (PM.seq_list_match _ _ (cbor_map_get_multiple_entry_match cbor_nondet_match true ps))
          (PM.seq_list_match
            (Seq.append (Seq.append s1 (Seq.cons dest_entry' Seq.empty)) (Seq.tail s2))
            (List.Tot.append (List.Tot.append l1 [(fst (List.Tot.hd l2), Some (snd ventry))]) (List.Tot.tl l2))
            (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
          );
        Trade.trans
          (PM.seq_list_match
            (Seq.append (Seq.append s1 (Seq.cons dest_entry' Seq.empty)) (Seq.tail s2))
            (List.Tot.append (List.Tot.append l1 [(fst (List.Tot.hd l2), Some (snd ventry))]) (List.Tot.tl l2))
            (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
          ) _ _;
        Trade.trans_concl_l _ (cbor_nondet_match ps dest_entry.key (fst (List.Tot.hd l2))) _ _;
        trade_prod_cancel_hyp_r_concl_r (cbor_nondet_match 1.0R _ _);
        trade_prod_cancel_concl_r_hyp_l (cbor_map_get_multiple_entry_match cbor_nondet_match
          true
          ps
          (Seq.Properties.head s2)
          (List.Tot.Base.hd l2));
        trade_prod_cancel_concl_r_hyp_r (Pulse.Lib.SeqMatch.seq_list_match s2
          l2
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        Trade.trans _ (cbor_nondet_match pvalue _ _ ** _) _;
        Trade.trans_concl_r _ _ (Pulse.Lib.SeqMatch.seq_list_match (Seq.Base.cons dest_entry'
              (Seq.Properties.tail s2))
          ((fst (List.Tot.Base.hd l2), Some (snd ventry)) :: List.Tot.Base.tl l2)
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)) _;
        lemma_trade_rewrite5 _ _ _ _ _;
        Trade.trans_hyp_r _ _ _ _;
        let lx = Ghost.hide [(fst (List.Tot.Base.hd l2), Some (snd ventry))];
        with s' . assert (S.pts_to dest s');
        with s1' s2' l1' l2' . assert (Pulse.Lib.SeqMatch.seq_list_match (Seq.append s1' s2') (List.Tot.append l1' l2') (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        lemma_seq_assoc_cons_upd s1 s2 dest_entry';
        assert (pure (Seq.equal s' (Seq.append s1' s2')));
        assert (pure (l1' == List.Tot.append l1 lx));
        assert (pure (l2' == List.Tot.tl l2));
        List.Tot.map_append fst l1 l2;
        List.Tot.map_append fst l1 lx;
        List.Tot.map_append fst l1' (List.Tot.tl l2);
        List.Tot.append_assoc (List.Tot.map fst l1) (List.Tot.map fst lx) (List.Tot.map fst (List.Tot.tl l2));
        List.Tot.map_append snd l1 l2;
        List.Tot.map_append snd l1 lx;
        List.Tot.map_append snd l1' (List.Tot.tl l2);
        List.Tot.append_count (List.Tot.map snd l1) (List.Tot.map snd l2) None;
        List.Tot.append_count (List.Tot.map snd l1) (List.Tot.map snd lx) None;
        List.Tot.append_count (List.Tot.map snd l1') (List.Tot.map snd (List.Tot.tl l2)) None;
        assert (pure (List.Tot.count None (List.Tot.map snd (List.Tot.append l1 l2)) == List.Tot.count None (List.Tot.map snd l1) + List.Tot.count None (List.Tot.map snd l2)));
        assert (pure (List.Tot.count None (List.Tot.map snd (List.Tot.append l1' (List.Tot.tl l2))) == List.Tot.count None (List.Tot.map snd l1) + List.Tot.count None (List.Tot.map snd lx) + List.Tot.count None (List.Tot.map snd (List.Tot.tl l2))));
        assert (pure (List.Tot.count None (List.Tot.map snd lx) == 0));
        assert (pure (List.Tot.count None (List.Tot.map snd l2) == (if dest_entry.found then 0 else 1) + List.Tot.count None (List.Tot.map snd (List.Tot.tl l2))));
        List.Tot.append_memP_forall l1 lx;
        assert (pure (forall x . List.Tot.memP x l1' ==> Spec.cbor_map_get m (fst x) == (match snd x with None -> List.Tot.assoc (fst x) l | Some z -> Some z)));
        List.Tot.append_length l1 lx;
        if (not dest_entry.found) { // TODO: I can remove this `if`, but at the expense of maintaining the left-hand-side list of already-seen items from the iterator in the enclosing loop.
          let i = !pi;
          pi := SZ.sub i 1sz;
        }
      } else {
        Trade.elim _ (cbor_map_get_multiple_entry_match cbor_nondet_match true ps (Seq.head s2) (List.Tot.hd l2));
        Trade.elim _ (Pulse.Lib.SeqMatch.seq_list_match s2
          l2
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        Trade.elim _ (Pulse.Lib.SeqMatch.seq_list_match (Seq.Base.append s1 s2)
          (List.Tot.append l1 l2)
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        List.Tot.append_assoc l1 [List.Tot.hd l2] (List.Tot.tl l2);
        List.Tot.append_memP_forall l1 [List.Tot.hd l2];
        List.Tot.append_length l1 [List.Tot.hd l2];
        Seq.cons_head_tail s2;
        assert (pure (Seq.equal s2 (Seq.append (Seq.cons (Seq.head s2) Seq.empty) (Seq.tail s2))));
        Seq.append_assoc s1 (Seq.cons (Seq.head s2) Seq.empty) (Seq.tail s2);
        assert (pure (Seq.equal (Seq.append s1 s2) (Seq.append (Seq.append s1 (Seq.cons (Seq.head s2) Seq.empty)) (Seq.tail s2))));
        Trade.rewrite_with_trade
          (Pulse.Lib.SeqMatch.seq_list_match (Seq.append s1 s2)
            (List.Tot.append l1 l2)
            (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
          )
          (Pulse.Lib.SeqMatch.seq_list_match (Seq.append (Seq.append s1 (Seq.cons (Seq.head s2) Seq.empty)) (Seq.tail s2))
            (List.Tot.append (List.Tot.append l1 [List.Tot.hd l2]) (List.Tot.tl l2))
            (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
          );
        Trade.trans_hyp_r _ _ (Pulse.Lib.SeqMatch.seq_list_match (Seq.Base.append s1 s2)
          (List.Tot.append l1 l2)
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)) _;
        ()
      }
    };
    S.pts_to_len dest;
    PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _;
    with s1 s2 l1 l2 . assert (PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
//    let j = !pj;
    with gi . assert (pts_to pi gi);
    lemma_trade_ab_cd_e _ _ _ _ _ _ _;
    Trade.elim_hyp_l _ _ _;
//    if (SZ.lt j (S.len dest)) {
      List.Tot.map_append snd l1 l2;
      List.Tot.append_count (List.Tot.map snd l1) (List.Tot.map snd l2) None;
      List.Tot.append_memP_forall l1 l2;
      List.Tot.mem_count (List.Tot.map snd l2) None;
      List.Tot.mem_memP None (List.Tot.map snd l2);
      list_memP_map_intro_forall snd l2;
      assert (pure (forall x . (List.Tot.memP x l2 /\ SZ.v gi == 0) ==> Some? (snd x)));
//      ()
//    } else {
      List.Tot.append_length l1 l2;
//      assert (pure (Nil? l2));
      List.Tot.append_l_nil l1;
//    }
  };
  Trade.elim_hyp_l _ _ _;
  with s' l' . assert (PM.seq_list_match s' l' (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
  List.Tot.mem_count (List.Tot.map snd l') None;
  List.Tot.mem_memP None (List.Tot.map snd l');
  list_memP_map_intro_forall snd l';
  ()
}

#pop-options

(* SLProp-to-Prop abstraction vehicle to prove the correctness of type abstraction in the Rust API *)

let cbor_nondet_case (x: cbor_nondet_t) : Tot cbor_nondet_case_t =
  match x with
  | Raw.CBOR_Case_Int _ -> CaseInt64
  | Raw.CBOR_Case_String _ -> CaseString
  | Raw.CBOR_Case_Tagged _
  | Raw.CBOR_Case_Serialized_Tagged _
    -> CaseTagged
  | Raw.CBOR_Case_Array _
  | Raw.CBOR_Case_Serialized_Array _
    -> CaseArray
  | Raw.CBOR_Case_Map _
  | Raw.CBOR_Case_Serialized_Map _
    -> CaseMap
  | Raw.CBOR_Case_Simple _ -> CaseSimpleValue

#push-options "--z3rlimit 32"

ghost
fn cbor_nondet_case_correct
  (x: cbor_nondet_t)
  (#p: perm)
  (#v: Spec.cbor)
requires
    (cbor_nondet_match p x v)
ensures
    (cbor_nondet_match p x v ** pure (cbor_nondet_case_correct_post x v))
{
  cbor_nondet_match_elim x;
  with p' v' . assert (Raw.cbor_match p' x v');
  Raw.cbor_match_cases x;
  SpecRaw.mk_cbor_eq v';
  Trade.elim _ _;
}

#pop-options
