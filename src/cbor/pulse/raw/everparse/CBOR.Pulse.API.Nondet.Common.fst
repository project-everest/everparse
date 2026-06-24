module CBOR.Pulse.API.Nondet.Common
#lang-pulse
friend CBOR.Pulse.API.Nondet.Type
friend CBOR.Spec.API.Format

open Pulse.Lib.Pervasives
open CBOR.Spec.Constants
open CBOR.Pulse.API.Base
open FStar.List.Tot

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module SM = Pulse.Lib.SeqMatch
module PMU = Pulse.Lib.SeqMatch.Util
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module I64 = FStar.Int64
module SU = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference

module SpecRawBase = CBOR.Spec.Raw.Base
module SpecRaw = CBOR.Spec.Raw
module RawType = CBOR.Pulse.Raw.EverParse.Type
module RawMatch = CBOR.Pulse.Raw.EverParse.Match
module Access = CBOR.Pulse.Raw.EverParse.Access
module RawMake = CBOR.Pulse.Raw.EverParse.Make
module ReadMapEntry = CBOR.Pulse.Raw.EverParse.ReadMapEntry
module RawSerialize = CBOR.Pulse.Raw.EverParse.Serialize
module ReadFields = CBOR.Pulse.Raw.EverParse.ReadFields
module ReadMapEntry = CBOR.Pulse.Raw.EverParse.ReadMapEntry
module Read = CBOR.Pulse.Raw.EverParse.Read
module Validate = CBOR.Pulse.Raw.EverParse.Validate
module NondetValidate = CBOR.Pulse.Raw.Format.Nondet.Validate
module NondetCompare = CBOR.Pulse.Raw.EverParse.Nondet.Compare
module NondetBasic = CBOR.Pulse.Raw.EverParse.Nondet.Basic
module NondetGen = CBOR.Pulse.Raw.EverParse.Nondet.Gen
module ResetPerm = CBOR.Pulse.Raw.EverParse.ResetPerm
module SpecF = CBOR.Spec.Raw.Format
module SpecRawEverParse = CBOR.Spec.Raw.EverParse
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module Proj = LowParse.PulseParse.Projectors

(* ============ Core match relation ============ *)

let cbor_nondet_match
  (p: perm)
  (c: cbor_nondet_t)
  (v: Spec.cbor)
: Tot slprop
= exists* v' . RawMatch.cbor_raw_match p c v' ** pure (
    SpecRaw.valid_raw_data_item v' /\
    SpecRaw.mk_cbor v' == v
  )

ghost fn cbor_nondet_match_elim
  (c: cbor_nondet_t)
  (#p: perm)
  (#v: Spec.cbor)
requires
  cbor_nondet_match p c v
returns v': Ghost.erased SpecRawBase.raw_data_item
ensures
  RawMatch.cbor_raw_match p c v' **
  Trade.trade
    (RawMatch.cbor_raw_match p c v')
    (cbor_nondet_match p c v) **
  pure (
    SpecRaw.valid_raw_data_item v' /\
    SpecRaw.mk_cbor v' == v
  )
{
  unfold (cbor_nondet_match p c v);
  with v' . assert (RawMatch.cbor_raw_match p c v');
  Trade.intro_trade
    (RawMatch.cbor_raw_match p c v')
    (cbor_nondet_match p c v)
    emp
    fn _ {
      fold (cbor_nondet_match p c v)
    };
  v'
}

ghost fn cbor_nondet_match_intro
  (c: cbor_nondet_t)
  (#p: perm)
  (#v: SpecRawBase.raw_data_item)
requires
  RawMatch.cbor_raw_match p c v **
  pure (
    SpecRaw.valid_raw_data_item v
  )
ensures
  cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v) **
  Trade.trade
    (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v))
    (RawMatch.cbor_raw_match p c v)
{
  RawMatch.cbor_raw_match_share c #p #v;
  fold (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v));
  Trade.intro_trade
    (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v))
    (RawMatch.cbor_raw_match p c v)
    (RawMatch.cbor_raw_match (p /. 2.0R) c v)
    fn _ {
      unfold (cbor_nondet_match (p /. 2.0R) c (SpecRaw.mk_cbor v));
      RawMatch.cbor_raw_match_gather c #(p /. 2.0R) #v;
      rewrite each (p /. 2.0R +. p /. 2.0R) as p
    }
}

(* ============ Reset perm ============ *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_reset_perm (_: unit) : reset_perm_t #_ cbor_nondet_match
=
  (c: cbor_nondet_t)
  (#p: perm)
  (#r: Ghost.erased Spec.cbor)
  (q: perm)
{
  let r' = cbor_nondet_match_elim c;
  let res = ResetPerm.cbor_raw_reset_perm p c (2.0R *. q);
  Trade.trans _ _ (cbor_nondet_match p c r);
  cbor_nondet_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p c r);
  rewrite each (2.0R *. q /. 2.0R) as q;
  rewrite each (SpecRaw.mk_cbor (Ghost.reveal r')) as Ghost.reveal r;
  res
}

(* ============ Share / Gather ============ *)

ghost
fn cbor_nondet_share
  (_: unit)
: CBOR.Pulse.API.Base.share_t u#0 u#0 #_ #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  RawMatch.cbor_raw_match_share x;
  fold (cbor_nondet_match (p /. 2.0R) x v);
  fold (cbor_nondet_match (p /. 2.0R) x v)
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
  with vA . assert (RawMatch.cbor_raw_match p x vA);
  with vB . assert (RawMatch.cbor_raw_match p' x vB);
  RawMatch.cbor_raw_match_gather x #p #vA #p' #vB;
  fold (cbor_nondet_match (p +. p') x v)
}

(* ============ Parse ============ *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_validate (_: unit) : cbor_nondet_validate_t
=
  (map_key_bound: _)
  (strict_check: _)
  (input: _)
  (#pm: _)
  (#v: _)
{
  Classical.forall_intro (Classical.move_requires SpecRaw.mk_cbor_map_key_depth);
  NondetValidate.cbor_validate_nondet map_key_bound strict_check input
}

let cbor_nondet_parse_valid_serialize_lemma
  (v: Seq.seq U8.t)
  (len: SZ.t)
: Lemma
  (requires cbor_nondet_validate_post None false v len /\ SZ.v len > 0)
  (ensures
    SZ.v len <= Seq.length v /\
    (exists v1 v2 . Ghost.reveal v == SpecF.serialize_cbor v1 `Seq.append` v2 /\ SZ.v len == Seq.length (SpecF.serialize_cbor v1))
  )
= let Some (y, n) = SpecF.parse_cbor v in
  SpecF.serialize_parse_cbor y;
  Seq.lemma_split v n;
  assert (v == SpecF.serialize_cbor y `Seq.append` Seq.slice v n (Seq.length v))

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_parse_valid (_: unit) : cbor_nondet_parse_valid_t #cbor_nondet_t cbor_nondet_match
=
  (input: S.slice U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  S.pts_to_len input;
  cbor_nondet_parse_valid_serialize_lemma v len;
  Seq.lemma_split v (SZ.v len);
  // Split the input into prefix (the cbor) and remainder
  let s1s2 = S.split input #pm len;
  let s1 = fst s1s2;
  let s2 = snd s1s2;
  rewrite (pts_to (fst s1s2) #pm (Seq.slice v 0 (SZ.v len))) as (pts_to s1 #pm (Seq.slice v 0 (SZ.v len)));
  rewrite (pts_to (snd s1s2) #pm (Seq.slice v (SZ.v len) (Seq.length v))) as (pts_to s2 #pm (Seq.slice v (SZ.v len) (Seq.length v)));
  rewrite (S.is_split input (fst s1s2) (snd s1s2)) as (S.is_split input s1 s2);
  S.pts_to_len s1;
  S.pts_to_len s2;
  let v1g : Ghost.erased (Seq.seq U8.t) = Ghost.hide (Seq.slice v 0 (SZ.v len));
  let v2g : Ghost.erased (Seq.seq U8.t) = Ghost.hide (Seq.slice v (SZ.v len) (Seq.length v));
  rewrite (pts_to s1 #pm (Seq.slice v 0 (SZ.v len))) as (pts_to s1 #pm v1g);
  rewrite (pts_to s2 #pm (Seq.slice v (SZ.v len) (Seq.length v))) as (pts_to s2 #pm v2g);
  // Build trade: pts_to s1 #pm v1g => pts_to input #pm v
  Trade.intro_trade
    (pts_to s1 #pm v1g)
    (pts_to input #pm v)
    (pts_to s2 #pm v2g ** S.is_split input s1 s2)
    fn _ {
      S.join s1 s2 input;
      rewrite (pts_to input #pm (Seq.append v1g v2g)) as (pts_to input #pm v)
    };
  // Now call cbor_parse_valid on s1
  let res = CBOR.Pulse.Raw.EverParse.Det.Validate.cbor_parse_valid s1;
  with v1 . assert (RawMatch.cbor_raw_match 1.0R res v1);
  // We have: v1g == serialize_cbor v1
  SpecF.serialize_parse_cbor v1;
  // SpecF.parse_cbor v1g == Some (v1, |serialize v1|)
  // Spec.cbor_parse v: by definition, looks up RF.parse_cbor v, which by parse_cbor_prefix == RF.parse_cbor v1g (same first len bytes)
  SpecF.parse_cbor_prefix v1g v;
  Trade.trans _ _ (pts_to input #pm v);
  cbor_nondet_match_intro res;
  Trade.trans _ _ (pts_to input #pm v);
  res
}

(* ============ Match with size / size / serialize ============ *)

let cbor_nondet_match_with_size
  (size: nat)
  (p: perm)
  (c: cbor_nondet_t)
  (v: Spec.cbor)
: Tot slprop
= exists* v' . RawMatch.cbor_raw_match p c v' ** pure (
    SpecRaw.valid_raw_data_item v' /\
    size == Seq.length (SpecF.serialize_cbor v') /\
    SpecRaw.mk_cbor v' == v
  )

ghost
fn cbor_nondet_match_with_size_intro (_: unit) : ghost_get_size_t #_ cbor_nondet_match cbor_nondet_match_with_size
= (x: _)
  (#p: _)
  (#x': _)
{
  unfold (cbor_nondet_match p x x');
  with y . assert (RawMatch.cbor_raw_match p x y);
  let size = Seq.length (SpecF.serialize_cbor y);
  fold (cbor_nondet_match_with_size size p x x');
  Trade.intro_trade
    (cbor_nondet_match_with_size size p x x')
    (cbor_nondet_match p x x')
    emp
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
  let res = RawSerialize.cbor_size (assume SZ.fits_u64) x bound;
  fold (cbor_nondet_match_with_size v p x x');
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_serialize_inner (_: unit) : cbor_nondet_serialize_t #cbor_nondet_t cbor_nondet_match_with_size
=
  (x: _)
  (output: _)
  (#size: _)
  (#y: _)
  (#pm: _)
  (#v: _)
{
  unfold (cbor_nondet_match_with_size size pm x y);
  with w . assert (RawMatch.cbor_raw_match pm x w);
  S.pts_to_len output;
  let len = RawSerialize.cbor_size (assume SZ.fits_u64) x (S.len output);
  if (len = 0sz) {
    fold (cbor_nondet_match_with_size size pm x y);
    None #SZ.t
  } else {
    // Split output at len; serialize into prefix only.
    let out, rem = S.split output len;
    S.pts_to_len out;
    let res = RawSerialize.cbor_serialize (assume SZ.fits_u64) x out;
    S.pts_to_len out;
    with v_new . assert (S.pts_to out v_new);
    // v_new == SpecF.serialize_cbor w (from length + prefix constraint)
    Seq.lemma_eq_elim v_new (SpecF.serialize_cbor w);
    // Join back
    S.join out rem output;
    with v' . assert (pts_to output v');
    S.pts_to_len output;
    SpecF.serialize_parse_cbor w;
    SpecF.parse_cbor_prefix (SpecF.serialize_cbor w) v';
    Seq.append_slices (SpecF.serialize_cbor w) (Seq.slice v (SZ.v len) (Seq.length v));
    fold (cbor_nondet_match_with_size size pm x y);
    Some res
  }
}

(* ============ Destructors ============ *)

fn cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let res = Access.cbor_raw_get_major_type p x;
  fold (cbor_nondet_match p x v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_read_simple_value_unsafe (_: unit) : read_simple_value_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let res = ReadFields.cbor_raw_read_simple_value p x;
  fold (cbor_nondet_match p x v);
  res
}

let cbor_nondet_read_simple_value () : read_simple_value_safe_t u#0 #_ cbor_nondet_match
= read_simple_value_safe (cbor_nondet_major_type ()) (cbor_nondet_read_simple_value_unsafe ())

ghost
fn cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  Access.cbor_raw_match_cases p x;
  SpecRaw.mk_cbor_eq v';
  drop_ (RawMatch.cbor_raw_match p x v');
  drop_ (pure (Access.cbor_raw_match_cases_prop x v'))
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_read_uint64_unsafe (_: unit) : read_uint64_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let res = ReadFields.cbor_raw_read_int64_value p x;
  fold (cbor_nondet_match p x v);
  res
}

let cbor_nondet_read_uint64 () : read_uint64_safe_t u#0 #_ cbor_nondet_match
= read_uint64_safe (cbor_nondet_major_type ()) (cbor_nondet_read_uint64_unsafe ())

let cbor_nondet_read_int64 () : read_int64_safe_t u#0 #_ cbor_nondet_match
= read_int64_safe (cbor_nondet_major_type ()) (cbor_nondet_read_uint64_unsafe ())

ghost
fn cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  Access.cbor_raw_match_cases p x;
  SpecRaw.mk_cbor_eq v';
  drop_ (RawMatch.cbor_raw_match p x v');
  drop_ (pure (Access.cbor_raw_match_cases_prop x v'))
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_string_length (_: unit) : get_string_length_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let s = Access.cbor_raw_get_string p x ();
  with pm' vs . assert (S.pts_to s #pm' vs);
  S.pts_to_len s;
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let len_sz = S.len s;
  let res = SZ.sizet_to_uint64 len_sz;
  Trade.elim _ (RawMatch.cbor_raw_match p x v');
  fold (cbor_nondet_match p x v);
  res
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_string_unsafe (_: unit) : get_string_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  let s = Access.cbor_raw_get_string p x ();
  Trade.trans _ (RawMatch.cbor_raw_match p x v') (cbor_nondet_match p x v);
  s
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_tagged_tag (_: unit) : get_tagged_tag_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let res = ReadFields.cbor_raw_read_tagged_tag p x;
  fold (cbor_nondet_match p x v);
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_tagged_payload (_: unit) : get_tagged_payload_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  let res = Access.cbor_raw_get_tagged_payload p x (assume SZ.fits_u64) ();
  Trade.trans _ (RawMatch.cbor_raw_match p x v') (cbor_nondet_match p x v);
  with p' w . assert (RawMatch.cbor_raw_match p' res w);
  SpecRaw.valid_eq SpecRaw.basic_data_model v';
  cbor_nondet_match_intro res;
  Trade.trans _ _ (cbor_nondet_match p x v);
  res
}

let cbor_nondet_get_tagged () : get_tagged_safe_t #_ cbor_nondet_match
= get_tagged_safe (cbor_nondet_major_type ()) (cbor_nondet_get_tagged_tag ()) (cbor_nondet_get_tagged_payload ())

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_array_length_unsafe (_: unit) : get_array_length_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let res = ReadFields.cbor_raw_read_array_length p x;
  fold (cbor_nondet_match p x v);
  res
}

let cbor_nondet_get_array_length () : get_array_length_safe_t u#0 #_ cbor_nondet_match
= get_array_length_safe (cbor_nondet_major_type ()) (cbor_nondet_get_array_length_unsafe ())

(* ============ Array iterator ============ *)

ghost
fn cbor_raw_match_share_aux (x1: RawType.cbor_raw) (#pm0: perm) (#x2: SpecRawBase.raw_data_item)
  requires RawMatch.cbor_raw_match pm0 x1 x2
  ensures RawMatch.cbor_raw_match (pm0 /. 2.0R) x1 x2 ** RawMatch.cbor_raw_match (pm0 /. 2.0R) x1 x2
{
  RawMatch.cbor_raw_match_share x1 #pm0 #x2
}

ghost
fn cbor_raw_match_gather_aux
    (x1: RawType.cbor_raw)
    (#pm0: perm)
    (#x2: SpecRawBase.raw_data_item)
    (#pm0': perm)
    (#x2': SpecRawBase.raw_data_item)
  requires RawMatch.cbor_raw_match pm0 x1 x2 ** RawMatch.cbor_raw_match pm0' x1 x2'
  ensures RawMatch.cbor_raw_match (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
{
  RawMatch.cbor_raw_match_gather x1 #pm0 #x2 #pm0' #x2'
}

let cbor_nondet_array_iterator_match
  (pm: perm)
  (it: cbor_nondet_array_iterator_t)
  (l: list Spec.cbor)
: Tot slprop
= exists* (l': list SpecRawBase.raw_data_item).
    I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm it l' **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item l' /\
      l == List.Tot.map SpecRaw.mk_cbor l' /\
      FStar.UInt.fits (List.Tot.length l) U64.n
    )

ghost
fn cbor_nondet_array_iterator_match_elim
  (i: cbor_nondet_array_iterator_t)
  (#p: perm)
  (#l: list Spec.cbor)
requires
  cbor_nondet_array_iterator_match p i l
returns l': Ghost.erased (list SpecRawBase.raw_data_item)
ensures
  I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i l' **
  Trade.trade
    (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i l')
    (cbor_nondet_array_iterator_match p i l) **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item l' /\
    l == List.Tot.map SpecRaw.mk_cbor l' /\
    FStar.UInt.fits (List.Tot.length l) U64.n
  )
{
  unfold (cbor_nondet_array_iterator_match p i l);
  with l' . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i l');
  Trade.intro_trade
    (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i l')
    (cbor_nondet_array_iterator_match p i l)
    emp
    fn _ {
      fold (cbor_nondet_array_iterator_match p i l)
    };
  l'
}

ghost
fn cbor_nondet_array_iterator_match_intro
  (i: cbor_nondet_array_iterator_t)
  (#p: perm)
  (#v: list SpecRawBase.raw_data_item)
requires
  I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i v **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item v /\
    FStar.UInt.fits (List.Tot.length v) U64.n
  )
ensures
  cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v) **
  Trade.trade
    (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v))
    (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i v)
{
  // Share the iterator match using unfold + base/mixed share
  match i {
    IT.IBase bi -> {
      rewrite each i as (IT.IBase #RawType.cbor_raw bi);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IBase #RawType.cbor_raw bi) v);
      I.base_mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi v cbor_raw_match_share_aux;
      ();
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IBase #RawType.cbor_raw bi) v);
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IBase #RawType.cbor_raw bi) v);
      rewrite each (IT.IBase #RawType.cbor_raw bi) as i;
      fold (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v));
      Trade.intro_trade
        (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v))
        (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i v)
        (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) i v)
        fn _ {
          unfold (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v));
          rewrite each i as (IT.IBase #RawType.cbor_raw bi);
          unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IBase #RawType.cbor_raw bi) v);
          with v2 . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IBase #RawType.cbor_raw bi) v2);
          unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IBase #RawType.cbor_raw bi) v2);
          I.base_mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (p /. 2.0R) bi v _ cbor_raw_match_gather_aux;
          rewrite each (p /. 2.0R +. p /. 2.0R) as p;
          fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IBase #RawType.cbor_raw bi) v);
          rewrite each (IT.IBase #RawType.cbor_raw bi) as i
        }
    }
    IT.IPair bi ml -> {
      rewrite each i as (IT.IPair #RawType.cbor_raw bi ml);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IPair #RawType.cbor_raw bi ml) v);
      with l1 l2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi l1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p ml l2
      );
      I.base_mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi l1 cbor_raw_match_share_aux;
      I.mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p ml l2 cbor_raw_match_share_aux;
      ();
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) v);
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) v);
      rewrite each (IT.IPair #RawType.cbor_raw bi ml) as i;
      fold (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v));
      Trade.intro_trade
        (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v))
        (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p i v)
        (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) i v)
        fn _ {
          unfold (cbor_nondet_array_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor v));
          rewrite each i as (IT.IPair #RawType.cbor_raw bi ml);
          unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) v);
          with l1a l2a . assert (
            I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) bi l1a **
            I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) ml l2a
          );
          with v2 . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) v2);
          unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) v2);
          I.base_mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (p /. 2.0R) bi l1a _ cbor_raw_match_gather_aux;
          I.mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (p /. 2.0R) (p /. 2.0R) ml l2a _ cbor_raw_match_gather_aux;
          rewrite each (p /. 2.0R +. p /. 2.0R) as p;
          fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IPair #RawType.cbor_raw bi ml) v);
          rewrite each (IT.IPair #RawType.cbor_raw bi ml) as i
        }
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_array_iterator_start_unsafe (_: unit) : array_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  // mk_cbor v' is CArray, so v' is Array len lr
  let ml = Access.cbor_raw_get_array p x ();
  Trade.trans _ _ (cbor_nondet_match p x v);
  with pm' lr . assert (
    I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' ml lr
  );
  // lr == Array?.v v', so each element is valid_raw_data_item (from v' being valid)
  SpecRaw.valid_eq SpecRaw.basic_data_model v';
  let it = I.iterator_start
    RawMatch.cbor_raw_match
    SpecRawEverParse.parse_raw_data_item
    Validate.jump_raw_data_item_eta
    pm'
    ml
    (Ghost.hide lr)
    cbor_raw_match_share_aux
    cbor_raw_match_gather_aux;
  Trade.trans _ _ (cbor_nondet_match p x v);
  // Now we have I.iterator_match cbor_raw_match parse_raw_data_item pm'' it lr
  with pm'' . assert (
    I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm'' it lr
  );
  ();
  cbor_nondet_array_iterator_match_intro it;
  Trade.trans _ _ (cbor_nondet_match p x v);
  // result is at perm pm''/2 with list = List.Tot.map mk_cbor lr
  // but we need it to relate to v (the original CArray)
  // Spec.unpack v == CArray (List.Tot.map mk_cbor lr) (since v == mk_cbor v')
  rewrite each (List.Tot.map SpecRaw.mk_cbor lr) as (Spec.CArray?.v (Spec.unpack v));
  it
}

let cbor_nondet_array_iterator_start () : array_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
= array_iterator_start_safe (cbor_nondet_major_type ()) (cbor_nondet_array_iterator_start_unsafe ())

fn cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let lr = cbor_nondet_array_iterator_match_elim x;
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #RawType.cbor_raw bi);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IBase #RawType.cbor_raw bi) lr);
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi lr;
      let len_before = IT.base_mixed_list_length bi;
      let r = (len_before = 0sz);
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IBase #RawType.cbor_raw bi) lr);
      rewrite each (IT.IBase #RawType.cbor_raw bi) as x;
      Trade.elim _ (cbor_nondet_array_iterator_match p x v);
      r
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #RawType.cbor_raw bi ml);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IPair #RawType.cbor_raw bi ml) lr);
      with l1 l2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi l1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p ml l2
      );
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi l1;
      I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p ml l2;
      let len_before = IT.base_mixed_list_length bi;
      let r = (len_before = 0sz);
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IPair #RawType.cbor_raw bi ml) lr);
      rewrite each (IT.IPair #RawType.cbor_raw bi ml) as x;
      Trade.elim _ (cbor_nondet_array_iterator_match p x v);
      r
    }
  }
}

#push-options "--z3rlimit 64"
fn cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let lr = cbor_nondet_array_iterator_match_elim x;
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #RawType.cbor_raw bi);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IBase #RawType.cbor_raw bi) lr);
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi lr;
      let len_before = IT.base_mixed_list_length bi;
      let res = SZ.sizet_to_uint64 len_before;
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IBase #RawType.cbor_raw bi) lr);
      rewrite each (IT.IBase #RawType.cbor_raw bi) as x;
      Trade.elim _ (cbor_nondet_array_iterator_match p x v);
      res
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #RawType.cbor_raw bi ml);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IPair #RawType.cbor_raw bi ml) lr);
      with l1 l2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi l1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p ml l2
      );
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p bi l1;
      I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p ml l2;
      let len_before = IT.base_mixed_list_length bi;
      let len_after = IT.mixed_list_length ml;
      List.Tot.append_length l1 l2;
      ();
      SZ.fits_u64_implies_fits (SZ.v len_before + SZ.v len_after);
      let len_total = SZ.add len_before len_after;
      let res = SZ.sizet_to_uint64 len_total;
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item p (IT.IPair #RawType.cbor_raw bi ml) lr);
      rewrite each (IT.IPair #RawType.cbor_raw bi ml) as x;
      Trade.elim _ (cbor_nondet_array_iterator_match p x v);
      res
    }
  }
}
#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_array_iterator_next_unsafe (_: unit) : array_iterator_next_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
= (x: _)
  (#y: _)
  (#py: _)
  (#z: _)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let lr = cbor_nondet_array_iterator_match_elim y;
  // lr == Cons (hd :: tl) since z is non-empty
  ();
  assert (pure (Cons? lr));
  let i_cur = !x;
  let res, it' = ReadMapEntry.iterator_next_raw_data_item f64 py i_cur lr;
  x := it';
  with pm_v hd_val tl_l pm' . assert (
    RawMatch.cbor_raw_match pm_v res hd_val **
    R.pts_to x it' **
    I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l **
    Trade.trade
      (RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
      (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (Ghost.reveal y) (Ghost.reveal lr))
  );
  // lr == hd :: tl_l (from iterator_next_post)
  // from cbor_nondet_array_iterator_match: List.Tot.for_all valid_raw_data_item lr
  // So hd_val is valid, and all of tl_l is valid
  ();
  // Build the trade chain:
  // First: compose iterator_next's trade with elim's trade
  Trade.trans
    (RawMatch.cbor_raw_match pm_v res hd_val ** I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
    (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (Ghost.reveal y) (Ghost.reveal lr))
    (cbor_nondet_array_iterator_match py y z);
  // Now intro for tail: need to convert iterator_match to cbor_nondet_array_iterator_match
  cbor_nondet_array_iterator_match_intro it';
  Trade.trans_hyp_r
    (RawMatch.cbor_raw_match pm_v res hd_val)
    (cbor_nondet_array_iterator_match (pm' /. 2.0R) it' (List.Tot.map SpecRaw.mk_cbor tl_l))
    (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item pm' it' tl_l)
    (cbor_nondet_array_iterator_match py y z);
  // Rewrite tail to match the spec form List.Tot.tl z
  Trade.rewrite_with_trade
    (cbor_nondet_array_iterator_match (pm' /. 2.0R) it' (List.Tot.map SpecRaw.mk_cbor tl_l))
    (cbor_nondet_array_iterator_match (pm' /. 2.0R) it' (List.Tot.tl z));
  Trade.trans_hyp_r _ _ _ (cbor_nondet_array_iterator_match py y z);
  // Now intro for head: convert RawMatch.cbor_raw_match to cbor_nondet_match
  cbor_nondet_match_intro res;
  Trade.trans_hyp_l
    (cbor_nondet_match (pm_v /. 2.0R) res (SpecRaw.mk_cbor hd_val))
    (RawMatch.cbor_raw_match pm_v res hd_val)
    (cbor_nondet_array_iterator_match (pm' /. 2.0R) it' (List.Tot.tl z))
    (cbor_nondet_array_iterator_match py y z);
  // Rewrite head value to List.Tot.hd z
  Trade.rewrite_with_trade
    (cbor_nondet_match (pm_v /. 2.0R) res (SpecRaw.mk_cbor hd_val))
    (cbor_nondet_match (pm_v /. 2.0R) res (List.Tot.hd z));
  Trade.trans_hyp_l _ _ _ (cbor_nondet_array_iterator_match py y z);
  res
}

#pop-options

let cbor_nondet_array_iterator_next () : array_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match
= array_iterator_next_safe (cbor_nondet_array_iterator_is_empty ()) (cbor_nondet_array_iterator_next_unsafe ())

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --ext no:context_pruning"

fn cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match
= (x: _)
  (len: _)
  (#py: _)
  (#z: _)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let lr = cbor_nondet_array_iterator_match_elim x;
  let n : Ghost.erased nat = Ghost.hide (U64.v len);
  let len_sz = SZ.uint64_to_sizet len;
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #RawType.cbor_raw bi);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IBase #RawType.cbor_raw bi) lr);
      // IBase arm: lr = l1, no l2
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi lr;
      let cb_sz = IT.base_mixed_list_length bi;
      let len_before_sz = (if SZ.lte len_sz cb_sz then len_sz else cb_sz);
      // Narrow the base list
      rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi lr)
           as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi lr);
      let bi' = I.base_mixed_list_narrow_n
        RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item
        Validate.jump_raw_data_item_eta 0 (SZ.v cb_sz) py bi lr
        0sz len_before_sz;
      // Share to get two copies at py/2
      let l1_narrow : Ghost.erased (list SpecRawBase.raw_data_item) = LowParse.PulseParse.Iterator.list_narrow lr 0 (SZ.v len_before_sz);
      rewrite each (LowParse.PulseParse.Iterator.list_narrow lr 0 (SZ.v len_before_sz)) as (Ghost.reveal l1_narrow);
      rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow))
           as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi' (Ghost.reveal l1_narrow));
      I.base_mixed_list_match_n_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi'
        (Ghost.reveal l1_narrow) cbor_raw_match_share_aux;
      // Build result iterator as IBase bi'
      let it' : LowParse.PulseParse.Iterator.Type.iterator RawType.cbor_raw = IT.IBase bi';
      // Prove l1_narrow == list_narrow lr 0 n
      LowParse.PulseParse.Iterator.list_narrow_append lr [] 0 (Ghost.reveal n);
      List.Tot.append_l_nil lr;
      CBOR.Spec.Util.list_map_splitAt SpecRaw.mk_cbor lr (Ghost.reveal n);
      CBOR.Spec.Util.list_for_all_splitAt SpecRaw.valid_raw_data_item lr (Ghost.reveal n);
      assert (pure (
        LowParse.PulseParse.Iterator.list_narrow (Ghost.reveal lr) 0 (Ghost.reveal n) ==
        fst (List.Tot.splitAt (Ghost.reveal n) (Ghost.reveal lr))));
      rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (Ghost.reveal l1_narrow))
           as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) bi' (Ghost.reveal l1_narrow));
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) (IT.IBase #RawType.cbor_raw bi') (Ghost.reveal l1_narrow));
      rewrite each (IT.IBase #RawType.cbor_raw bi') as it';
      fold (cbor_nondet_array_iterator_match (py /. 2.0R) it' (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal l1_narrow)));
      Trade.intro_trade
        (cbor_nondet_array_iterator_match (py /. 2.0R) it' (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal l1_narrow)))
        (cbor_nondet_array_iterator_match py (IT.IBase #RawType.cbor_raw bi) z)
        (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (Ghost.reveal l1_narrow) **
         Trade.trade
           (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow))
           (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi lr) **
         Trade.trade
           (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IBase #RawType.cbor_raw bi) lr)
           (cbor_nondet_array_iterator_match py (IT.IBase #RawType.cbor_raw bi) z))
        fn _ {
          unfold (cbor_nondet_array_iterator_match (py /. 2.0R) it' (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal l1_narrow)));
          with v' . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) it' v');
          rewrite each it' as (IT.IBase #RawType.cbor_raw bi');
          unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) (IT.IBase #RawType.cbor_raw bi') v');
          // it' = IBase bi', so v' = xl1 directly
          rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) bi' v')
               as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' v');
          I.base_mixed_list_match_n_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) (py /. 2.0R) bi' v' (Ghost.reveal l1_narrow) cbor_raw_match_gather_aux;
          rewrite each v' as (Ghost.reveal l1_narrow);
          rewrite each (py /. 2.0R +. py /. 2.0R) as py;
          rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi' (Ghost.reveal l1_narrow))
               as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow));
          Trade.elim _ (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi lr);
          rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi lr)
               as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi lr);
          fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IBase #RawType.cbor_raw bi) lr);
          Trade.elim _ (cbor_nondet_array_iterator_match py (IT.IBase #RawType.cbor_raw bi) z)
        };
      rewrite each (IT.IBase #RawType.cbor_raw bi) as x;
      rewrite each (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal l1_narrow)) as (fst (List.Tot.splitAt (U64.v len) z));
      it'
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #RawType.cbor_raw bi ml);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IPair #RawType.cbor_raw bi ml) lr);
      with l1 l2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py ml l2
      );
      I.base_mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l1;
      I.mixed_list_match_length RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py ml l2;
      let cb_sz = IT.base_mixed_list_length bi;
      let len_before_sz = (if SZ.lte len_sz cb_sz then len_sz else cb_sz);
      let len_after_sz = (if SZ.lte len_sz cb_sz then 0sz else SZ.sub len_sz cb_sz);
      rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l1)
           as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi l1);
      let bi' = I.base_mixed_list_narrow_n
        RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item
        Validate.jump_raw_data_item_eta 0 (SZ.v cb_sz) py bi l1
        0sz len_before_sz;
      let ca_sz = IT.mixed_list_length ml;
      List.Tot.append_length l1 l2;
      assert (pure (SZ.v len_after_sz <= SZ.v ca_sz));
      rewrite (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py ml l2)
           as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py ml l2);
      let after' = I.mixed_list_narrow_n
        RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item
        Validate.jump_raw_data_item_eta 0 (SZ.v ca_sz) py ml l2
        0sz len_after_sz
        cbor_raw_match_share_aux cbor_raw_match_gather_aux;
      // narrow_after returns mixed_list_match at (py/2). Share once more to get 2x (py/4):
      let l2_narrow_raw : Ghost.erased (list SpecRawBase.raw_data_item) = LowParse.PulseParse.Iterator.list_narrow l2 0 (SZ.v len_after_sz);
      rewrite each (LowParse.PulseParse.Iterator.list_narrow l2 0 (SZ.v len_after_sz)) as (Ghost.reveal l2_narrow_raw);
      I.mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) after' (Ghost.reveal l2_narrow_raw) cbor_raw_match_share_aux;
      rewrite each ((py /. 2.0R) /. 2.0R) as (py /. 4.0R);
      // narrow_before returns base_mixed_list_match at py. Share to (py/2), then share once more to (py/4):
      rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)))
           as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi' (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)));
      I.base_mixed_list_match_n_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi'
        (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)) cbor_raw_match_share_aux;
      // We now have 2x base_mixed_list_match_n at (py/2). Share one of them again to (py/4):
      I.base_mixed_list_match_n_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi'
        (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)) cbor_raw_match_share_aux;
      rewrite each ((py /. 2.0R) /. 2.0R) as (py /. 4.0R);
      let l1_narrow : Ghost.erased (list SpecRawBase.raw_data_item) = LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz);
      let l2_narrow : Ghost.erased (list SpecRawBase.raw_data_item) = Ghost.hide (Ghost.reveal l2_narrow_raw);
      rewrite each (LowParse.PulseParse.Iterator.list_narrow l1 0 (SZ.v len_before_sz)) as (Ghost.reveal l1_narrow);
      rewrite each (Ghost.reveal l2_narrow_raw) as (Ghost.reveal l2_narrow);
      // Use one (py/4) base_mixed and one (py/4) mixed for the wrapper.
      rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 4.0R) bi' (Ghost.reveal l1_narrow))
           as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) bi' (Ghost.reveal l1_narrow));
      let it' : LowParse.PulseParse.Iterator.Type.iterator RawType.cbor_raw = IT.IPair bi' after';
      List.Tot.append_length l1 l2;
      LowParse.PulseParse.Iterator.list_narrow_append l1 l2 0 (Ghost.reveal n);
      let lr_narrow : Ghost.erased (list SpecRawBase.raw_data_item) = Ghost.hide (List.Tot.append (Ghost.reveal l1_narrow) (Ghost.reveal l2_narrow));
      assert (pure (
        LowParse.PulseParse.Iterator.list_narrow (Ghost.reveal lr) 0 (Ghost.reveal n) ==
        Ghost.reveal lr_narrow));
      CBOR.Spec.Util.list_map_splitAt SpecRaw.mk_cbor lr (Ghost.reveal n);
      CBOR.Spec.Util.list_for_all_splitAt SpecRaw.valid_raw_data_item lr (Ghost.reveal n);
      assert (pure (
        LowParse.PulseParse.Iterator.list_narrow (Ghost.reveal lr) 0 (Ghost.reveal n) ==
        fst (List.Tot.splitAt (Ghost.reveal n) (Ghost.reveal lr))));
      // Before fold, assert we have the right slprops:
      assert (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) bi' (Ghost.reveal l1_narrow));
      assert (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) after' (Ghost.reveal l2_narrow));
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) (IT.IPair #RawType.cbor_raw bi' after') (Ghost.reveal lr_narrow));
      rewrite each (IT.IPair #RawType.cbor_raw bi' after') as it';
      fold (cbor_nondet_array_iterator_match (py /. 4.0R) it' (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal lr_narrow)));
      // Before Trade.intro_trade, assert the resources are available:
      assert (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 4.0R) bi' (Ghost.reveal l1_narrow));
      assert (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (Ghost.reveal l1_narrow));
      assert (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) after' (Ghost.reveal l2_narrow));
      Trade.intro_trade
        (cbor_nondet_array_iterator_match (py /. 4.0R) it' (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal lr_narrow)))
        (cbor_nondet_array_iterator_match py (IT.IPair #RawType.cbor_raw bi ml) z)
        (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 4.0R) bi' (Ghost.reveal l1_narrow) **
         I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) bi' (Ghost.reveal l1_narrow) **
         I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) after' (Ghost.reveal l2_narrow) **
         Trade.trade
           (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow))
           (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi l1) **
         Trade.trade
           (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) after' (Ghost.reveal l2_narrow))
           (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py ml l2) **
         Trade.trade
           (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IPair #RawType.cbor_raw bi ml) lr)
           (cbor_nondet_array_iterator_match py (IT.IPair #RawType.cbor_raw bi ml) z))
        fn _ {
          unfold (cbor_nondet_array_iterator_match (py /. 4.0R) it' (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal lr_narrow)));
          with v' . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) it' v');
          // it' = IPair bi' after', rewrite before unfold
          rewrite (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) it' v')
               as (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) (IT.IPair #RawType.cbor_raw bi' after') v');
          unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) (IT.IPair #RawType.cbor_raw bi' after') v');
          // The unfold produces exists* l1 l2 with base_mixed_list_match bi' l1 ** mixed_list_match after' l2 ** pure(v' == l1 @ l2)
          // 
          // After unfold, the context has slprops with FRESH existential variables (l1, l2 from the exists*),
          // PLUS the resources which use (l1_narrow, l2_narrow).
          // 
          // We have:
          //   - base_mixed_list_match (py/4) bi' l1_from_exists (from unfold)
          //   - mixed_list_match (py/4) after' l2_from_exists (from unfold) 
          //   - pure(v' == l1_from_exists @ l2_from_exists)
          // Plus resources:
          //   - base_mixed_list_match_n (py/4) bi' l1_narrow
          //   - base_mixed_list_match_n (py/2) bi' l1_narrow  
          //   - mixed_list_match (py/4) after' l2_narrow
          //
          // Use gather to prove l1_from_exists == l1_narrow by gathering the base_mixed slprops.
          // The gather function takes two slprops and proves their lists are equal.
          // After gathering, we have base_mixed_list_match_n (py/2) bi' l1_narrow with l1_from_exists == l1_narrow.
          
          // First, grab the ONE base_mixed_list_match from the unfold. It has a fresh list variable.
          with l1' l2' . _;
          // Now we have l1' (from unfold) and l2' (from unfold) named.
          // We also have l1_narrow and l2_narrow from resources.
          // Since the exists* gives us the pure(v' == l1' @ l2'), and we know v' == lr_narrow,
          // and lr_narrow == l1_narrow @ l2_narrow, we should have l1' == l1_narrow and l2' == l2_narrow.
          // Use gather to prove l1' == l1_narrow:
          rewrite (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) bi' l1')
               as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 4.0R) bi' l1');
          I.base_mixed_list_match_n_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 4.0R) (py /. 4.0R) bi' l1' (Ghost.reveal l1_narrow) cbor_raw_match_gather_aux;
          rewrite each l1' as (Ghost.reveal l1_narrow);
          // Gather l2' == l2_narrow using mixed_list_match_gather:
          I.mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 4.0R) (py /. 4.0R) after' l2' (Ghost.reveal l2_narrow) cbor_raw_match_gather_aux;
          rewrite each l2' as (Ghost.reveal l2_narrow);
          rewrite each (py /. 4.0R +. py /. 4.0R) as (py /. 2.0R);
          // Gather the two base_mixed_n at (py/2) to py:
          I.base_mixed_list_match_n_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) (py /. 2.0R) (py /. 2.0R) bi' (Ghost.reveal l1_narrow) (Ghost.reveal l1_narrow) cbor_raw_match_gather_aux;
          rewrite each (py /. 2.0R +. py /. 2.0R) as py;
          rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v len_before_sz) py bi' (Ghost.reveal l1_narrow))
               as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi' (Ghost.reveal l1_narrow));
          // Apply narrow trades:
          Trade.elim _ (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi l1);
          Trade.elim _ (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py ml l2);
          rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v cb_sz) py bi l1)
               as (I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l1);
          rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v ca_sz) py ml l2)
               as (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py ml l2);
          fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IPair #RawType.cbor_raw bi ml) lr);
          Trade.elim _ (cbor_nondet_array_iterator_match py (IT.IPair #RawType.cbor_raw bi ml) z)
        };
      rewrite each (IT.IPair #RawType.cbor_raw bi ml) as x;
      rewrite each (List.Tot.map SpecRaw.mk_cbor (Ghost.reveal lr_narrow)) as (fst (List.Tot.splitAt (U64.v len) z));
      it'
    }
  }
}

#pop-options

ghost
fn cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match
= (x: _)
  (#py: _)
  (#z: _)
{
  unfold (cbor_nondet_array_iterator_match py x z);
  with l' . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py x l');
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #RawType.cbor_raw bi);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IBase #RawType.cbor_raw bi) l');
      I.base_mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l' cbor_raw_match_share_aux;
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) (IT.IBase #RawType.cbor_raw bi) l');
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) (IT.IBase #RawType.cbor_raw bi) l');
      rewrite each (IT.IBase #RawType.cbor_raw bi) as x;
      fold (cbor_nondet_array_iterator_match (py /. 2.0R) x z);
      fold (cbor_nondet_array_iterator_match (py /. 2.0R) x z)
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #RawType.cbor_raw bi ml);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py (IT.IPair #RawType.cbor_raw bi ml) l');
      with l1 l2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py ml l2
      );
      I.base_mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py bi l1 cbor_raw_match_share_aux;
      I.mixed_list_match_share RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py ml l2 cbor_raw_match_share_aux;
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) l');
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py /. 2.0R) (IT.IPair #RawType.cbor_raw bi ml) l');
      rewrite each (IT.IPair #RawType.cbor_raw bi ml) as x;
      fold (cbor_nondet_array_iterator_match (py /. 2.0R) x z);
      fold (cbor_nondet_array_iterator_match (py /. 2.0R) x z)
    }
  }
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
  with l1 . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 x l1);
  with l2 . assert (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py2 x l2);
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #RawType.cbor_raw bi);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 (IT.IBase #RawType.cbor_raw bi) l1);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py2 (IT.IBase #RawType.cbor_raw bi) l2);
      I.base_mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 py2 bi l1 l2 cbor_raw_match_gather_aux;
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py1 +. py2) (IT.IBase #RawType.cbor_raw bi) l1);
      rewrite each (IT.IBase #RawType.cbor_raw bi) as x;
      fold (cbor_nondet_array_iterator_match (py1 +. py2) x z1)
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #RawType.cbor_raw bi ml);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 (IT.IPair #RawType.cbor_raw bi ml) l1);
      unfold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py2 (IT.IPair #RawType.cbor_raw bi ml) l2);
      with la1 la2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 bi la1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 ml la2
      );
      with lb1 lb2 . assert (
        I.base_mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py2 bi lb1 **
        I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py2 ml lb2
      );
      I.base_mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 py2 bi la1 lb1 cbor_raw_match_gather_aux;
      I.mixed_list_match_gather RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item py1 py2 ml la2 lb2 cbor_raw_match_gather_aux;
      List.Tot.append_injective la1 lb1 la2 lb2;
      fold (I.iterator_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item (py1 +. py2) (IT.IPair #RawType.cbor_raw bi ml) l1);
      rewrite each (IT.IPair #RawType.cbor_raw bi ml) as x;
      fold (cbor_nondet_array_iterator_match (py1 +. py2) x z1)
    }
  }
}

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_array_item_unsafe (_: unit) : get_array_item_t u#0 #_ cbor_nondet_match
= (x: _)
  (i: _)
  (#p: _)
  (#y: _)
{
  let orig_list : Ghost.erased (list Spec.cbor) = Ghost.hide (Spec.CArray?.v (Spec.unpack y));
  let it = cbor_nondet_array_iterator_start_unsafe () x;
  with p_it l_it . assert (cbor_nondet_array_iterator_match p_it it l_it);
  let mut pit = it;
  let mut pj = 0uL;
  let cont0 = U64.lt 0uL i;
  let mut pcont = cont0;
  while (
    !pcont
  )
  invariant exists* j_val cont iter suffix piter .
    R.pts_to pj j_val **
    R.pts_to pcont cont **
    R.pts_to pit iter **
    cbor_nondet_array_iterator_match piter iter suffix **
    Trade.trade (cbor_nondet_array_iterator_match piter iter suffix) (cbor_nondet_match p x y) **
    pure (
      U64.v j_val <= U64.v i /\
      List.Tot.length suffix + U64.v j_val == List.Tot.length (Ghost.reveal orig_list) /\
      U64.v i - U64.v j_val < List.Tot.length suffix /\
      List.Tot.index suffix (U64.v i - U64.v j_val) == List.Tot.index (Ghost.reveal orig_list) (U64.v i) /\
      cont == (U64.v j_val < U64.v i)
    )
  {
    with gj gcont gi gsuffix gpiter .
      assert (
        R.pts_to pj gj **
        R.pts_to pcont gcont **
        R.pts_to pit gi **
        cbor_nondet_array_iterator_match gpiter gi gsuffix **
        Trade.trade (cbor_nondet_array_iterator_match gpiter gi gsuffix) (cbor_nondet_match p x y)
      );
    let elem = cbor_nondet_array_iterator_next_unsafe () pit;
    with p_elem p_iter' v_elem iter' z_tl .
      assert (
        cbor_nondet_match p_elem elem v_elem **
        R.pts_to pit iter' **
        cbor_nondet_array_iterator_match p_iter' iter' z_tl **
        Trade.trade
          (cbor_nondet_match p_elem elem v_elem ** cbor_nondet_array_iterator_match p_iter' iter' z_tl)
          (cbor_nondet_array_iterator_match gpiter gi gsuffix) **
        pure (Ghost.reveal gsuffix == v_elem :: z_tl)
      );
    Trade.elim_hyp_l
      (cbor_nondet_match p_elem elem v_elem)
      (cbor_nondet_array_iterator_match p_iter' iter' z_tl)
      (cbor_nondet_array_iterator_match gpiter gi gsuffix);
    Trade.trans
      (cbor_nondet_array_iterator_match p_iter' iter' z_tl)
      (cbor_nondet_array_iterator_match gpiter gi gsuffix)
      (cbor_nondet_match p x y);
    let j_val = !pj;
    pj := U64.add j_val 1uL;
    let new_cont = U64.lt (U64.add j_val 1uL) i;
    pcont := new_cont;
    ()
  };
  // Now j_val == i, suffix starts at element i
  let res = cbor_nondet_array_iterator_next_unsafe () pit;
  with p_res p_iter_final v_res iter_final z_final .
    assert (
      cbor_nondet_match p_res res v_res **
      R.pts_to pit iter_final **
      cbor_nondet_array_iterator_match p_iter_final iter_final z_final **
      Trade.trade
        (cbor_nondet_match p_res res v_res ** cbor_nondet_array_iterator_match p_iter_final iter_final z_final)
        _
    );
  Trade.elim_hyp_r
    (cbor_nondet_match p_res res v_res)
    (cbor_nondet_array_iterator_match p_iter_final iter_final z_final)
    _;
  Trade.trans
    (cbor_nondet_match p_res res v_res)
    _
    (cbor_nondet_match p x y);
  res
}

#pop-options

let cbor_nondet_get_array_item () : get_array_item_safe_t #_ cbor_nondet_match
= get_array_item_safe (cbor_nondet_major_type ()) (cbor_nondet_get_array_length_unsafe ()) (cbor_nondet_get_array_item_unsafe ())

(* ============ Map length (after array section per fsti ordering) ============ *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_get_map_length_unsafe (_: unit) : get_map_length_t u#0 #_ cbor_nondet_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_match p x v);
  with v' . assert (RawMatch.cbor_raw_match p x v');
  SpecRaw.mk_cbor_eq v';
  let res = ReadFields.cbor_raw_read_map_length p x;
  fold (cbor_nondet_match p x v);
  res
}

let cbor_nondet_get_map_length () : get_map_length_safe_t u#0 #_ cbor_nondet_match
= get_map_length_safe (cbor_nondet_major_type ()) (cbor_nondet_get_map_length_unsafe ())

(* ============ Map iterator section ============ *)

let cbor_nondet_map_iterator_match
  (pm: perm)
  (it: cbor_nondet_map_iterator_t)
  (l: list (Spec.cbor & Spec.cbor))
: Tot slprop
= exists* (lr: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)).
    I.iterator_match
      (fun (pm0: perm) (e: RawType.cbor_map_entry RawType.cbor_raw)
           (v: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
         RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm it lr **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst lr) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd lr) /\
      l == List.Tot.map SpecRaw.mk_cbor_map_entry lr /\
      FStar.UInt.fits (List.Tot.length l) U64.n
    )

ghost
fn cbor_map_entry_match_share_aux
  (e: RawType.cbor_map_entry RawType.cbor_raw)
  (#pm0: perm)
  (#x2: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
  requires RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e x2
  ensures RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (pm0 /. 2.0R) e x2 **
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (pm0 /. 2.0R) e x2
{
  RawMatch.cbor_map_entry_match_share RawMatch.cbor_raw_match cbor_raw_match_share_aux e #pm0 #x2
}

ghost
fn cbor_map_entry_match_gather_aux
    (e: RawType.cbor_map_entry RawType.cbor_raw)
    (#pm0: perm)
    (#x2: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
    (#pm0': perm)
    (#x2': (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
  requires RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e x2 **
           RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0' e x2'
  ensures RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (pm0 +. pm0') e x2 **
          pure (x2 == x2')
{
  ghost fn cbor_raw_match_gather_explicit
      (x1: RawType.cbor_raw)
      (#pm00: perm)
      (#xa: SpecRawBase.raw_data_item)
      (#pm00': perm)
      (xb: SpecRawBase.raw_data_item { xb << x2' })
    requires RawMatch.cbor_raw_match pm00 x1 xa ** RawMatch.cbor_raw_match pm00' x1 xb
    ensures RawMatch.cbor_raw_match (pm00 +. pm00') x1 xa ** pure (xa == xb)
  {
    cbor_raw_match_gather_aux x1 #pm00 #xa #pm00' #xb
  };
  RawMatch.cbor_map_entry_match_gather RawMatch.cbor_raw_match e #pm0 #x2 #pm0' #x2'
    cbor_raw_match_gather_explicit
}

ghost
fn cbor_nondet_map_iterator_match_elim
  (i: cbor_nondet_map_iterator_t)
  (#p: perm)
  (#l: list (Spec.cbor & Spec.cbor))
requires
  cbor_nondet_map_iterator_match p i l
returns lr: Ghost.erased (list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
ensures
  I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    p i lr **
  Trade.trade
    (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p i lr)
    (cbor_nondet_map_iterator_match p i l) **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst lr) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd lr) /\
    l == List.Tot.map SpecRaw.mk_cbor_map_entry lr /\
    FStar.UInt.fits (List.Tot.length l) U64.n
  )
{
  unfold (cbor_nondet_map_iterator_match p i l);
  with lr . assert (I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    p i lr);
  Trade.intro_trade
    (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p i lr)
    (cbor_nondet_map_iterator_match p i l)
    emp
    fn _ {
      fold (cbor_nondet_map_iterator_match p i l)
    };
  lr
}

ghost
fn cbor_nondet_map_iterator_match_intro
  (i: cbor_nondet_map_iterator_t)
  (#p: perm)
  (#v: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
requires
  I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    p i v **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v) /\
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v) /\
    FStar.UInt.fits (List.Tot.length v) U64.n
  )
ensures
  cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v) **
  Trade.trade
    (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v))
    (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      p i v)
{
  match i {
    IT.IBase bi -> {
      rewrite each i as (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v);
      I.base_mixed_list_match_share
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p bi v cbor_map_entry_match_share_aux;
      ();
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (p /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v);
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (p /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v);
      rewrite each (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) as i;
      fold (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v));
      Trade.intro_trade
        (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v))
        (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          p i v)
        (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          (p /. 2.0R) i v)
        fn _ {
          unfold (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v));
          rewrite each i as (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi);
          unfold (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v);
          with v2 . assert (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v2);
          unfold (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v2);
          I.base_mixed_list_match_gather
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (p /. 2.0R) bi v _ cbor_map_entry_match_gather_aux;
          rewrite each (p /. 2.0R +. p /. 2.0R) as p;
          fold (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            p (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) v);
          rewrite each (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) as i
        }
    }
    IT.IPair bi ml -> {
      rewrite each i as (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v);
      with l1 l2 . assert (
        I.base_mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          p bi l1 **
        I.mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          p ml l2);
      I.base_mixed_list_match_share
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p bi l1 cbor_map_entry_match_share_aux;
      I.mixed_list_match_share
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p ml l2 cbor_map_entry_match_share_aux;
      ();
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (p /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v);
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (p /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v);
      rewrite each (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) as i;
      fold (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v));
      Trade.intro_trade
        (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v))
        (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          p i v)
        (I.iterator_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          (p /. 2.0R) i v)
        fn _ {
          unfold (cbor_nondet_map_iterator_match (p /. 2.0R) i (List.Tot.map SpecRaw.mk_cbor_map_entry v));
          rewrite each i as (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml);
          unfold (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v);
          with l1a l2a . assert (
            I.base_mixed_list_match
              (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
              (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
              (p /. 2.0R) bi l1a **
            I.mixed_list_match
              (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
              (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
              (p /. 2.0R) ml l2a);
          with v2 . assert (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v2);
          unfold (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v2);
          I.base_mixed_list_match_gather
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (p /. 2.0R) bi l1a _ cbor_map_entry_match_gather_aux;
          I.mixed_list_match_gather
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            (p /. 2.0R) (p /. 2.0R) ml l2a _ cbor_map_entry_match_gather_aux;
          rewrite each (p /. 2.0R +. p /. 2.0R) as p;
          fold (I.iterator_match
            (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            p (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) v);
          rewrite each (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) as i
        }
    }
  }
}


#push-options "--z3rlimit 128 --fuel 2 --ifuel 2 --ext no:context_pruning"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_map_iterator_start_unsafe (_: unit) : map_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match
= (x: _)
  (#p: _)
  (#y: _)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let v' = cbor_nondet_match_elim x;
  SpecRaw.mk_cbor_eq v';
  SpecRaw.valid_eq SpecRaw.basic_data_model v';
  // mk_cbor v' is CMap, so v' is Map len lr
  let ml = Access.cbor_raw_get_map p x ();
  Trade.trans _ _ (cbor_nondet_match p x y);
  with pm' lr . assert (
    I.mixed_list_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' ml lr
  );
  let it = I.iterator_start
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    Validate.jump_nondep_then_raw_data_item_eta
    pm' ml lr
    cbor_map_entry_match_share_aux
    cbor_map_entry_match_gather_aux;
  Trade.trans _ _ (cbor_nondet_match p x y);
  cbor_nondet_map_iterator_match_intro it;
  Trade.trans _ _ (cbor_nondet_match p x y);
  let m : Ghost.erased Spec.cbor_map = Spec.CMap?.c (Spec.unpack y);
  let lspec : Ghost.erased (list (Spec.cbor & Spec.cbor)) = List.Tot.map SpecRaw.mk_cbor_map_entry lr;
  Classical.forall_intro (SpecRaw.list_assoc_map_mk_cbor_map_entry m lr ());
  SpecRaw.list_no_repeats_map_fst_mk_cbor_map_entry lr;
  // length proof: lspec == map mk_cbor_map_entry lr, so length lspec == length lr.
  // From mk_cbor_eq on y' (the raw Map), cbor_map_length m == length lr.
  it
}

#pop-options

let cbor_nondet_map_iterator_start () : map_iterator_start_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match
= map_iterator_start_safe (cbor_nondet_major_type ()) (cbor_nondet_map_iterator_start_unsafe ())

fn cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match
= (x: _)
  (#p: _)
  (#v: _)
{
  let lr = cbor_nondet_map_iterator_match_elim x;
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr);
      I.base_mixed_list_match_length
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p bi lr;
      let len_before = IT.base_mixed_list_length bi;
      let res = (len_before = 0sz);
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr);
      rewrite each (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) as x;
      Trade.elim _ _;
      res
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr);
      with l1 l2 . assert (
        I.base_mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          p bi l1 **
        I.mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          p ml l2);
      I.base_mixed_list_match_length
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p bi l1;
      I.mixed_list_match_length
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p ml l2;
      let len_before = IT.base_mixed_list_length bi;
      List.Tot.append_length l1 l2;
      let res = (len_before = 0sz);
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        p (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr);
      rewrite each (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) as x;
      Trade.elim _ _;
      res
    }
  }
}


(* ============ Map entry match ============ *)

let cbor_nondet_map_entry_match
  (pm: perm)
  (entry: cbor_nondet_map_entry_t)
  (pair: Spec.cbor & Spec.cbor)
: Tot slprop
= cbor_nondet_match pm entry.RawType.cbor_map_entry_key (fst pair) **
  cbor_nondet_match pm entry.RawType.cbor_map_entry_value (snd pair)

ghost
fn cbor_nondet_map_entry_match_intro
  (entry: cbor_nondet_map_entry_t)
  (#p: perm)
  (#a: SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)
requires
  RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p entry a **
  pure (
    SpecRaw.valid_raw_data_item (fst a) /\
    SpecRaw.valid_raw_data_item (snd a)
  )
ensures
  cbor_nondet_map_entry_match (p /. 2.0R) entry (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)) **
  Trade.trade
    (cbor_nondet_map_entry_match (p /. 2.0R) entry (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)))
    (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p entry a)
{
  unfold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p entry a);
  unfold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
    (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
    entry a);
  unfold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
    entry (snd a));
  rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get entry) (fst a))
       as (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_key (fst a));
  rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get entry) (snd a))
       as (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_value (snd a));
  cbor_nondet_match_intro entry.RawType.cbor_map_entry_key;
  cbor_nondet_match_intro entry.RawType.cbor_map_entry_value;
  fold (cbor_nondet_map_entry_match (p /. 2.0R) entry (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)));
  Trade.intro_trade
    (cbor_nondet_map_entry_match (p /. 2.0R) entry (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)))
    (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p entry a)
    (Trade.trade
       (cbor_nondet_match (p /. 2.0R) entry.RawType.cbor_map_entry_key (SpecRaw.mk_cbor (fst a)))
       (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_key (fst a)) **
     Trade.trade
       (cbor_nondet_match (p /. 2.0R) entry.RawType.cbor_map_entry_value (SpecRaw.mk_cbor (snd a)))
       (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_value (snd a)))
    fn _ {
      unfold (cbor_nondet_map_entry_match (p /. 2.0R) entry (SpecRaw.mk_cbor (fst a), SpecRaw.mk_cbor (snd a)));
      Trade.elim _ (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_key (fst a));
      Trade.elim _ (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_value (snd a));
      rewrite (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_key (fst a))
           as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get entry) (fst a));
      rewrite (RawMatch.cbor_raw_match p entry.RawType.cbor_map_entry_value (snd a))
           as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get entry) (snd a));
      fold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
        entry (snd a));
      fold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
        entry a);
      fold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p entry a);
    }
}

fn cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match
= (x2: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_nondet_map_entry_match p x2 v2);
  Trade.intro_trade
    (cbor_nondet_match p x2.RawType.cbor_map_entry_key (fst v2))
    (cbor_nondet_map_entry_match p x2 v2)
    (cbor_nondet_match p x2.RawType.cbor_map_entry_value (snd v2))
    fn _ {
      fold (cbor_nondet_map_entry_match p x2 v2)
    };
  x2.RawType.cbor_map_entry_key
}

fn cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match
= (x2: _)
  (#p: _)
  (#v2: _)
{
  unfold (cbor_nondet_map_entry_match p x2 v2);
  Trade.intro_trade
    (cbor_nondet_match p x2.RawType.cbor_map_entry_value (snd v2))
    (cbor_nondet_map_entry_match p x2 v2)
    (cbor_nondet_match p x2.RawType.cbor_map_entry_key (fst v2))
    fn _ {
      fold (cbor_nondet_map_entry_match p x2 v2)
    };
  x2.RawType.cbor_map_entry_value
}

ghost
fn cbor_nondet_map_entry_share_priv (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match
= (x: _)
  (#p: _)
  (#v: _)
{
  unfold (cbor_nondet_map_entry_match p x v);
  cbor_nondet_share () x.RawType.cbor_map_entry_key;
  cbor_nondet_share () x.RawType.cbor_map_entry_value;
  fold (cbor_nondet_map_entry_match (p /. 2.0R) x v);
  fold (cbor_nondet_map_entry_match (p /. 2.0R) x v)
}

ghost
fn cbor_nondet_map_entry_gather_priv (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match
= (x: _)
  (#p: _)
  (#v: _)
  (#p': _)
  (#v': _)
{
  unfold (cbor_nondet_map_entry_match p x v);
  unfold (cbor_nondet_map_entry_match p' x v');
  cbor_nondet_gather () x.RawType.cbor_map_entry_key #p #_ #p';
  cbor_nondet_gather () x.RawType.cbor_map_entry_value #p #_ #p';
  fold (cbor_nondet_map_entry_match (p +. p') x v)
}

(* ============ Map iterator next ============ *)

module ReadMapEntry = CBOR.Pulse.Raw.EverParse.ReadMapEntry

#push-options "--z3rlimit 256 --fuel 2 --ifuel 1 --ext no:context_pruning"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_map_iterator_next_unsafe (_: unit) : map_iterator_next_t #_ #_ cbor_nondet_map_entry_match cbor_nondet_map_iterator_match
= (x: _)
  (#y: _)
  (#py: _)
  (#z: _)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let lr = cbor_nondet_map_iterator_match_elim y;
  rewrite (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      py y lr)
    as (I.iterator_match
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      py y lr);
  let i_cur = !x;
  let res, it' = ReadMapEntry.iterator_next_map_entry_raw_data_item f64 py i_cur lr;
  x := it';
  with pm_v hd_val tl_l pm' . assert (
    RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
    R.pts_to x it' **
    I.iterator_match
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it' tl_l **
    Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match
         (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         pm' it' tl_l)
      (I.iterator_match
         (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         py (Ghost.reveal y) (Ghost.reveal lr))
  );
  rewrite (I.iterator_match
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it' tl_l)
    as (I.iterator_match
      (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
      (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
      pm' it' tl_l);
  rewrite (Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match
         (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         pm' it' tl_l)
      (I.iterator_match
         (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         py (Ghost.reveal y) (Ghost.reveal lr)))
    as (Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm_v res hd_val **
       I.iterator_match
         (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         pm' it' tl_l)
      (I.iterator_match
         (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
         (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
         py (Ghost.reveal y) (Ghost.reveal lr)));
  // lr == hd_val :: tl_l, so map fst lr == fst hd_val :: map fst tl_l, similarly for snd
  cbor_nondet_map_entry_match_intro res;
  Trade.trans_hyp_l _ _ _ (I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    py (Ghost.reveal y) (Ghost.reveal lr));
  cbor_nondet_map_iterator_match_intro it';
  Trade.trans_hyp_r _ _ _ (I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    py (Ghost.reveal y) (Ghost.reveal lr));
  Trade.trans _ _ (cbor_nondet_map_iterator_match py (Ghost.reveal y) (Ghost.reveal z));
  res
}

#pop-options

let cbor_nondet_map_iterator_next () : map_iterator_next_safe_t #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match
= map_iterator_next_safe
    (cbor_nondet_map_iterator_is_empty ())
    (cbor_nondet_map_iterator_next_unsafe ())
    (cbor_nondet_map_entry_share_priv ())
    (cbor_nondet_map_entry_gather_priv ())
    (cbor_nondet_map_entry_key ())
    (cbor_nondet_map_entry_value ())

ghost
fn cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match
= (x: _)
  (#py: _)
  (#z: _)
{
  unfold (cbor_nondet_map_iterator_match py x z);
  with lr . assert (I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    py x lr);
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr);
      I.base_mixed_list_match_share
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py bi lr cbor_map_entry_match_share_aux;
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (py /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr);
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (py /. 2.0R) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr);
      rewrite each (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) as x;
      fold (cbor_nondet_map_iterator_match (py /. 2.0R) x z);
      fold (cbor_nondet_map_iterator_match (py /. 2.0R) x z)
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr);
      with l1 l2 . assert (
        I.base_mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py bi l1 **
        I.mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py ml l2);
      I.base_mixed_list_match_share
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py bi l1 cbor_map_entry_match_share_aux;
      I.mixed_list_match_share
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py ml l2 cbor_map_entry_match_share_aux;
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (py /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr);
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (py /. 2.0R) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr);
      rewrite each (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) as x;
      fold (cbor_nondet_map_iterator_match (py /. 2.0R) x z);
      fold (cbor_nondet_map_iterator_match (py /. 2.0R) x z)
    }
  }
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
  with lr1 . assert (I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    py1 x lr1);
  with lr2 . assert (I.iterator_match
    (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
    (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
    py2 x lr2);
  match x {
    IT.IBase bi -> {
      rewrite each x as (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py1 (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr1);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py2 (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr2);
      I.base_mixed_list_match_gather
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py1 py2 bi lr1 lr2 cbor_map_entry_match_gather_aux;
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (py1 +. py2) (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) lr1);
      rewrite each (IT.IBase #(RawType.cbor_map_entry RawType.cbor_raw) bi) as x;
      fold (cbor_nondet_map_iterator_match (py1 +. py2) x z1)
    }
    IT.IPair bi ml -> {
      rewrite each x as (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py1 (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr1);
      unfold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py2 (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr2);
      with l1a l2a . assert (
        I.base_mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py1 bi l1a **
        I.mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py1 ml l2a);
      with l1b l2b . assert (
        I.base_mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py2 bi l1b **
        I.mixed_list_match
          (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
          py2 ml l2b);
      I.base_mixed_list_match_gather
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py1 py2 bi l1a l1b cbor_map_entry_match_gather_aux;
      I.mixed_list_match_gather
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        py1 py2 ml l2a l2b cbor_map_entry_match_gather_aux;
      List.Tot.append_injective l1a l1b l2a l2b;
      fold (I.iterator_match
        (fun pm0 e v -> RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm0 e v)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        (py1 +. py2) (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) lr1);
      rewrite each (IT.IPair #(RawType.cbor_map_entry RawType.cbor_raw) bi ml) as x;
      fold (cbor_nondet_map_iterator_match (py1 +. py2) x z1)
    }
  }
}

(* Public exports for entry share/gather, placed here to match fsti ordering *)

let cbor_nondet_map_entry_share () = cbor_nondet_map_entry_share_priv ()

let cbor_nondet_map_entry_gather () = cbor_nondet_map_entry_gather_priv ()

(* ============ Equality ============ *)

#push-options "--z3rlimit 64"

#restart-solver
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
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let v1' = cbor_nondet_match_elim x1;
  let v2' = cbor_nondet_match_elim x2;
  let res = NondetCompare.compare_cbor_raw_basic f64 None x1 x2;
  Trade.elim _ (cbor_nondet_match p1 x1 v1);
  Trade.elim _ (cbor_nondet_match p2 x2 v2);
  // res == check_equiv basic_data_model None v1' v2'
  CBOR.Spec.Raw.Nondet.check_equiv_correct SpecRaw.basic_data_model None v1' v2';
  // check_equiv_cond gives: if Some b, b == raw_equiv v1' v2'; if None, exceeds_bound is impossible since None map_bound never exceeds.
  // So res must be Some b where b == raw_equiv v1' v2'.
  SpecRaw.mk_cbor_equiv v1' v2';
  // raw_equiv v1' v2' <==> mk_cbor v1' == mk_cbor v2'
  match res {
    Some b -> { b }
    None -> { false }  // unreachable since map_bound is None
  }
}

#pop-options

(* ============ Map get ============ *)

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
    pure (cbor_nondet_map_get_invariant_true_postcond vx vk vv)

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
  (cont: bool)
  (bres: bool)
requires
  cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i cont bres **
  pure ((cont && not bres) == false)
ensures
  exists* res .
    map_get_post cbor_nondet_match x px vx vk res **
    pure (Spec.CMap? (Spec.unpack vx) /\
      (Some? (Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack vx)) vk) == Some? res) /\
      mk_map_gen_by_ref_postcond (Ghost.reveal vdest0) res vdest bres
    )
{
  if bres {
    rewrite (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i cont bres)
      as (cbor_nondet_map_get_invariant_true px x vx vk vdest);
    unfold (cbor_nondet_map_get_invariant_true px x vx vk vdest);
    fold (map_get_post_some cbor_nondet_match x px vx vk vdest);
    fold (map_get_post cbor_nondet_match x px vx vk (Some vdest))
  } else {
    rewrite (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i cont bres)
      as (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i false);
    unfold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i false);
    Trade.elim _ _;
    fold (map_get_post_none cbor_nondet_match x px vx vk);
    fold (map_get_post cbor_nondet_match x px vx vk None)
  }
}

#push-options "--z3rlimit 128"

#restart-solver
inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_map_get_by_ref (_: unit)
: map_get_by_ref_t u#0 #_ cbor_nondet_match
= (x: _)
  (k: _)
  (dest: _)
  (#px: _)
  (#vx: _)
  (#pk: _)
  (#vk: _)
  (#vdest0: _)
{
  let i = cbor_nondet_map_iterator_start_unsafe () x;
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
  ) invariant exists* i vdest res cont . (
    R.pts_to pi i **
    R.pts_to dest vdest **
    R.pts_to pres res **
    R.pts_to pcont cont **
    cbor_nondet_match pk k vk **
    cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i cont res
  ) {
    with gi vdest gres gcont . assert (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest gi gcont gres);
    rewrite (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest gi gcont gres)
      as (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest gi true);
    unfold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest gi true);
    let y = cbor_nondet_map_iterator_next_unsafe () pi;
    Trade.trans _ _ (cbor_nondet_match px x vx);
    with py y_val vy . assert (cbor_nondet_map_entry_match py y_val vy);
    unfold (cbor_nondet_map_entry_match py y_val vy);
    Trade.intro_trade
      (cbor_nondet_match py y_val.RawType.cbor_map_entry_key (fst vy) **
       cbor_nondet_match py y_val.RawType.cbor_map_entry_value (snd vy))
      (cbor_nondet_map_entry_match py y_val vy)
      emp
      fn _ {
        fold (cbor_nondet_map_entry_match py y_val vy)
      };
    Trade.trans_hyp_l _ _ _ (cbor_nondet_match px x vx);
    if (cbor_nondet_equal y_val.RawType.cbor_map_entry_key k) {
      Trade.elim_hyp_r _ _ _;
      Trade.elim_hyp_l _ _ _;
      dest := y_val.RawType.cbor_map_entry_value;
      pres := true;
      fold (cbor_nondet_map_get_invariant_true px x vx vk y_val.RawType.cbor_map_entry_value);
      with i_val . assert (R.pts_to pi i_val);
      with gcont' . assert (R.pts_to pcont gcont');
      rewrite (cbor_nondet_map_get_invariant_true px x vx vk y_val.RawType.cbor_map_entry_value)
        as (cbor_nondet_map_get_invariant px x vx vdest0 vk y_val.RawType.cbor_map_entry_value i_val gcont' true)
    } else {
      Trade.elim_hyp_l _ _ _;
      let i_val = !pi;
      let cont_val = not (cbor_nondet_map_iterator_is_empty () i_val);
      pcont := cont_val;
      fold (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i_val cont_val);
      rewrite (cbor_nondet_map_get_invariant_false px x vx vdest0 vk vdest i_val cont_val)
        as (cbor_nondet_map_get_invariant px x vx vdest0 vk vdest i_val cont_val gres)
    }
  };
  let res = !pres;
  with vdest . assert (R.pts_to dest vdest);
  with i_val . assert (R.pts_to pi i_val);
  cbor_nondet_map_get_concl px x vx vdest0 vk vdest i_val _ res;
  res
}

#pop-options

let cbor_nondet_map_get () : map_get_by_ref_safe_t #_ cbor_nondet_match
= map_get_by_ref_safe (cbor_nondet_major_type ()) (cbor_nondet_map_get_by_ref ())

(* ============ Constructors ============ *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_mk_simple_value_unsafe (_: unit) : mk_simple_t u#0 #_ cbor_nondet_match
= (v: _)
{
  let res = RawMake.cbor_mk_simple_value v;
  // raw_data_item is Simple v; valid_raw_data_item (Simple v) is trivial
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Simple v);
  SpecRaw.mk_cbor_eq (SpecRaw.Simple v);
  fold (cbor_nondet_match 1.0R res (Spec.pack (Spec.CSimple v)));
  res
}

let cbor_nondet_mk_simple_value () : mk_simple_safe_t #_ cbor_nondet_match
  = mk_simple_safe (cbor_nondet_mk_simple_value_unsafe ())

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
#restart-solver

fn cbor_nondet_mk_uint64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_uint64
= (v: _)
{
  let res = RawMake.cbor_mk_int64 cbor_major_type_uint64 v;
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Int64 cbor_major_type_uint64 (SpecRaw.mk_raw_uint64 v));
  SpecRaw.mk_cbor_eq (SpecRaw.Int64 cbor_major_type_uint64 (SpecRaw.mk_raw_uint64 v));
  fold (cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 cbor_major_type_uint64 v)));
  res
}

fn cbor_nondet_mk_neg_int64 (_: unit) : mk_int64_gen_t u#0 #_ cbor_nondet_match cbor_major_type_neg_int64
= (v: _)
{
  let res = RawMake.cbor_mk_int64 cbor_major_type_neg_int64 v;
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Int64 cbor_major_type_neg_int64 (SpecRaw.mk_raw_uint64 v));
  SpecRaw.mk_cbor_eq (SpecRaw.Int64 cbor_major_type_neg_int64 (SpecRaw.mk_raw_uint64 v));
  fold (cbor_nondet_match 1.0R res (Spec.pack (Spec.CInt64 cbor_major_type_neg_int64 v)));
  res
}

#pop-options

let cbor_nondet_mk_int64 () : mk_signed_int64_t #_ cbor_nondet_match
  = mk_signed_int64 (mk_int64_dispatch _ (cbor_nondet_mk_uint64 ()) (cbor_nondet_mk_neg_int64 ()))

(* ============ String constructor ============ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_mk_string (_: unit) : mk_string_t u#0 #_ cbor_nondet_match
= (ty: _)
  (s: _)
  (#p: _)
  (#v: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  Pulse.Lib.Slice.pts_to_len s;
  let res_raw = RawMake.cbor_mk_string f64 ty s;
  with r . assert (RawMatch.cbor_raw_match 1.0R res_raw r);
  // pure facts from cbor_mk_string
  let _p = elim_pure_explicit (
    CBOR.Spec.Raw.Optimal.raw_data_item_ints_optimal r /\
    CBOR.Spec.Raw.Sort.raw_data_item_sorted CBOR.Spec.Raw.Format.deterministically_encoded_cbor_map_key_order r /\
    SpecRaw.valid_raw_data_item r /\
    SpecRaw.mk_det_raw_cbor (SpecRaw.mk_cbor r) == Ghost.reveal r /\
    SpecRaw.String? r /\
    SpecRaw.String?.typ r == ty /\
    (SpecRaw.String?.v r <: Seq.seq FStar.UInt8.t) == Ghost.reveal v
  );
  SpecRaw.mk_cbor_eq (Ghost.reveal r);
  // mk_cbor r == pack (CString ty v)
  // Reset perm from 1.0R to 2.0R on a new value res, so that intro can give us wrapper at 1.0R.
  let res = ResetPerm.cbor_raw_reset_perm 1.0R res_raw 2.0R;
  // Now: raw_match 2.0R res r ** trade (raw_match 2.0R res r) (raw_match 1.0R res_raw r)
  cbor_nondet_match_intro res;
  // Now: cbor_nondet_match (2.0R /. 2.0R) res (mk_cbor r) ** trade (...) (raw_match 2.0R res r)
  rewrite each (2.0R /. 2.0R) as 1.0R;
  rewrite each (SpecRaw.mk_cbor (Ghost.reveal r)) as (Spec.pack (Spec.CString ty v));
  // Compose trades: wrapper → raw_match 2.0R res r → raw_match 1.0R res_raw r → slice_pts_to
  Trade.trans _ _ (RawMatch.cbor_raw_match 1.0R res_raw r);
  Trade.trans _ _ (Pulse.Lib.Slice.pts_to s #p v);
  res
}

#pop-options

(* ============ Tagged constructor ============ *)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_mk_tagged_unsafe (_: unit) : mk_tagged_t u#0 #_ cbor_nondet_match
= (tag: _)
  (r: _)
  (#pr: _)
  (#v: _)
  (#pv: _)
  (#v': _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  let tag64 = SpecRaw.mk_raw_uint64 tag;
  // Elim cbor_nondet_match into raw match (preserves a trade back)
  let vraw = cbor_nondet_match_elim v;
  // raw_match pv v vraw ** trade_back: (raw_match pv v vraw) → (cbor_nondet_match pv v v')
  let res_raw = RawMake.cbor_mk_tagged tag r;
  with rraw . assert (RawMatch.cbor_raw_match 1.0R res_raw rraw);
  // pure facts: rraw == Tagged tag64 vraw
  let _ = elim_pure_explicit (Ghost.reveal rraw == SpecRaw.Tagged tag64 (Ghost.reveal vraw));
  SpecRaw.valid_eq SpecRaw.basic_data_model (Ghost.reveal rraw);
  SpecRaw.mk_cbor_eq (Ghost.reveal rraw);
  // mk_cbor (Tagged tag64 vraw) == pack (CTagged tag (mk_cbor vraw)) == pack (CTagged tag v')
  // Reset perm 1.0R → 2.0R so intro can give wrapper at 1.0R
  let res = ResetPerm.cbor_raw_reset_perm 1.0R res_raw 2.0R;
  cbor_nondet_match_intro res;
  rewrite each (2.0R /. 2.0R) as 1.0R;
  rewrite each (SpecRaw.mk_cbor (Ghost.reveal rraw)) as (Spec.pack (Spec.CTagged tag v'));
  // Now: cbor_nondet_match 1.0R res (CTagged tag v') ** trade (wrapper) (raw_match 2.0R res rraw) **
  //      trade (raw_match 2.0R res rraw) (raw_match 1.0R res_raw rraw) **
  //      trade (raw_match 1.0R res_raw rraw) (R.pts_to r #pr v ** raw_match pv v vraw) **
  //      trade (raw_match pv v vraw) (cbor_nondet_match pv v v')
  Trade.trans _ (RawMatch.cbor_raw_match 1.0R res_raw rraw) _;
  // Now: trade (raw_match 2.0R res rraw) (R.pts_to r #pr v ** raw_match pv v vraw)
  // Use trans_concl_r to convert raw_match pv vraw → cbor_nondet_match pv v v' on the rhs
  Trade.trans_concl_r
    (RawMatch.cbor_raw_match 2.0R res rraw)
    (R.pts_to r #pr v)
    (RawMatch.cbor_raw_match pv v vraw)
    (cbor_nondet_match pv v v');
  // Now: trade (raw_match 2.0R res rraw) (R.pts_to r #pr v ** cbor_nondet_match pv v v')
  Trade.trans _ (RawMatch.cbor_raw_match 2.0R res rraw) _;
  res
}

#pop-options

let cbor_nondet_mk_tagged () : mk_tagged_safe_t #_ cbor_nondet_match
  = mk_tagged_safe (cbor_nondet_mk_tagged_unsafe ())


(* ============ Map entry constructor (moved below mk_array) ============ *)

(* ============ Array constructor ============ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn rec seq_list_cbor_nondet_match_to_raw_trade
  (p: perm)
  (c: Seq.seq RawType.cbor_raw)
  (v: list Spec.cbor)
  requires PM.seq_list_match c v (cbor_nondet_match p)
  returns v_raw: Ghost.erased (list SpecRawBase.raw_data_item)
  ensures
    PM.seq_list_match c v_raw (RawMatch.cbor_raw_match p) **
    Trade.trade
      (PM.seq_list_match c v_raw (RawMatch.cbor_raw_match p))
      (PM.seq_list_match c v (cbor_nondet_match p)) **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item v_raw /\
      Ghost.reveal v == List.Tot.map SpecRaw.mk_cbor v_raw
    )
  decreases v
{
  PM.seq_list_match_length (cbor_nondet_match p) c v;
  if (Nil? v) {
    PM.seq_list_match_nil_elim c v (cbor_nondet_match p);
    PM.seq_list_match_nil_intro c [] (RawMatch.cbor_raw_match p);
    Trade.intro_trade
      (PM.seq_list_match c [] (RawMatch.cbor_raw_match p))
      (PM.seq_list_match c v (cbor_nondet_match p))
      emp
      fn _ {
        PM.seq_list_match_nil_elim c [] (RawMatch.cbor_raw_match p);
        PM.seq_list_match_nil_intro c v (cbor_nondet_match p);
      };
    []
  } else {
    PMU.seq_list_match_cons_elim_trade c v (cbor_nondet_match p);
    let h = cbor_nondet_match_elim (Seq.head c);
    Trade.trans_hyp_l _ _ _ (PM.seq_list_match c v (cbor_nondet_match p));
    let q = seq_list_cbor_nondet_match_to_raw_trade p (Seq.tail c) (List.Tot.tl v);
    Trade.trans_hyp_r _ _ _ (PM.seq_list_match c v (cbor_nondet_match p));
    PMU.seq_list_match_cons_intro_trade
      (Seq.head c) (Ghost.reveal h)
      (Seq.tail c) q
      (RawMatch.cbor_raw_match p);
    Trade.trans _ _ (PM.seq_list_match c v (cbor_nondet_match p));
    rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
    (Ghost.reveal h :: q)
  }
}

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --ext no:context_pruning"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_mk_array_inner (_: unit) : mk_array_t cbor_nondet_match
= (a: _) (#pa: _) (#va: _) (#pv: _) (#vv: _)
{
  let f64 : squash (SZ.fits_u64) = assume (SZ.fits_u64);
  S.pts_to_len a;
  PM.seq_list_match_length (cbor_nondet_match pv) va vv;
  // 1. Bridge seq_list cbor_nondet_match → cbor_raw_match (via trade)
  let l_raw = seq_list_cbor_nondet_match_to_raw_trade pv va vv;
  // Now: PM.seq_list_match va l_raw (RawMatch.cbor_raw_match pv) **
  //      Trade(seq_list va l_raw (cbor_raw_match pv) ==> seq_list va vv (cbor_nondet_match pv))
  //      vv == List.Tot.map mk_cbor l_raw

  // 2. Share pts_to a
  S.share a;
  let sp = pa /. 2.0R;
  // Now: pts_to a #sp va ** pts_to a #sp va (saved half for trade)
  // 3. Build Slice mixed_list
  let bml : IT.base_mixed_list RawType.cbor_raw = IT.Slice sp pv a;
  let ml : IT.mixed_list RawType.cbor_raw = IT.Base bml;
  rewrite (S.pts_to a #sp va)
       as (S.pts_to a #(1.0R *. sp) va);
  rewrite (PM.seq_list_match va l_raw (RawMatch.cbor_raw_match pv))
       as (PM.seq_list_match va l_raw (RawMatch.cbor_raw_match (1.0R *. pv)));
  assert (pure (IT.base_mixed_list_length (IT.Slice #(RawType.cbor_raw) sp pv a) == S.len a));
  fold (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (S.len a)) 1.0R (IT.Slice #(RawType.cbor_raw) sp pv a) l_raw);
  rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (S.len a)) 1.0R (IT.Slice #(RawType.cbor_raw) sp pv a) l_raw)
       as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R bml l_raw);
  fold (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_raw) bml) l_raw);
  rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_raw) bml) l_raw)
       as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml)) 1.0R ml l_raw);
  fold (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 1.0R ml l_raw);
  // 4. Compute length and call cbor_mk_array
  let len_sz = S.len a;
  let len64 = SZ.sizet_to_uint64 len_sz;
  let ru = SpecRaw.mk_raw_uint64 len64;
  let res_raw = RawMake.cbor_mk_array f64 ru.size ml;
  // Postcondition: cbor_raw_match 1.0R res_raw xh ** trade(... ==> mixed_list_match)
  //   where xh == cbor_mk_array_xh ru.size (mixed_list_length ml) l_raw
  with xh . assert (RawMatch.cbor_raw_match 1.0R res_raw xh);
  let _ = elim_pure_explicit (Ghost.reveal xh == RawMake.cbor_mk_array_xh ru.size (IT.mixed_list_length ml) l_raw);
  assert (pure (IT.mixed_list_length ml == len_sz));
  assert (pure (List.Tot.length l_raw == SZ.v len_sz));
  assert (pure (Ghost.reveal xh == SpecRaw.Array ru l_raw));
  SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Array ru l_raw);
  SpecRaw.mk_cbor_eq (SpecRaw.Array ru l_raw);
  List.Tot.map_lemma SpecRaw.mk_cbor l_raw;
  // mk_cbor (Array ru l_raw) == pack (CArray (List.Tot.map mk_cbor l_raw)) == pack (CArray vv)
  // 5. Build the "rest" trade: from mixed_list_match → (S.pts_to a #pa va ** seq_list_match va vv (cbor_nondet_match pv))
  Trade.intro_trade
    (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 1.0R ml l_raw)
    (S.pts_to a #pa va ** PM.seq_list_match va vv (cbor_nondet_match pv))
    (S.pts_to a #sp va **
     Trade.trade
       (PM.seq_list_match va l_raw (RawMatch.cbor_raw_match pv))
       (PM.seq_list_match va vv (cbor_nondet_match pv)))
    fn _ {
      unfold (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 1.0R ml l_raw);
      rewrite (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.mixed_list_length ml)) 1.0R ml l_raw)
           as (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_raw) bml) l_raw);
      unfold (I.mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_raw) bml) l_raw);
      rewrite (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R bml l_raw)
           as (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (S.len a)) 1.0R (IT.Slice #(RawType.cbor_raw) sp pv a) l_raw);
      unfold (I.base_mixed_list_match_n RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 0 (SZ.v (S.len a)) 1.0R (IT.Slice #(RawType.cbor_raw) sp pv a) l_raw);
      S.gather a;
      with l' l1 . assert (
        S.pts_to a #(sp +. sp) l' **
        PM.seq_list_match l1 l_raw (RawMatch.cbor_raw_match (1.0R *. pv)));
      rewrite each l' as va;
      rewrite each l1 as va;
      rewrite (S.pts_to a #(sp +. sp) va) as (S.pts_to a #pa va);
      rewrite (PM.seq_list_match va l_raw (RawMatch.cbor_raw_match (1.0R *. pv)))
           as (PM.seq_list_match va l_raw (RawMatch.cbor_raw_match pv));
      Trade.elim _ (PM.seq_list_match va vv (cbor_nondet_match pv));
    };
  // 6. Compose: cbor_mk_array's trade and the rest trade
  Trade.trans _ (I.mixed_list_match RawMatch.cbor_raw_match SpecRawEverParse.parse_raw_data_item 1.0R ml l_raw) _;
  // Now: trade (raw_match 1.0R res_raw xh) (S.pts_to a #pa va ** seq_list_match va vv (cbor_nondet_match pv))
  // 7. Apply reset_perm to double the raw_match permission
  let res = ResetPerm.cbor_raw_reset_perm 1.0R res_raw 2.0R;
  // raw_match 2.0R res xh ** trade (raw_match 2.0R res xh) (raw_match 1.0R res_raw xh)
  cbor_nondet_match_intro res;
  // cbor_nondet_match 1.0R res (mk_cbor xh) ** trade (wrapper) (raw_match 2.0R res xh)
  rewrite each (2.0R /. 2.0R) as 1.0R;
  rewrite each (SpecRaw.mk_cbor (Ghost.reveal xh)) as (Spec.pack (Spec.CArray vv));
  // Compose trades
  Trade.trans _ (RawMatch.cbor_raw_match 1.0R res_raw xh) _;
  Trade.trans _ (RawMatch.cbor_raw_match 2.0R res xh) _;
  res
}

#pop-options

(* ============ Map entry constructor ============ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
#restart-solver

fn cbor_nondet_mk_map_entry (_: unit) : mk_map_entry_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_map_entry_match
= (xk: _)
  (xv: _)
  (#pk: _)
  (#vk: _)
  (#pv: _)
  (#vv: _)
{
  // Reset permissions on both inputs to 1.0R
  let xk' = cbor_nondet_reset_perm () xk 1.0R;
  let xv' = cbor_nondet_reset_perm () xv 1.0R;
  Trade.prod (cbor_nondet_match 1.0R xk' vk) _ (cbor_nondet_match 1.0R xv' vv) _;

  let res : RawType.cbor_map_entry RawType.cbor_raw = {
    RawType.cbor_map_entry_key = xk';
    RawType.cbor_map_entry_value = xv';
  };
  Trade.rewrite_with_trade
    (cbor_nondet_match 1.0R xk' vk ** cbor_nondet_match 1.0R xv' vv)
    (cbor_nondet_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv));
  Trade.trans (cbor_nondet_map_entry_match 1.0R res (Ghost.reveal vk, Ghost.reveal vv)) _ _;
  res
}

#pop-options

(* ============ Map constructor ============ *)

(* Wrap NondetCompare.compare_cbor_raw as a raw-level equality check.
   For basic_data_model and map_bound=None, the result is always Some b
   where b == raw_equiv. *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_raw_equiv
  (x1: RawType.cbor_raw)
  (x2: RawType.cbor_raw)
  (#p1: perm)
  (#v1: Ghost.erased SpecRawBase.raw_data_item)
  (#p2: perm)
  (#v2: Ghost.erased SpecRawBase.raw_data_item)
requires
  RawMatch.cbor_raw_match p1 x1 v1 **
  RawMatch.cbor_raw_match p2 x2 v2 **
  pure (
    SpecRaw.valid_raw_data_item v1 /\
    SpecRaw.valid_raw_data_item v2
  )
returns res: bool
ensures
  RawMatch.cbor_raw_match p1 x1 v1 **
  RawMatch.cbor_raw_match p2 x2 v2 **
  pure (res == SpecRaw.raw_equiv v1 v2)
{
  let f64 : squash SZ.fits_u64 = assume SZ.fits_u64;
  let res = NondetCompare.compare_cbor_raw_basic f64 None x1 x2;
  CBOR.Spec.Raw.Nondet.check_equiv_correct SpecRaw.basic_data_model None v1 v2;
  match res {
    Some b -> { b }
    None -> { false }  // unreachable since map_bound = None
  }
}

(* Check that input slice of map entries has no two keys equivalent under raw_equiv.
   Ported from old/CBOR.Pulse.Raw.Nondet.Compare.cbor_nondet_no_setoid_repeats. *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --ext no:context_pruning"
#restart-solver

fn cbor_nondet_no_setoid_repeats
  (x: S.slice (RawType.cbor_map_entry RawType.cbor_raw))
  (#px: perm)
  (#s: Ghost.erased (Seq.seq (RawType.cbor_map_entry RawType.cbor_raw)))
  (#ps: perm)
  (#l: Ghost.erased (list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)))
requires
  S.pts_to x #px s **
  PM.seq_list_match s l (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) **
  pure (
    List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l)
  )
returns res: bool
ensures
  S.pts_to x #px s **
  PM.seq_list_match s l (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) **
  pure (res == CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l))
{
  S.pts_to_len x;
  let mut pn1 = 0sz;
  let mut pres = true;
  Trade.refl (PM.seq_list_match s l (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps));
  while (
    let res = !pres;
    PM.seq_list_match_length (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) _ _;
    (res && SZ.lt !pn1 (S.len x))
  ) invariant exists* n1 res s1 l1 . (
    S.pts_to x #px s **
    R.pts_to pn1 n1 **
    R.pts_to pres res **
    PM.seq_list_match s1 l1 (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) **
    Trade.trade
      (PM.seq_list_match s1 l1 (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps))
      (PM.seq_list_match s l (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps)) **
    pure (
      SZ.v n1 <= Seq.length s /\
      Seq.equal s1 (Seq.slice s (SZ.v n1) (Seq.length s)) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l1) /\
      CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l) ==
        (res && CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l1))
    )
  ) {
    PM.seq_list_match_length (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) _ _;
    let n1 = !pn1;
    let x1 = S.op_Array_Access x n1;
    PMU.seq_list_match_cons_elim_trade _ _ (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps);
    Trade.trans _ _ (PM.seq_list_match s l (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps));
    with gx1 y1 . assert (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps gx1 y1);
    rewrite each gx1 as x1;
    let n2 : SZ.t = SZ.add n1 1sz;
    pn1 := n2;
    let mut pn2 = n2;
    with s1' l1' . assert (PM.seq_list_match s1' l1' (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps));
    Trade.refl (PM.seq_list_match s1' l1' (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps));
    while (
      let res = !pres;
      PM.seq_list_match_length (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) _ _;
      (res && SZ.lt !pn2 (S.len x))
    ) invariant exists* n2 res s2 l2 . (
      S.pts_to x #px s **
      RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x1 y1 **
      R.pts_to pn2 n2 **
      R.pts_to pres res **
      PM.seq_list_match s2 l2 (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) **
      Trade.trade
        (PM.seq_list_match s2 l2 (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps))
        (PM.seq_list_match s1' l1' (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps)) **
      pure (
        SZ.v n2 <= Seq.length s /\
        Seq.equal s2 (Seq.slice s (SZ.v n2) (Seq.length s)) /\
        List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst l2) /\
        CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l) ==
          (res && (not (List.Tot.existsb (SpecRaw.raw_equiv (fst y1)) (List.Tot.map fst l2))) &&
           CBOR.Spec.Util.list_no_setoid_repeats SpecRaw.raw_equiv (List.Tot.map fst l1'))
      )
    ) {
      PM.seq_list_match_length (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps) _ _;
      let n2 = !pn2;
      let x2 = S.op_Array_Access x n2;
      PMU.seq_list_match_cons_elim_trade _ _ (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps);
      with gx2 y2 . assert (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x1 y1 **
                            RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps gx2 y2);
      rewrite each gx2 as x2;
      // Use existing cbor_map_entry_match_share_aux which unfolds to RawMatch on key/value
      unfold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x1 y1);
      unfold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj)
        x1 y1);
      unfold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj
        x1 (snd y1));
      rewrite (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get x1) (fst y1))
           as (RawMatch.cbor_raw_match ps x1.RawType.cbor_map_entry_key (fst y1));
      rewrite (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get x1) (snd y1))
           as (RawMatch.cbor_raw_match ps x1.RawType.cbor_map_entry_value (snd y1));
      unfold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x2 y2);
      unfold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj)
        x2 y2);
      unfold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj
        x2 (snd y2));
      rewrite (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get x2) (fst y2))
           as (RawMatch.cbor_raw_match ps x2.RawType.cbor_map_entry_key (fst y2));
      rewrite (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get x2) (snd y2))
           as (RawMatch.cbor_raw_match ps x2.RawType.cbor_map_entry_value (snd y2));

      pres := not (cbor_nondet_raw_equiv x1.RawType.cbor_map_entry_key x2.RawType.cbor_map_entry_key);

      // Re-fold x1
      rewrite (RawMatch.cbor_raw_match ps x1.RawType.cbor_map_entry_key (fst y1))
           as (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get x1) (fst y1));
      rewrite (RawMatch.cbor_raw_match ps x1.RawType.cbor_map_entry_value (snd y1))
           as (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get x1) (snd y1));
      fold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj
        x1 (snd y1));
      fold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj)
        x1 y1);
      fold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x1 y1);
      // Re-fold x2
      rewrite (RawMatch.cbor_raw_match ps x2.RawType.cbor_map_entry_key (fst y2))
           as (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get x2) (fst y2));
      rewrite (RawMatch.cbor_raw_match ps x2.RawType.cbor_map_entry_value (snd y2))
           as (RawMatch.cbor_raw_match ps (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get x2) (snd y2));
      fold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj
        x2 (snd y2));
      fold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match ps) RawMatch.cbor_map_entry_value_proj)
        x2 y2);
      fold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x2 y2);

      Trade.elim_hyp_l (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps x2 y2) _ _;
      Trade.trans _ _ (PM.seq_list_match s1' l1' (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps));
      pn2 := SZ.add n2 1sz;
    };
    Trade.elim_hyp_l _ _ _;
    Trade.elim _ (PM.seq_list_match s1' l1' (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match ps));
    ()
  };
  Trade.elim _ _;
  !pres
}

#pop-options


(* ============ Bridges for map seq_list (cbor_nondet → raw) ============ *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
#restart-solver

ghost
fn cbor_nondet_map_entry_to_raw_trade
  (p: perm)
  (e: RawType.cbor_map_entry RawType.cbor_raw)
  (v: Spec.cbor & Spec.cbor)
  requires cbor_nondet_map_entry_match p e v
  returns h: Ghost.erased (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)
  ensures
    RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e h **
    Trade.trade
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e h)
      (cbor_nondet_map_entry_match p e v) **
    pure (
      SpecRaw.valid_raw_data_item (fst h) /\
      SpecRaw.valid_raw_data_item (snd h) /\
      fst v == SpecRaw.mk_cbor (fst h) /\
      snd v == SpecRaw.mk_cbor (snd h)
    )
{
  unfold (cbor_nondet_map_entry_match p e v);
  // Now: cbor_nondet_match p e.key (fst v) ** cbor_nondet_match p e.value (snd v)
  let hfst = cbor_nondet_match_elim e.RawType.cbor_map_entry_key;
  let hsnd = cbor_nondet_match_elim e.RawType.cbor_map_entry_value;
  // Now have raw matches + trades back to cbor_nondet_match
  Trade.prod
    (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key hfst)
    _
    (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value hsnd)
    _;
  // T_prod : (raw match key fst ** raw match value snd) ==> (nondet match key ** nondet match value)
  let h : Ghost.erased (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item) =
    Ghost.hide (Ghost.reveal hfst, Ghost.reveal hsnd);
  // Now fold raw_match pair into cbor_map_entry_match via projectors
  rewrite (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value hsnd)
       as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get e) (snd (Ghost.reveal h)));
  fold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
    e (snd (Ghost.reveal h)));
  rewrite (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key hfst)
       as (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get e) (fst (Ghost.reveal h)));
  fold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
    (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
    e (Ghost.reveal h));
  fold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e (Ghost.reveal h));
  // Build the trade: from RawMatch.cbor_map_entry_match h back to cbor_nondet_map_entry_match v
  Trade.intro_trade
    (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e (Ghost.reveal h))
    (cbor_nondet_map_entry_match p e v)
    (Trade.trade
      (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key hfst **
       RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value hsnd)
      (cbor_nondet_match p e.RawType.cbor_map_entry_key (fst v) **
       cbor_nondet_match p e.RawType.cbor_map_entry_value (snd v)))
    fn _ {
      // Unfold RawMatch.cbor_map_entry_match
      unfold (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p e (Ghost.reveal h));
      unfold (Proj.vmatch_pair_with_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_key_proj
        (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj)
        e (Ghost.reveal h));
      unfold (Proj.vmatch_with_pair_proj (RawMatch.cbor_raw_match p) RawMatch.cbor_map_entry_value_proj
        e (snd (Ghost.reveal h)));
      rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_key_proj.Proj.pair_proj_get e) (fst (Ghost.reveal h)))
           as (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_key hfst);
      rewrite (RawMatch.cbor_raw_match p (RawMatch.cbor_map_entry_value_proj.Proj.pair_proj_get e) (snd (Ghost.reveal h)))
           as (RawMatch.cbor_raw_match p e.RawType.cbor_map_entry_value hsnd);
      Trade.elim _ (cbor_nondet_match p e.RawType.cbor_map_entry_key (fst v) **
                    cbor_nondet_match p e.RawType.cbor_map_entry_value (snd v));
      fold (cbor_nondet_map_entry_match p e v);
    };
  h
}

#pop-options

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
#restart-solver

ghost
fn rec seq_list_cbor_nondet_map_entry_match_to_raw_trade
  (p: perm)
  (c: Seq.seq (RawType.cbor_map_entry RawType.cbor_raw))
  (v: list (Spec.cbor & Spec.cbor))
  requires PM.seq_list_match c v (cbor_nondet_map_entry_match p)
  returns v_raw: Ghost.erased (list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
  ensures
    PM.seq_list_match c v_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p) **
    Trade.trade
      (PM.seq_list_match c v_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p))
      (PM.seq_list_match c v (cbor_nondet_map_entry_match p)) **
    pure (
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map fst v_raw) /\
      List.Tot.for_all SpecRaw.valid_raw_data_item (List.Tot.map snd v_raw) /\
      Ghost.reveal v == List.Tot.map SpecRaw.mk_cbor_map_entry v_raw
    )
  decreases v
{
  PM.seq_list_match_length (cbor_nondet_map_entry_match p) c v;
  if (Nil? v) {
    PM.seq_list_match_nil_elim c v (cbor_nondet_map_entry_match p);
    PM.seq_list_match_nil_intro c [] (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p);
    Trade.intro_trade
      (PM.seq_list_match c [] (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p))
      (PM.seq_list_match c v (cbor_nondet_map_entry_match p))
      emp
      fn _ {
        PM.seq_list_match_nil_elim c [] (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p);
        PM.seq_list_match_nil_intro c v (cbor_nondet_map_entry_match p);
      };
    []
  } else {
    PMU.seq_list_match_cons_elim_trade c v (cbor_nondet_map_entry_match p);
    let h = cbor_nondet_map_entry_to_raw_trade p (Seq.head c) (List.Tot.hd v);
    Trade.trans_hyp_l _ _ _ (PM.seq_list_match c v (cbor_nondet_map_entry_match p));
    let q = seq_list_cbor_nondet_map_entry_match_to_raw_trade p (Seq.tail c) (List.Tot.tl v);
    Trade.trans_hyp_r _ _ _ (PM.seq_list_match c v (cbor_nondet_map_entry_match p));
    PMU.seq_list_match_cons_intro_trade
      (Seq.head c) (Ghost.reveal h)
      (Seq.tail c) q
      (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match p);
    Trade.trans _ _ (PM.seq_list_match c v (cbor_nondet_map_entry_match p));
    rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
    (Ghost.reveal h :: q)
  }
}

#pop-options


(* ============ Helper: fits_mod ============ *)

noextract
let fits_mod_nondet (x: nat) (n: pos) : Lemma
  (requires x <= pow2 n - 1)
  (ensures FStar.UInt.fits x n)
= ()

(* ============ mk_map_gen ============ *)

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --ext no:context_pruning"
#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
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
  PM.seq_list_match_length (cbor_nondet_map_entry_match pv) va vv;
  let f64 : squash SZ.fits_u64 = assume (SZ.fits_u64);
  if (SZ.gt (S.len a) (SZ.uint64_to_sizet 18446744073709551615uL)) {
    Trade.refl (PM.seq_list_match va vv (cbor_nondet_map_entry_match pv));
    fold (mk_map_gen_post cbor_nondet_match cbor_nondet_map_entry_match a va pv vv None);
    false
  } else {
    // 1. Bridge: cbor_nondet_map_entry_match → RawMatch.cbor_map_entry_match (raw)
    let l_raw = seq_list_cbor_nondet_map_entry_match_to_raw_trade pv va vv;
    // Now: seq_list_match va l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pv) ** trade
    //      vv == List.Tot.map mk_cbor_map_entry l_raw
    //      for_all valid (map fst l_raw) /\ for_all valid (map snd l_raw)
    PM.seq_list_match_length (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pv) va l_raw;
    // 2. No setoid repeats check
    let correct = cbor_nondet_no_setoid_repeats a;
    if (correct) {
      // 3. Build mixed_list (similar to mk_array)
      SpecRaw.list_no_repeats_map_fst_mk_cbor_map_entry l_raw;
      // Now: List.Tot.no_repeats_p (List.Tot.map fst vv)
      S.share a;
      let sp = 1.0R /. 2.0R;
      // S.pts_to a #sp va ** S.pts_to a #sp va (array perm is 1.0R)
      let bml : IT.base_mixed_list (RawType.cbor_map_entry RawType.cbor_raw) = IT.Slice sp pv a;
      let ml : IT.mixed_list (RawType.cbor_map_entry RawType.cbor_raw) = IT.Base bml;
      rewrite (S.pts_to a #sp va)
           as (S.pts_to a #(1.0R *. sp) va);
      rewrite (PM.seq_list_match va l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pv))
           as (PM.seq_list_match va l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (1.0R *. pv)));
      assert (pure (IT.base_mixed_list_length (IT.Slice #(RawType.cbor_map_entry RawType.cbor_raw) sp pv a) == S.len a));
      fold (I.base_mixed_list_match_n
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        0 (SZ.v (S.len a)) 1.0R
        (IT.Slice #(RawType.cbor_map_entry RawType.cbor_raw) sp pv a) l_raw);
      rewrite (I.base_mixed_list_match_n
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        0 (SZ.v (S.len a)) 1.0R
        (IT.Slice #(RawType.cbor_map_entry RawType.cbor_raw) sp pv a) l_raw)
           as (I.base_mixed_list_match_n
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R bml l_raw);
      fold (I.mixed_list_match_n
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_map_entry RawType.cbor_raw) bml) l_raw);
      rewrite (I.mixed_list_match_n
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_map_entry RawType.cbor_raw) bml) l_raw)
           as (I.mixed_list_match_n
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
        0 (SZ.v (IT.mixed_list_length ml)) 1.0R ml l_raw);
      fold (I.mixed_list_match
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item) 1.0R ml l_raw);
      // 4. Call cbor_mk_map
      let len_sz = S.len a;
      let len64 = SZ.sizet_to_uint64 len_sz;
      let ru = SpecRaw.mk_raw_uint64 len64;
      fits_mod_nondet (SZ.v (S.len a)) U64.n;
      let res_raw = RawMake.cbor_mk_map f64 ru.size ml;
      with xh . assert (RawMatch.cbor_raw_match 1.0R res_raw xh);
      let _ = elim_pure_explicit (Ghost.reveal xh == RawMake.cbor_mk_map_xh ru.size (IT.mixed_list_length ml) l_raw);
      assert (pure (IT.mixed_list_length ml == len_sz));
      assert (pure (List.Tot.length l_raw == SZ.v len_sz));
      assert (pure (Ghost.reveal xh == SpecRaw.Map ru l_raw));
      SpecRaw.valid_eq SpecRaw.basic_data_model (SpecRaw.Map ru l_raw);
      SpecRaw.mk_cbor_eq (SpecRaw.Map ru l_raw);
      let m : Ghost.erased Spec.cbor_map = Ghost.hide (Spec.CMap?.c (Spec.unpack (SpecRaw.mk_cbor (Ghost.reveal xh))));
      Spec.pack_unpack (SpecRaw.mk_cbor (Ghost.reveal xh));
      Classical.forall_intro (SpecRaw.list_assoc_map_mk_cbor_map_entry m l_raw ());
      let v_pack : Ghost.erased Spec.cbor = Ghost.hide (Spec.pack (Spec.CMap m));
      // 5. Build the "rest" trade: mixed_list_match → (S.pts_to a #1.0R va ** seq_list_match va vv (cbor_nondet_map_entry_match pv))
      Trade.intro_trade
        (I.mixed_list_match
          (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
            RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
          (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item) 1.0R ml l_raw)
        (S.pts_to a #1.0R va ** PM.seq_list_match va vv (cbor_nondet_map_entry_match pv))
        (S.pts_to a #sp va **
         Trade.trade
           (PM.seq_list_match va l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pv))
           (PM.seq_list_match va vv (cbor_nondet_map_entry_match pv)))
        fn _ {
          unfold (I.mixed_list_match
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item) 1.0R ml l_raw);
          rewrite (I.mixed_list_match_n
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            0 (SZ.v (IT.mixed_list_length ml)) 1.0R ml l_raw)
               as (I.mixed_list_match_n
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_map_entry RawType.cbor_raw) bml) l_raw);
          unfold (I.mixed_list_match_n
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R (IT.Base #(RawType.cbor_map_entry RawType.cbor_raw) bml) l_raw);
          rewrite (I.base_mixed_list_match_n
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            0 (SZ.v (IT.base_mixed_list_length bml)) 1.0R bml l_raw)
               as (I.base_mixed_list_match_n
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            0 (SZ.v (S.len a)) 1.0R (IT.Slice #(RawType.cbor_map_entry RawType.cbor_raw) sp pv a) l_raw);
          unfold (I.base_mixed_list_match_n
            (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
              RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
            (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item)
            0 (SZ.v (S.len a)) 1.0R (IT.Slice #(RawType.cbor_map_entry RawType.cbor_raw) sp pv a) l_raw);
          S.gather a;
          with l' l1 . assert (
            S.pts_to a #(sp +. sp) l' **
            PM.seq_list_match l1 l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (1.0R *. pv)));
          rewrite each l' as va;
          rewrite each l1 as va;
          rewrite (S.pts_to a #(sp +. sp) va) as (S.pts_to a #1.0R va);
          rewrite (PM.seq_list_match va l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match (1.0R *. pv)))
               as (PM.seq_list_match va l_raw (RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pv));
          Trade.elim _ (PM.seq_list_match va vv (cbor_nondet_map_entry_match pv));
        };
      // 6. Compose: cbor_mk_map's trade and the rest trade
      Trade.trans _ (I.mixed_list_match
        (fun (pm': perm) (elem: RawType.cbor_map_entry RawType.cbor_raw) (x: (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) ->
          RawMatch.cbor_map_entry_match RawMatch.cbor_raw_match pm' elem x)
        (LowParse.Spec.Combinators.nondep_then SpecRawEverParse.parse_raw_data_item SpecRawEverParse.parse_raw_data_item) 1.0R ml l_raw) _;
      // Now: trade (raw_match 1.0R res_raw xh) (S.pts_to a #1.0R va ** seq_list_match va vv (cbor_nondet_map_entry_match pv))
      // 7. Apply reset_perm to double the raw_match permission
      let res = ResetPerm.cbor_raw_reset_perm 1.0R res_raw 2.0R;
      // raw_match 2.0R res xh ** trade (raw_match 2.0R res xh) (raw_match 1.0R res_raw xh)
      cbor_nondet_match_intro res;
      // cbor_nondet_match 1.0R res (mk_cbor xh) ** trade (wrapper) (raw_match 2.0R res xh)
      rewrite each (2.0R /. 2.0R) as 1.0R;
      rewrite each (SpecRaw.mk_cbor (Ghost.reveal xh)) as (Ghost.reveal v_pack);
      // Compose trades
      Trade.trans _ (RawMatch.cbor_raw_match 1.0R res_raw xh) _;
      Trade.trans _ (RawMatch.cbor_raw_match 2.0R res xh) _;
      // Expose v_pack == pack (CMap m) so fold can unify
      rewrite each (Ghost.reveal v_pack) as (Spec.pack (Spec.CMap m));
      assert (pure (Spec.cbor_map_length m == Seq.length va));
      fold (mk_map_gen_post cbor_nondet_match cbor_nondet_map_entry_match a va pv vv (Some res));
      dest := res;
      true
    } else {
      // Negative case: ~ list_no_setoid_repeats raw_equiv (map fst l_raw)
      // By bridge: ~ List.Tot.no_repeats_p (List.Tot.map fst vv)
      SpecRaw.list_no_repeats_map_fst_mk_cbor_map_entry l_raw;
      Trade.elim _ (PM.seq_list_match va vv (cbor_nondet_map_entry_match pv));
      Trade.refl (PM.seq_list_match va vv (cbor_nondet_map_entry_match pv));
      assert (pure (mk_map_gen_none_postcond va vv va vv));
      fold (mk_map_gen_post cbor_nondet_match cbor_nondet_map_entry_match a va pv vv None);
      false
    }
  }
}

#pop-options

(* ============ Helpers for map_get_multiple ============ *)

noextract [@@noextract_to "krml"]
let set_snd_None_nondet
  (t1 t2: Type)
  (x: (t1 & option t2))
: Tot (t1 & option t2)
= (fst x, None)

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

let list_memP_map_intro_forall_nondet
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

ghost fn lemma_trade_ab_cd_e_nondet
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

ghost fn trade_prod_cancel_hyp_r_concl_l_nondet
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

ghost fn trade_prod_cancel_hyp_r_concl_r_nondet
  (#a b #c #d #e: slprop)
requires
  Trade.trade (a ** b) c ** Trade.trade d (e ** b)
ensures
  Trade.trade (a ** d) (c ** e)
{
  slprop_equivs ();
  rewrite Trade.trade d (e ** b) as Trade.trade d (b ** e);
  trade_prod_cancel_hyp_r_concl_l_nondet b
}

ghost fn trade_prod_cancel_concl_r_hyp_l_nondet
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (c ** d) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (c ** d) e as Trade.trade (d ** c) e;
  trade_prod_cancel_hyp_r_concl_r_nondet c;
  rewrite Trade.trade (d ** a) (e ** b) as Trade.trade (a ** d) (b ** e)
}

ghost fn trade_prod_cancel_concl_r_hyp_r_nondet
  (#a #b c #d #e: slprop)
requires
  Trade.trade a (b ** c) ** Trade.trade (d ** c) e
ensures
  Trade.trade (a ** d) (b ** e)
{
  slprop_equivs ();
  rewrite Trade.trade (d ** c) e as Trade.trade (c ** d) e;
  trade_prod_cancel_concl_r_hyp_l_nondet c
}

let lemma_seq_assoc_cons_nondet
  (#t: Type)
  (a: Seq.seq t)
  (b: t)
  (c: Seq.seq t)
: Lemma
  (Seq.equal (Seq.append a (Seq.cons b c)) (Seq.append (Seq.append a (Seq.cons b Seq.empty)) c))
= ()

let lemma_seq_assoc_cons_upd_nondet
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

ghost fn lemma_trade_rewrite5_nondet
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

ghost fn cbor_map_get_multiple_entry_match_snd_prop_nondet
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


#push-options "--z3rlimit 128 --print_implicits"

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_map_get_multiple_inner (_: unit) : cbor_map_get_multiple_t #_ cbor_nondet_match
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
    (List.Tot.map (set_snd_None_nondet Spec.cbor Spec.cbor) [])
    (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
  intro
    (Trade.trade
      (PM.seq_list_match
        Seq.empty
        (List.Tot.map (set_snd_None_nondet Spec.cbor Spec.cbor) [])
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
  ) invariant exists* i s' s1 s2 l1 l2 . (
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
      SZ.v i == Seq.length s1
    )
  ) {
    with s1 s2 l1 l2 . assert (
      PM.seq_list_match s1 l1 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
      PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps)
    );
    PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _;
    PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match false ps) _ _;
    PMU.seq_list_match_cons_elim_trade s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps);
    let i = !pi;
    let x = S.op_Array_Access dest i;
    assert (pure (x == Seq.head s2));
    let x' = { x with found = false };
    S.op_Array_Assignment dest i x';
    slprop_equivs ();
    let y' : Ghost.erased (Spec.cbor & option Spec.cbor) = Ghost.hide (set_snd_None_nondet _ _ (List.Tot.hd l2));
    Trade.rewrite_with_trade
      (cbor_map_get_multiple_entry_match cbor_nondet_match false ps (Seq.head s2) (List.Tot.hd l2))
      (cbor_map_get_multiple_entry_match cbor_nondet_match true ps x' y');
    Trade.trans_hyp_l _ _ _ (PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps));
    PMU.seq_list_match_singleton_intro_trade x' (Ghost.reveal y') (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
    Trade.trans_hyp_l _ _ _ (PM.seq_list_match s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match false ps));
    Trade.trans_hyp_r _ _ _ (PM.seq_list_match s v (cbor_map_get_multiple_entry_match cbor_nondet_match false ps));
    trade_assoc_hyp_r2l _ _ _ _;
    PMU.seq_list_match_append_intro_trade (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) s1 l1 _ _;
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
  let iter = cbor_nondet_map_iterator_start_unsafe () map;
  Trade.prod _ (cbor_nondet_match pmap map vmap) _ _;
  let mut piter = iter;
  while (
    let i = !pi;
    let iter = !piter;
    (i <> 0sz && not (cbor_nondet_map_iterator_is_empty () iter))
  ) invariant exists* i iter l s0 l0 pmi . (
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
      (forall x . List.Tot.memP x l0 ==> Spec.cbor_map_get m (fst x) == (match snd x with None -> List.Tot.assoc (fst x) l | Some z -> Some z))
    )
  ) {
    let entry = cbor_nondet_map_iterator_next_unsafe () piter;
    Trade.trans_hyp_l _ (cbor_nondet_map_iterator_match _ _ _) _ _;
    trade_assoc_hyp_l2r _ _ _ _;
    with pentry ventry . assert (cbor_nondet_map_entry_match pentry entry ventry);
    Trade.rewrite_with_trade
      (cbor_nondet_map_entry_match pentry entry ventry)
      (cbor_nondet_match pentry entry.RawType.cbor_map_entry_key (fst ventry) **
        cbor_nondet_match pentry entry.RawType.cbor_map_entry_value (snd ventry)
      );
    Trade.trans_hyp_l _ (cbor_nondet_map_entry_match _ _ _) _ _;
    with s0 l0 . assert (PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
    Seq.append_empty_l s0;
    Trade.rewrite_with_trade
      (cbor_nondet_match pentry entry.RawType.cbor_map_entry_value (snd ventry) ** PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps))
      (cbor_nondet_match pentry entry.RawType.cbor_map_entry_value (snd ventry) ** PM.seq_list_match (Seq.append Seq.empty s0) (List.Tot.append [] l0) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
    let mut pj = 0sz;
    S.pts_to_len dest;
    with iter pmi l . assert (cbor_nondet_map_iterator_match pmi iter l);
    List.Tot.assoc_mem (fst ventry) l;
    while (
      let j = !pj;
      let i = !pi;
      (SZ.lt j (S.len dest) && SZ.gt i 0sz)
    ) invariant exists* i j pvalue s' s1 l1 s2 l2 . (
      pts_to pi i **
      pts_to pj j **
      S.pts_to dest s' **
      cbor_nondet_match pvalue entry.RawType.cbor_map_entry_value (snd ventry) ** 
      PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) **
      Trade.trade
        (cbor_nondet_match pvalue entry.RawType.cbor_map_entry_value (snd ventry) ** 
          PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
        )
        (cbor_nondet_match pentry entry.RawType.cbor_map_entry_value (snd ventry) ** 
          PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
        ) **
      cbor_nondet_match pentry entry.RawType.cbor_map_entry_key (fst ventry) ** 
      pure (
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
      with pvalue . assert (cbor_nondet_match pvalue entry.RawType.cbor_map_entry_value (snd ventry));
      S.pts_to_len dest;
      PM.seq_list_match_length (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _;
      with s1 s2 l1 l2 . assert (PM.seq_list_match (Seq.append s1 s2) (List.Tot.append l1 l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
      List.Tot.append_length l1 l2;
      PMU.seq_list_match_append_elim_trade (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) _ _ _ _;
      PMU.seq_list_match_cons_elim_trade s2 l2 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
      let j = !pj;
      pj := SZ.add j 1sz;
      let dest_entry = S.op_Array_Access dest j;
      Trade.rewrite_with_trade
        (cbor_map_get_multiple_entry_match cbor_nondet_match true ps (Seq.head s2) (List.Tot.hd l2))
        (cbor_nondet_match ps dest_entry.key (fst (List.Tot.hd l2)) **
          cbor_map_get_multiple_entry_match_snd cbor_nondet_match true dest_entry (snd (List.Tot.hd l2)));
      cbor_map_get_multiple_entry_match_snd_prop_nondet cbor_nondet_match dest_entry (snd (List.Tot.hd l2));
      Trade.elim_hyp_r _ (cbor_map_get_multiple_entry_match_snd cbor_nondet_match true dest_entry (snd (List.Tot.hd l2))) _;
      if (cbor_nondet_equal dest_entry.key entry.RawType.cbor_map_entry_key) {
        let pvalue' = share_gather_trade (cbor_nondet_share ()) (cbor_nondet_gather ()) entry.RawType.cbor_map_entry_value;
        let entry_value = cbor_nondet_reset_perm () entry.RawType.cbor_map_entry_value 1.0R;
        Trade.trans_hyp_r _ (cbor_nondet_match 1.0R entry_value _) _ _;
        let dest_entry' = { dest_entry with found = true; value = entry_value };
        S.op_Array_Assignment dest j dest_entry';
        Trade.rewrite_with_trade
          (cbor_nondet_match ps dest_entry.key (fst (List.Tot.hd l2)) **
            cbor_nondet_match 1.0R entry_value (snd ventry)
          )
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps dest_entry' (fst (List.Tot.hd l2), Some (snd ventry)));
        PMU.seq_list_match_cons_intro_trade _ _ (Seq.tail s2) (List.Tot.tl l2) (cbor_map_get_multiple_entry_match cbor_nondet_match true ps);
        PMU.seq_list_match_append_intro_trade (cbor_map_get_multiple_entry_match cbor_nondet_match true ps) s1 l1 _ _;
        lemma_seq_assoc_cons_nondet s1 dest_entry' (Seq.tail s2);
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
        trade_prod_cancel_hyp_r_concl_r_nondet (cbor_nondet_match 1.0R _ _);
        trade_prod_cancel_concl_r_hyp_l_nondet (cbor_map_get_multiple_entry_match cbor_nondet_match
          true
          ps
          (Seq.Properties.head s2)
          (List.Tot.Base.hd l2));
        trade_prod_cancel_concl_r_hyp_r_nondet (Pulse.Lib.SeqMatch.seq_list_match s2
          l2
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        Trade.trans _ (cbor_nondet_match pvalue _ _ ** _) _;
        Trade.trans_concl_r _ _ (Pulse.Lib.SeqMatch.seq_list_match (Seq.Base.cons dest_entry'
              (Seq.Properties.tail s2))
          ((fst (List.Tot.Base.hd l2), Some (snd ventry)) :: List.Tot.Base.tl l2)
          (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)) _;
        lemma_trade_rewrite5_nondet _ _ _ _ _;
        Trade.trans_hyp_r _ _ _
          (cbor_nondet_match pentry entry.RawType.cbor_map_entry_value (snd ventry) ** 
            PM.seq_list_match s0 l0 (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        let lx = Ghost.hide [(fst (List.Tot.Base.hd l2), Some (snd ventry))];
        with s' . assert (S.pts_to dest s');
        with s1' s2' l1' l2' . assert (Pulse.Lib.SeqMatch.seq_list_match (Seq.append s1' s2') (List.Tot.append l1' l2') (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
        lemma_seq_assoc_cons_upd_nondet s1 s2 dest_entry';
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
        if (not dest_entry.found) {
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
    with gi . assert (pts_to pi gi);
    lemma_trade_ab_cd_e_nondet _ _ _ _ _ _ _;
    Trade.elim_hyp_l _ _ _;
    List.Tot.map_append snd l1 l2;
    List.Tot.append_count (List.Tot.map snd l1) (List.Tot.map snd l2) None;
    List.Tot.append_memP_forall l1 l2;
    List.Tot.mem_count (List.Tot.map snd l2) None;
    List.Tot.mem_memP None (List.Tot.map snd l2);
    list_memP_map_intro_forall_nondet snd l2;
    assert (pure (forall x . (List.Tot.memP x l2 /\ SZ.v gi == 0) ==> Some? (snd x)));
    List.Tot.append_length l1 l2;
    List.Tot.append_l_nil l1;
    with _s1 _s2 _l1 _l2 . assert (Pulse.Lib.SeqMatch.seq_list_match (Seq.Base.append _s1 _s2)
      (_l1 @ _l2)
      (cbor_map_get_multiple_entry_match cbor_nondet_match true ps)
      );
    with s0' . assert (pts_to dest s0');
    rewrite each (Seq.Base.append _s1 _s2) as s0';
    ()
  };
  Trade.elim_hyp_l _ _ _;
  with s' l' . assert (PM.seq_list_match s' l' (cbor_map_get_multiple_entry_match cbor_nondet_match true ps));
  List.Tot.mem_count (List.Tot.map snd l') None;
  List.Tot.mem_memP None (List.Tot.map snd l');
  list_memP_map_intro_forall_nondet snd l';
  ()
}

#pop-options

