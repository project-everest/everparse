module CDDL.Pulse.Serialize.MapGroup
#lang-pulse
include CDDL.Pulse.Serialize.Base
include CDDL.Pulse.Parse.MapGroup
open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest
module Gen = CDDL.Pulse.Serialize.Gen.MapGroup
module GenBase = CDDL.Pulse.Serialize.Gen.MapGroup.Base

(* Bridge lemma: local pre implies Gen pre *)
let impl_serialize_map_group_pre_to_gen
  (count: U64.t) (size: SZ.t) (l: cbor_map) (w: Seq.seq U8.t)
: Lemma
  (requires impl_serialize_map_group_pre count size l w)
  (ensures Gen.impl_serialize_map_group_pre Gen.cbor_det_parse_map count size l w)
  [SMTPat (impl_serialize_map_group_pre count size l w)]
= Cbor.cbor_det_parse_map_equiv (cbor_map_length l) w l (SZ.v size)

(* Bridge lemma: Gen pre implies local pre *)
let impl_serialize_map_group_pre_from_gen
  (count: U64.t) (size: SZ.t) (l: cbor_map) (w: Seq.seq U8.t)
: Lemma
  (requires Gen.impl_serialize_map_group_pre Gen.cbor_det_parse_map count size l w)
  (ensures impl_serialize_map_group_pre count size l w)
  [SMTPat (Gen.impl_serialize_map_group_pre Gen.cbor_det_parse_map count size l w)]
= Cbor.cbor_det_parse_map_equiv (U64.v count) w l (SZ.v size)

let impl_serialize_map_group_valid_equiv
  (l: cbor_map)
  (#t: det_map_group)
  (#fp: map_constraint)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (v: tgt)
  (len: nat)
: Lemma
  (impl_serialize_map_group_valid l s v len <==>
   Gen.impl_serialize_map_group_valid Gen.cbor_det_max_length l s v len)
= if s.mg_serializable v &&
     cbor_map_disjoint_tot l (s.mg_serializer v) &&
     FStar.UInt.fits (cbor_map_length l + cbor_map_length (s.mg_serializer v)) 64
  then
    GenBase.cbor_map_det_max_length_eq (cbor_map_union l (s.mg_serializer v))

let impl_serialize_map_group_valid_gen_iff_not_invalid
  (l: cbor_map)
  (#t: det_map_group)
  (#fp: map_constraint)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (v: tgt)
  (len: nat)
: Lemma
  (Gen.impl_serialize_map_group_valid Gen.cbor_det_max_length l s v len ==
   not (Gen.impl_serialize_map_group_invalid Gen.cbor_det_min_length l s v len))
= if s.mg_serializable v &&
     cbor_map_disjoint_tot l (s.mg_serializer v) &&
     FStar.UInt.fits (cbor_map_length l + cbor_map_length (s.mg_serializer v)) 64
  then begin
    let m = cbor_map_union l (s.mg_serializer v) in
    GenBase.cbor_map_det_min_length_eq m;
    GenBase.cbor_map_det_max_length_eq m
  end

(* Bridge lemma: Gen post implies local post *)
let impl_serialize_map_group_post_gen_to_local
  (#t: det_map_group)
  (#fp: map_constraint)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (count': U64.t) (size': SZ.t)
  (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t) (res: bool)
: Lemma
  (requires Gen.impl_serialize_map_group_post Gen.cbor_det_parse_map Gen.cbor_det_min_length Gen.cbor_det_max_length count' size' l s v w res)
  (ensures impl_serialize_map_group_post count' size' l s v w res)
  [SMTPat (Gen.impl_serialize_map_group_post Gen.cbor_det_parse_map Gen.cbor_det_min_length Gen.cbor_det_max_length count' size' l s v w res)]
= impl_serialize_map_group_valid_equiv l s v (Seq.length w);
  impl_serialize_map_group_valid_gen_iff_not_invalid l s v (Seq.length w)

(* Bridge lemma: local post implies Gen post *)
let impl_serialize_map_group_post_local_to_gen
  (#t: det_map_group)
  (#fp: map_constraint)
  (#tgt: Type0)
  (#inj: bool)
  (s: mg_spec t fp tgt inj)
  (count': U64.t) (size': SZ.t)
  (l: cbor_map) (v: tgt)
  (w: Seq.seq U8.t) (res: bool)
: Lemma
  (requires impl_serialize_map_group_post count' size' l s v w res)
  (ensures Gen.impl_serialize_map_group_post Gen.cbor_det_parse_map Gen.cbor_det_min_length Gen.cbor_det_max_length count' size' l s v w res)
  [SMTPat (impl_serialize_map_group_post count' size' l s v w res)]
= impl_serialize_map_group_valid_equiv l s v (Seq.length w);
  impl_serialize_map_group_valid_gen_iff_not_invalid l s v (Seq.length w)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_intro'
    (#[@@@erasable] t: Ghost.erased det_map_group)
    (#[@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable] s: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable] r: rel impl_tgt tgt)
    (i: Gen.impl_serialize_map_group Gen.cbor_det_parse_map Gen.cbor_det_min_length Gen.cbor_det_max_length s r)
: impl_serialize_map_group s r
=
  (c: _)
  (#v: _)
  (out: _)
  (out_count: _)
  (out_size: _)
  (l: _)
{
  let res = i c out out_count out_size l;
  res
}

let impl_serialize_map_group_intro = impl_serialize_map_group_intro'

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_group_elim'
    (#[@@@erasable] t: Ghost.erased det_map_group)
    (#[@@@erasable] fp: Ghost.erased map_constraint)
    (#[@@@erasable]tgt: Type0)
    (#[@@@erasable] inj: Ghost.erased bool)
    (#[@@@erasable] s: Ghost.erased (mg_spec t fp tgt inj))
    (#impl_tgt: Type0)
    (#[@@@erasable] r: rel impl_tgt tgt)
    (i: impl_serialize_map_group s r)
: Gen.impl_serialize_map_group Gen.cbor_det_parse_map Gen.cbor_det_min_length Gen.cbor_det_max_length s r
=
  (c: _)
  (#v: _)
  (out: _)
  (out_count: _)
  (out_size: _)
  (l: _)
{
  let res = i c out out_count out_size l;
  res
}

let impl_serialize_map_group_elim = impl_serialize_map_group_elim'

(* Bridge lemma: Gen insert pre implies local insert pre *)
let cbor_serialize_map_insert_pre_gen_to_local
  (m: cbor_map)
  (off2: SZ.t)
  (key: cbor)
  (off3: SZ.t)
  (value: cbor)
  (v: Seq.seq U8.t)
: Lemma
  (requires Gen.cbor_serialize_map_insert_pre Gen.cbor_det_parse_map Gen.cbor_det_parse m off2 key off3 value v)
  (ensures cbor_det_serialize_map_insert_pre m off2 key off3 value v)
  [SMTPat (Gen.cbor_serialize_map_insert_pre Gen.cbor_det_parse_map Gen.cbor_det_parse m off2 key off3 value v)]
= Cbor.cbor_det_parse_map_equiv (cbor_map_length m) (Seq.slice v 0 (SZ.v off2)) m (SZ.v off2);
  Gen.cbor_det_parse_equiv (Seq.slice v (SZ.v off2) (SZ.v off3)) key (SZ.v off3 - SZ.v off2);
  Gen.cbor_det_parse_equiv (Seq.slice v (SZ.v off3) (Seq.length v)) value (Seq.length v - SZ.v off3)

(* Bridge lemma: local insert post implies Gen insert post *)
let cbor_serialize_map_insert_post_local_to_gen
  (m: cbor_map)
  (key: cbor)
  (value: cbor)
  (res: bool)
  (v': Seq.seq U8.t)
: Lemma
  (requires cbor_det_serialize_map_insert_post m key value res v')
  (ensures Gen.cbor_serialize_map_insert_post Gen.cbor_det_parse_map m key value res v')
  [SMTPat (cbor_det_serialize_map_insert_post m key value res v')]
= if res then begin
    let m' = cbor_map_union m (cbor_map_singleton key value) in
    Cbor.cbor_det_parse_map_equiv (cbor_map_length m') v' m' (Seq.length v')
  end

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_serialize_map_insert_elim'
  (f: cbor_det_serialize_map_insert_t)
: Gen.cbor_serialize_map_insert_t Gen.cbor_det_parse_map Gen.cbor_det_parse
=
  (out: _)
  (m: _)
  (off2: _)
  (key: _)
  (off3: _)
  (value: _)
{
  let res = f out m off2 key off3 value;
  res
}

let cbor_det_serialize_map_insert_elim f = cbor_det_serialize_map_insert_elim' f

let cbor_det_parse_postcond_some_to_gen
  (v: Seq.seq U8.t) (v': cbor) (vrem: Seq.seq U8.t)
: Lemma
  (requires cbor_det_parse_postcond_some v v' vrem)
  (ensures Gen.cbor_parse_postcond_some Gen.cbor_det_parse v v' vrem)
  [SMTPat (cbor_det_parse_postcond_some v v' vrem)]
= Gen.cbor_det_parse_equiv v v' (Seq.length (Cbor.cbor_det_serialize v'))

inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_det_parse_elim'
  (#cbor_t: Type0)
  (#vmatch: perm -> cbor_t -> cbor -> slprop)
  (f: cbor_det_parse_t vmatch)
: Gen.cbor_parse_t Gen.cbor_det_parse vmatch
=
  (input: _)
  (#pm: _)
  (#v: _)
{
  let res = f input;
  match res {
    None -> {
      unfold (cbor_det_parse_post vmatch input pm v None);
      drop_ (pure (~ (exists v1 v2 . Ghost.reveal v == Cbor.cbor_det_serialize v1 `Seq.append` v2)));
      fold (Gen.cbor_parse_post Gen.cbor_det_parse vmatch input pm v None);
      None #(cbor_t & S.slice U8.t)
    }
    Some pair -> {
      unfold (cbor_det_parse_post vmatch input pm v (Some pair));
      let (c, rem) = pair;
      unfold (cbor_det_parse_post_some vmatch input pm v c rem);
      with v' vrem. _;
      fold (Gen.cbor_parse_post_some Gen.cbor_det_parse vmatch input pm v c rem);
      fold (Gen.cbor_parse_post Gen.cbor_det_parse vmatch input pm v (Some (c, rem)));
      Some (c, rem)
    }
  }
}

let cbor_det_parse_elim f = cbor_det_parse_elim' f

let impl_serialize_map cbor_det_serialize_map i sq =
  impl_serialize_intro (Gen.impl_det_serialize_map cbor_det_serialize_map (impl_serialize_map_group_elim i))

let impl_serialize_map_group_ext i ps' sq =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_ext (impl_serialize_map_group_elim i) ps' sq)

let impl_serialize_map_group_ext' i fp' sq =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_ext' (impl_serialize_map_group_elim i) fp' sq)

let impl_serialize_map_group_nop () =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_nop ())

let impl_serialize_map_group_choice i1 i2 sq =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_choice (impl_serialize_map_group_elim i1) (impl_serialize_map_group_elim i2) sq)

let impl_serialize_map_group_zero_or_one i1 sq =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_zero_or_one (impl_serialize_map_group_elim i1) sq)

let impl_serialize_map_group_either_left i1 i2 =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_either_left (impl_serialize_map_group_elim i1) (impl_serialize_map_group_elim i2))

let impl_serialize_map_group_concat i1 i2 sq =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_group_concat (impl_serialize_map_group_elim i1) (impl_serialize_map_group_elim i2) sq)

let impl_serialize_match_item_for insert ik cut ivalue =
  impl_serialize_map_group_intro (Gen.impl_serialize_match_item_for (cbor_det_serialize_map_insert_elim insert) (impl_serialize_elim ik) cut (impl_serialize_elim ivalue))

let impl_serialize_map_zero_or_more map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather parse mk_map_entry insert key_eq pa1 pa2 va_ex =
  impl_serialize_map_group_intro (Gen.impl_serialize_map_zero_or_more map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather (cbor_det_parse_elim parse) mk_map_entry (cbor_det_serialize_map_insert_elim insert) key_eq (impl_serialize_elim pa1) (impl_serialize_elim pa2) va_ex)
