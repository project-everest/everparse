module Parquet.Pulse.Jump
#lang-pulse
open Pulse.Lib.Pervasives
include LowParse.Pulse.Base
include Parquet.Spec.Jump

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module V = Pulse.Lib.Vec
module PV = Parquet.Pulse.Vec

inline_for_extraction
fn impl_pred_jump_with_offset_and_size_then_parse
  (#t: Type0)
  (offset: SZ.t)
  (size: SZ.t)
  (#k: Ghost.erased parser_kind)
  (#p: Ghost.erased (tot_parser k t))
  (s: Ghost.erased (tot_serializer p))
  (input: S.slice byte)
  (#pm: perm)
  (v: Ghost.erased bytes)
requires
  pts_to input #pm v ** pure (
    SZ.v offset + SZ.v size <= Seq.length v /\
    pred_jump_with_offset_and_size_then_parse (SZ.v offset) (SZ.v size) p v
  )
returns res: S.slice byte
ensures exists* v' .
  pts_to_serialized (serializer_of_tot_serializer s) res #pm v' **
  Trade.trade
    (pts_to_serialized (serializer_of_tot_serializer s) res #pm v')
    (pts_to input #pm v) **
  pure (
    SZ.v offset + SZ.v size <= Seq.length v /\
    Seq.slice v (SZ.v offset) (SZ.v offset + SZ.v size) == bare_serialize (serializer_of_tot_serializer s) v'
  )
{
  let (s0, s12) = S.split_trade input offset;
  Trade.elim_hyp_l _ _ _;
  let (s1, s2) = S.split_trade s12 size;
  Trade.elim_hyp_r _ _ _;
  Trade.trans _ _ (pts_to input #pm v);
  with v1 . assert (pts_to s1 #pm v1);
  let v' = Ghost.hide (fst (Some?.v (Ghost.reveal (parse (parser_of_tot_parser p) v1))));
  serializer_correct_implies_complete (parser_of_tot_parser p) (serializer_of_tot_serializer s);
  pts_to_serialized_intro_trade (serializer_of_tot_serializer s) s1 v';
  Trade.trans _ _ (pts_to input #pm v);
  s1
}

inline_for_extraction
fn validate_jump_with_offset_and_size_then_parse
  (precond: slprop)
  (#t: Type0)
  (offset: SZ.t)
  (size: SZ.t)
  (#k: Ghost.erased parser_kind)
  (#p: Ghost.erased (tot_parser k t))
  (u: validator_gen precond (parser_of_tot_parser p))
  (input: S.slice byte)
  (#pm: perm)
  (v: Ghost.erased bytes)
requires
  precond **
  pts_to input #pm v
returns res: bool
ensures 
  precond **
  pts_to input #pm v ** pure (
    res == pred_jump_with_offset_and_size_then_parse (SZ.v offset) (SZ.v size) p v
  )
{
  S.pts_to_len input;
  if (SZ.gt offset (S.len input)) {
    false
  } else if (SZ.gt size (SZ.sub (S.len input) offset)) {
    false
  } else {
    let (s1, s2) = S.split_trade input (SZ.add offset size);
    let mut poffset = offset;
    let is_valid = u s1 poffset;
    let off = !poffset;
    Trade.elim _ _;
    (SZ.eq off (SZ.add offset size) && is_valid)
  }
}

open LowParse.Pulse.Combinators
open LowParse.Pulse.SeqBytes

inline_for_extraction
fn impl_pred_jump_with_offset_and_size_then_parse_pts_to_serialized_filter
  (#t: Type0)
  (offset: SZ.t)
  (size: SZ.t)
  (phi: bytes -> GTot bool)
  (#k: Ghost.erased parser_kind)
  (#p: Ghost.erased (tot_parser k t))
  (s: Ghost.erased (tot_serializer p))
  (input: S.slice byte)
  (#pm: perm)
  (v: Ghost.erased bytes { phi v })
requires
  pts_to_serialized (serialize_filter serialize_seq_all_bytes phi) input #pm v ** pure (
    (phi v ==> pred_jump_with_offset_and_size_then_parse (SZ.v offset) (SZ.v size) p v)
  )
returns res: S.slice byte
ensures exists* v' .
  pts_to_serialized (serializer_of_tot_serializer s) res #pm v' **
  Trade.trade
    (pts_to_serialized (serializer_of_tot_serializer s) res #pm v')
    (pts_to_serialized (serialize_filter serialize_seq_all_bytes phi) input #pm v) **
  pure (
    SZ.v offset + SZ.v size <= Seq.length v /\
    Seq.slice v (SZ.v offset) (SZ.v offset + SZ.v size) == bare_serialize (serializer_of_tot_serializer s) v'
  )
{
  pts_to_serialized_filter_elim_trade serialize_seq_all_bytes phi input;
  pts_to_serialized_elim_trade serialize_seq_all_bytes input;
  Trade.trans _ _ (pts_to_serialized (serialize_filter serialize_seq_all_bytes phi) input #pm v);
  let res = impl_pred_jump_with_offset_and_size_then_parse offset size s input v;
  Trade.trans _ _ (pts_to_serialized (serialize_filter serialize_seq_all_bytes phi) input #pm v);
  res
}

module Rel = CDDL.Pulse.Types.Base
module I64 = FStar.Int64
module SM = Pulse.Lib.SeqMatch.Util

inline_for_extraction
let impl_fst_f
  (#implt: Type0)
  (#spect: Type0)
  (f: (spect -> (int & int)))
  (r: Rel.rel implt spect)
=
    (impl: implt) ->
    (spec: Ghost.erased spect) ->
    stt I64.t
      (r impl spec)
      (fun res -> r impl spec ** pure ((I64.v res <: int) == fst (Ghost.reveal f spec)))

inline_for_extraction
let impl_snd_f
  (#implt: Type0)
  (#spect: Type0)
  (f: (spect -> (int & int)))
  (r: Rel.rel implt spect)
=
    (impl: implt) ->
    (spec: Ghost.erased spect) ->
    stt I64.t
      (r impl spec)
      (fun res -> r impl spec ** pure ((I64.v res <: int) == snd (Ghost.reveal f spec)))

inline_for_extraction
fn impl_offsets_and_sizes_are_contiguous
  (#implt: Type0)
  (#spect: Type0)
  (f: Ghost.erased (spect -> (int & int)))
  (r: Rel.rel implt spect)
  (implf_fst: impl_fst_f f r)
  (implf_snd: impl_snd_f f r)
  (impl: PV.vec implt)
  (#spec: Ghost.erased (list spect))
requires
  PV.rel_vec_of_list r impl spec
returns res: bool
ensures
  PV.rel_vec_of_list r impl spec **
  pure (res == offsets_and_sizes_are_contiguous (List.Tot.map f spec))
{
  unfold (PV.rel_vec_of_list r impl spec);
  with s . assert (pts_to impl.data s);
  SM.seq_list_match_length r s spec;
  V.pts_to_len impl.data;
  if (SZ.lt impl.len 2sz) {
    fold (PV.rel_vec_of_list r impl spec);
    true
  } else {
    SM.seq_list_match_cons_elim_trade _ _ _;
    let mut pl = V.op_Array_Access impl.data 0sz;
    let mut pres = true;
    let mut pi = 1sz;
    while (
      let res = !pres;
      if (res) {
        SM.seq_list_match_length r _ _;
        let i = !pi;
        SZ.lt i impl.len
      } else {
        false
      }
    ) invariant b . exists* impll specl sr specr res i . (
      pts_to impl.data s **
      pts_to pl impll **
      r impll specl **
      SM.seq_list_match sr specr r **
      Trade.trade
        (r impll specl ** SM.seq_list_match sr specr r)
        (SM.seq_list_match s spec r) **
      pts_to pres res **
      pts_to pi i **
      pure (
        SZ.v i <= Seq.length s /\
        sr == Seq.slice s (SZ.v i) (Seq.length s) /\
        offsets_and_sizes_are_contiguous (List.Tot.map f spec) == (res && offsets_and_sizes_are_contiguous (List.Tot.map f (specl :: specr))) /\
        b == (res && Cons? specr)
      )
    ) {
      let impl1 = !pl;
      with spec1 . assert (r impl1 spec1);
      let off1 = implf_fst impl1 _;
      if (I64.lt off1 0L) {
        pres := false
      } else {
        let sz1 = implf_snd impl1 _;
        if (I64.lt sz1 0L) {
          pres := false
        } else {
          SM.seq_list_match_length r _ _;
          SM.seq_list_match_cons_elim_trade _ _ _;
          let i = !pi;
          with gimpl2 spec2 . assert (r impl1 spec1 ** r gimpl2 spec2);
          let impl2 = V.op_Array_Access impl.data i;
          rewrite each gimpl2 as impl2;
          let off2 = implf_fst impl2 _;
          if (I64.lt off2 off1) {
            Trade.elim (r impl2 _ ** _) _;
            pres := false
          } else if (sz1 <> I64.sub off2 off1) {
            Trade.elim (r impl2 _ ** _) _;
            pres := false
          } else {
            Trade.elim_hyp_l (r impl1 _) _ _;
            Trade.trans _ _ (SM.seq_list_match s spec r);
            pl := impl2;
            pi := SZ.add i 1sz;
          }
        }
      }
    };
    Trade.elim _ _;
    fold (PV.rel_vec_of_list r impl spec);
    !pres
  }
}

inline_for_extraction
fn impl_offsets_and_sizes_are_sorted
  (#implt: Type0)
  (#spect: Type0)
  (f: Ghost.erased (spect -> (int & int)))
  (r: Rel.rel implt spect)
  (implf_fst: impl_fst_f f r)
  (implf_snd: impl_snd_f f r)
  (impl: PV.vec implt)
  (#spec: Ghost.erased (list spect))
requires
  PV.rel_vec_of_list r impl spec
returns res: bool
ensures
  PV.rel_vec_of_list r impl spec **
  pure (res == offsets_and_sizes_are_sorted (List.Tot.map f spec))
{
  unfold (PV.rel_vec_of_list r impl spec);
  with s . assert (pts_to impl.data s);
  SM.seq_list_match_length r s spec;
  V.pts_to_len impl.data;
  if (SZ.lt impl.len 2sz) {
    fold (PV.rel_vec_of_list r impl spec);
    true
  } else {
    SM.seq_list_match_cons_elim_trade _ _ _;
    let mut pl = V.op_Array_Access impl.data 0sz;
    let mut pres = true;
    let mut pi = 1sz;
    while (
      let res = !pres;
      if (res) {
        SM.seq_list_match_length r _ _;
        let i = !pi;
        SZ.lt i impl.len
      } else {
        false
      }
    ) invariant b . exists* impll specl sr specr res i . (
      pts_to impl.data s **
      pts_to pl impll **
      r impll specl **
      SM.seq_list_match sr specr r **
      Trade.trade
        (r impll specl ** SM.seq_list_match sr specr r)
        (SM.seq_list_match s spec r) **
      pts_to pres res **
      pts_to pi i **
      pure (
        SZ.v i <= Seq.length s /\
        sr == Seq.slice s (SZ.v i) (Seq.length s) /\
        offsets_and_sizes_are_sorted (List.Tot.map f spec) == (res && offsets_and_sizes_are_sorted (List.Tot.map f (specl :: specr))) /\
        b == (res && Cons? specr)
      )
    ) {
      let impl1 = !pl;
      with spec1 . assert (r impl1 spec1);
      let off1 = implf_fst impl1 _;
      if (I64.lt off1 0L) {
        pres := false
      } else {
        let sz1 = implf_snd impl1 _;
        if (I64.lt sz1 0L) {
          pres := false
        } else {
          SM.seq_list_match_length r _ _;
          SM.seq_list_match_cons_elim_trade _ _ _;
          let i = !pi;
          with gimpl2 spec2 . assert (r impl1 spec1 ** r gimpl2 spec2);
          let impl2 = V.op_Array_Access impl.data i;
          rewrite each gimpl2 as impl2;
          let off2 = implf_fst impl2 _;
          if (I64.lt off2 off1) {
            Trade.elim (r impl2 _ ** _) _;
            pres := false
          } else if (I64.gt sz1 (I64.sub off2 off1)) {
            Trade.elim (r impl2 _ ** _) _;
            pres := false
          } else {
            Trade.elim_hyp_l (r impl1 _) _ _;
            Trade.trans _ _ (SM.seq_list_match s spec r);
            pl := impl2;
            pi := SZ.add i 1sz;
          }
        }
      }
    };
    Trade.elim _ _;
    fold (PV.rel_vec_of_list r impl spec);
    !pres
  }
}
