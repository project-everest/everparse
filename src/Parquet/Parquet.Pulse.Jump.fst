module Parquet.Pulse.Jump
#lang-pulse
open Pulse.Lib.Pervasives
include LowParse.Pulse.Base
include Parquet.Spec.Jump

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util

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
