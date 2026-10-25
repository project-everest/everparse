module EverParse3d.Lowstar.BufferAdapter
friend EverParse3d.Prelude
friend EverParse3d.Actions.Base
open Pulse.Lib.Pervasives
open EverParse3d.State
#lang-pulse

module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.LowstarBuffer
module I = EverParse3d.InputStream.Base
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module E = EverParse3d.Lowstar.ErrorCode
module EC = EverParse3d.ErrorCode
module C = EverParse3d.AppCtxt
module EH = EverParse3d.Actions.ErrorHandler.LowstarBuffer

noextract
let result_prop
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t)
  (has_action consumes: bool)
  (start: U64.t) (input: Seq.seq U8.t) (result: U64.t)
  : Tot prop
  = exists (status: U8.t) (position: U64.t).
      U64.v position < E.position_limit /\
      result == E.pack status position /\
      (status == EC.validator_error_action_failed ==> has_action) /\
      (EC.is_validation_error status ==> None? (LP.parse p input)) /\
      U64.v start <= U64.v position /\
      U64.v position <= U64.v start + Seq.length input /\
      (status == EC.validator_success ==>
        Some? (LP.parse p input) /\
        U64.v position == U64.v start + snd (Some?.v (LP.parse p input))) /\
      (not consumes /\ status <> EC.validator_success ==> position == start)

inline_for_extraction noextract
let validator
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t)
  (d: state_dict) (has_action consumes use_error_handler: bool)
  : Type0
  = (ctxt: C.app_ctxt) ->
    (handler: (if use_error_handler then EH.error_handler else unit)) ->
    (input: B.base_t) ->
    (length: U64.t) ->
    (start: U64.t) ->
    (extra: forevery_values d) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    stt U64.t
      (exists* v_ctxt.
        R.pts_to ctxt v_ctxt ** AP.pts_to input contents **
        forevery_state d extra **
        pure (Seq.length contents == U64.v length /\
              U64.v length < 4294967296 /\
              SZ.fits (U64.v length) /\
              U64.v start <= U64.v length))
      (fun result -> exists* v_ctxt' extra'.
        R.pts_to ctxt v_ctxt' ** AP.pts_to input contents **
        forevery_state d extra' **
        pure (Seq.length contents == U64.v length /\
              U64.v start <= U64.v length /\
              (not has_action ==> extra' == extra) /\
              result_prop p has_action consumes start
                (Seq.slice contents (U64.v start) (U64.v length)) result))

inline_for_extraction noextract
fn adapt_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk)
  (#[@@@erasable] t: Type)
  (#[@@@erasable] p: P.parser #nz #wk k t)
  (#[@@@erasable] d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_buffer p d has_action use_error_handler)
  : validator p d has_action true use_error_handler
  = (ctxt: _) (handler: _) (input: _) (length: _) (start: _)
    (extra: _) (contents: _)
{
  let len = SZ.uint64_to_sizet length;
  let initial = SZ.uint64_to_sizet start;
  let mut cursor = initial;
  let remaining = Ghost.hide (Seq.slice contents (U64.v start) (U64.v length));
  fold (B.stream_pts_to input len cursor contents remaining);
  rewrite (B.stream_pts_to input len cursor contents remaining)
    as (I.pts_to #_ #_ #_ #B.pts_to_inst input len cursor contents remaining);
  let status = worker ctxt handler input len cursor extra contents remaining;
  with rest . assert (I.pts_to #_ #_ #_ #B.pts_to_inst input len cursor contents rest);
  rewrite (I.pts_to #_ #_ #_ #B.pts_to_inst input len cursor contents rest)
    as (B.stream_pts_to input len cursor contents rest);
  unfold (B.stream_pts_to input len cursor contents rest);
  let final = !cursor;
  I.sizet_to_uint64_exact final;
  let position = SZ.sizet_to_uint64 final;
  LP.parser_kind_prop_equiv k p;
  let result = E.pack status position;
  assert (pure (result_prop p has_action true start remaining result));
  result
}

inline_for_extraction noextract
fn adapt_no_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk)
  (#[@@@erasable] t: Type)
  (#[@@@erasable] p: P.parser #nz #wk k t)
  (#[@@@erasable] d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_no_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_buffer p d has_action use_error_handler)
  : validator p d has_action false use_error_handler
  = (ctxt: _) (handler: _) (input: _) (length: _) (start: _)
    (extra: _) (contents: _)
{
  let len = SZ.uint64_to_sizet length;
  let initial = SZ.uint64_to_sizet start;
  let mut cursor = initial;
  let mut lookahead = 0sz;
  let remaining = Ghost.hide (Seq.slice contents (U64.v start) (U64.v length));
  fold (B.stream_pts_to input len cursor contents remaining);
  rewrite (B.stream_pts_to input len cursor contents remaining)
    as (I.pts_to #_ #_ #_ #B.pts_to_inst input len cursor contents remaining);
  let status = worker ctxt handler input len cursor lookahead extra contents remaining (Ghost.hide 0sz);
  let offset = !lookahead;
  LP.parser_kind_prop_equiv k p;
  Seq.lemma_eq_elim (Seq.slice remaining 0 (Seq.length remaining)) remaining;
  I.sizet_to_uint64_exact offset;
  let position = (if status = EC.validator_success
    then U64.add start (SZ.sizet_to_uint64 offset)
    else start);
  rewrite (I.pts_to #_ #_ #_ #B.pts_to_inst input len cursor contents remaining)
    as (B.stream_pts_to input len cursor contents remaining);
  unfold (B.stream_pts_to input len cursor contents remaining);
  let result = E.pack status position;
  assert (pure (result_prop p has_action false start remaining result));
  result
}
