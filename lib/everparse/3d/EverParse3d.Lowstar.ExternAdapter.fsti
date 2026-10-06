module EverParse3d.Lowstar.ExternAdapter
open Pulse.Lib.Pervasives
open EverParse3d.State

module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.LowstarExtern
module P = EverParse3d.Prelude
module LP = EverParse3d.Lowstar.ExternAdapter.Spec
module I = EverParse3d.InputStream.Base
module E = EverParse3d.Lowstar.ErrorCode
module EC = EverParse3d.ErrorCode
module EH = EverParse3d.Actions.ErrorHandler.LowstarExtern
module C = EverParse3d.AppCtxt
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// The entire public postcondition is transparent to callers, including the
// exact physical suffix on consuming failure and unchanged no-read input.
noextract
let result_prop
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t) (has_action consumes: bool)
  (start: U64.t) (input: Seq.seq U8.t)
  (actual: U64.t) (rest: Seq.seq U8.t) (result: U64.t)
  : Tot prop =
  exists (status: U8.t) (position: U64.t { U64.v position < E.position_limit }).
    result == E.pack status position /\
    (status == EC.validator_error_action_failed ==> has_action) /\
    (EC.is_validation_error status ==> None? (LP.parse p input)) /\
    U64.v start <= U64.v position /\
    U64.v position <= U64.v start + Seq.length input /\
    I.seq_is_suffix_of rest input /\
    U64.v actual + Seq.length rest == U64.v start + Seq.length input /\
    (consumes ==> position == actual) /\
    (not consumes ==> actual == start /\ Seq.equal rest input) /\
    (not consumes /\ status <> EC.validator_success ==> position == start) /\
    (status == EC.validator_success ==>
      Some? (LP.parse p input) /\
      U64.v position == U64.v start + snd (Some?.v (LP.parse p input)) /\
      (consumes ==> Seq.equal rest
        (Seq.slice input (snd (Some?.v (LP.parse p input))) (Seq.length input))))

inline_for_extraction noextract
let validator
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser #nz #wk k t)
  (d: state_dict) (has_action consumes use_error_handler: bool)
  : Type0 =
  (ctxt: C.app_ctxt) ->
  (handler: (if use_error_handler then EH.error_handler else unit)) ->
  (input: B.base_t) ->
  (start: U64.t) ->
  (extra: forevery_values d) ->
  (contents: Ghost.erased (Seq.seq U8.t)) ->
  (remaining: Ghost.erased (Seq.seq U8.t)) ->
  stt U64.t
    (exists* v_ctxt.
      R.pts_to ctxt v_ctxt ** B.public_pts_to input start contents remaining **
      forevery_state d extra)
    (fun result -> exists* v_ctxt' actual rest extra'.
      R.pts_to ctxt v_ctxt' ** B.public_pts_to input actual contents rest **
      forevery_state d extra' **
      pure (U64.v actual < E.position_limit /\
        (not has_action ==> extra' == extra) /\
        result_prop p has_action consumes start remaining actual rest result))

inline_for_extraction noextract
val adapt_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (#p: P.parser k t) (#d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_extern p d has_action use_error_handler)
  : validator p d has_action true use_error_handler

inline_for_extraction noextract
val adapt_no_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (#p: P.parser k t) (#d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_no_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_extern p d has_action use_error_handler)
  : validator p d has_action false use_error_handler

module IT = EverParse3d.Interpreter

[@@noextract_to "krml"; EverParse3d.Actions.Common.specialize_backend]
inline_for_extraction noextract
let validator_of
  (d: state_dict) (eh: bool)
  #ha #ar #nz #wk (#k: P.parser_kind nz wk)
  (t: IT.typ B.base_t B.len_t B.pos_t B.input_stream_extern d eh k ha ar)
  = validator (IT.as_parser t) d ha (not ar) eh

inline_for_extraction noextract
let adapt
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (#p: P.parser k t) (#d: state_dict) (#ha: bool) (#eh: bool)
  (ar: bool)
  (worker: A.validate_with_action_t #B.base_t #B.len_t #B.pos_t
    #B.input_stream_extern p d ha ar eh)
  : validator p d ha (not ar) eh
  = if ar
    then adapt_no_read #nz #wk #k #t #p #d #ha #eh worker
    else adapt_read #nz #wk #k #t #p #d #ha #eh worker
