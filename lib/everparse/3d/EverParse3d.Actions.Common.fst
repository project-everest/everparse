module EverParse3d.Actions.Common
open Pulse.Lib.Pervasives
module I = EverParse3d.InputStream.Base
module AppCtxt = EverParse3d.AppCtxt
open FStar.FunctionalExtensionality
module U8 = FStar.UInt8
module F = FStar.FunctionalExtensionality
module U64 = FStar.UInt64
module SZ = FStar.SizeT
  
(* An attribute to control partial evaluation of backend definitions.
   Distinct from EverParse3d.Interpreter.specialize so that backend modules,
   which cannot depend on the interpreter, can still be unfolded by it. *)
let specialize_backend = ()

let app_ctxt = AppCtxt.app_ctxt

let error_handler
    {| inst: I.input_stream_inst 'base_t 'len_t 'pos_t  |}
= 
    typename:string ->
    fieldname:string ->
    error_reason:string ->
    error_code:U8.t ->
    ctxt: app_ctxt ->
    sl_base: 'base_t ->
    sl_len: 'len_t ->
    sl_pos: 'pos_t ->
    contents_sl: Ghost.erased (Seq.seq U8.t) ->
    v_sl: Ghost.erased (Seq.seq U8.t) ->
    stt unit
      (requires exists* v_ctxt .
        I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
	pts_to ctxt v_ctxt
      )
      (ensures fun _ -> exists* v_ctxt' .
	I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
	pts_to ctxt v_ctxt'
      )

(*
// The C macro used as the error handler when 3d is invoked with
// `--use_error_handler_macro`. It lives here (rather than in
// EverParse3d.Actions.Base) so that it is also reachable from
// EverParse3d.ProbeActions, which must select between the dynamic
// error-handler callback and this macro just like the validators do.
[@@CMacro]
assume val error_handler_macro: error_handler
