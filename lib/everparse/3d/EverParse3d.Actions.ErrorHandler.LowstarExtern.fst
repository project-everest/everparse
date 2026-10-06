module EverParse3d.Actions.ErrorHandler.LowstarExtern
open Pulse.Lib.Pervasives
#lang-pulse

module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module I = EverParse3d.InputStream.Base
module B = EverParse3d.InputStream.LowstarExtern.Types
module AppCtxt = EverParse3d.AppCtxt
module E = EverParse3d.Lowstar.ErrorCode

let error_handler =
  typename:string ->
  fieldname:string ->
  error_reason:string ->
  error_code:U64.t ->
  ctxt:AppCtxt.app_ctxt ->
  input:B.base_t ->
  start_pos:U64.t ->
  stt unit
    (exists* v. R.pts_to ctxt v)
    (fun _ -> exists* v'. R.pts_to ctxt v')

inline_for_extraction noextract
fn error_handler_arrow_of (h: error_handler)
  : I.error_handler_arrow B.base_t B.len_t B.pos_t
  = (typename: _) (fieldname: _) (reason: _) (code: _)
    (ctxt: _) (base: _) (len: _) (pos: _) (start: _)
{
  h typename fieldname reason (E.legacy_kind code) ctxt base start
}
