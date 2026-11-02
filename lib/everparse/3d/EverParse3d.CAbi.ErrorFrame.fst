module EverParse3d.CAbi.ErrorFrame
open Pulse.Lib.Pervasives
#lang-pulse

(* The error frame filled by the default error handler of the generated
   wrappers, shared by the `--api lowstar` and `--api pulse` runtimes. *)

module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module B = EverParse3d.CAbi.Boolean

[@@FStar.Attributes.rename_let "EVERPARSE_ERROR_FRAME"]
noeq type error_frame = {
  filled: B.t;
  start_pos: U64.t;
  typename_s: string;
  fieldname: string;
  reason: string;
  error_code: U64.t;
}

noextract inline_for_extraction
fn record_error
  (typename_s fieldname reason: string)
  (error_code: U64.t) (context: R.ref error_frame) (start_pos: U64.t)
  (#frame: Ghost.erased error_frame)
requires R.pts_to context (Ghost.reveal frame)
returns _: unit
ensures R.pts_to context
  (if B.to_bool (Ghost.reveal frame).filled then Ghost.reveal frame else
    { filled = B.of_bool true; start_pos = start_pos; typename_s = typename_s;
      fieldname = fieldname; reason = reason; error_code = error_code })
{
  let frame = !context;
  if (not (B.to_bool frame.filled)) {
    context := { filled = B.of_bool true; start_pos = start_pos; typename_s = typename_s;
      fieldname = fieldname; reason = reason; error_code = error_code };
  }
}
