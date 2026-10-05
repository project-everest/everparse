module EverParse3d.Lowstar.SupportBuffer
open Pulse.Lib.Pervasives
#lang-pulse

module P = EverParse3d.Lowstar.Public
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64

let input_buffer = Pulse.Lib.ArrayPtr.ptr FStar.UInt8.t

fn default_error_handler
  (typename_s fieldname reason: string)
  (error_code: U64.t) (context: R.ref P.error_frame)
  (input: input_buffer) (start_pos: U64.t)
  (#frame: Ghost.erased P.error_frame)
requires R.pts_to context (Ghost.reveal frame)
returns _: unit
ensures R.pts_to context
  (if (Ghost.reveal frame).P.filled then Ghost.reveal frame else
    { P.filled = true; P.start_pos = start_pos; P.typename_s = typename_s;
      P.fieldname = fieldname; P.reason = reason; P.error_code = error_code })
{
  P.record_error typename_s fieldname reason error_code context start_pos
}
