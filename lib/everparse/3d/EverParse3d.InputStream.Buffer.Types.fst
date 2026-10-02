module EverParse3d.InputStream.Buffer.Types
open Pulse.Lib.Pervasives
#lang-pulse

(* The `buffer` backend's stream types and its [input_stream_pts_to] instance.

   Split out of EverParse3d.InputStream.Buffer so that
   EverParse3d.Actions.ErrorHandler.Buffer, which needs them to state the
   backend's error-handler type, can sit *between* this module and the full
   [input_stream_inst] instance -- which in turn has to name that error-handler
   type. EverParse3d.InputStream.Buffer re-exports everything here, so generated
   code still refers to these under that module name. *)

module AP = Pulse.Lib.ArrayPtr
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I = EverParse3d.InputStream.Base

let base_t = AP.ptr U8.t
let len_t = SZ.t
let pos_t = R.ref SZ.t

let stream_pts_to
  (b: base_t) (len: len_t) (pos: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: Tot slprop
= exists* (p: SZ.t).
    AP.pts_to b contents **
    R.pts_to pos p **
    pure (
      Seq.length contents == SZ.v len /\
      SZ.v p <= SZ.v len /\
      v == Seq.slice contents (SZ.v p) (SZ.v len)
    )

(* After [truncate], the enclosing stream keeps the ownership of the bytes
   beyond the truncation point, together with the fact that they are physically
   adjacent to the truncated prefix. *)
let stream_is_prefix_of
  (base_x: base_t) (len_x: len_t) (pos_x: pos_t)
  (base_y: base_t) (len_y: len_t) (pos_y: pos_t)
  (contents0: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: Tot slprop
= exists* (s': base_t).
    AP.pts_to s' suffix **
    pure (
      base_x == base_y /\ pos_x == pos_y /\
      AP.adjacent base_x (SZ.v len_x) s' /\
      SZ.v len_x + Seq.length suffix == SZ.v len_y
    )

noextract
inline_for_extraction
let pts_to_inst : I.input_stream_pts_to base_t len_t pos_t = {
  pts_to = stream_pts_to;
  is_prefix_of = stream_is_prefix_of;
}
