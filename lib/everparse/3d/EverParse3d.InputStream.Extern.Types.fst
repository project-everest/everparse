module EverParse3d.InputStream.Extern.Types
open Pulse.Lib.Pervasives
#lang-pulse

(* The `extern` backend's stream types and its [input_stream_pts_to] instance.

   Split out of EverParse3d.InputStream.Extern so that
   EverParse3d.Actions.ErrorHandler.Extern, which needs them to state the
   backend's error-handler type, can sit *between* this module and the full
   [input_stream_inst] instance -- which in turn has to name that error-handler
   type. EverParse3d.InputStream.Extern re-exports everything here, so generated
   code still refers to these under that module name. *)

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I = EverParse3d.InputStream.Base

(* The client-supplied per-invocation context, `EVERPARSE_EXTRA_T`. The 3D
   frontend passes it into the generated wrapper, which threads it down to the
   primitives below. It is abstract here so that KaRaMeL emits it as a real C
   parameter, matching the Low* prelude
   (`src/3d/prelude/extern/EverParse3d.InputStream.Extern.Base.fsti`). *)
assume val extra_t : Type0

assume val input_stream_base : Type0

inline_for_extraction
noextract
let base_t = input_stream_base
(* [0] is "unbounded"; [n > 0] means the view ends at absolute position
   [n - 1]. See the header comment. *)
inline_for_extraction
noextract
let len_t = SZ.t
inline_for_extraction
noextract
let pos_t = SZ.t

(* The raw, client-side view of the stream. It takes no [len]: the client knows
   nothing of our truncation bounds, and dropping the argument here is what
   keeps the assumed C prototypes (EverParseStreamHas, ...Read, ...Skip, ...)
   exactly as they were. *)
assume val stream_pts_to_raw
  (base: base_t) (pos: Ghost.erased pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: slprop

assume val stream_is_prefix_of_raw
  (base_x: base_t) (pos_x: Ghost.erased pos_t)
  (base_y: base_t) (pos_y: Ghost.erased pos_t)
  (contents: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: slprop

inline_for_extraction
noextract
let bounded (len: len_t) : Tot bool = SZ.gt len 0sz

(* What a [len] asserts about the view it labels. The [fits] conjunct is the
   standing assumption that the whole stream is addressable, without which the
   bound of a truncation could not be computed. *)
let bound_ok (len: len_t) (pos: pos_t) (contents: Seq.seq U8.t) : prop =
  SZ.fits (SZ.v pos + Seq.length contents + 1) /\
  (bounded len ==> SZ.v len == SZ.v pos + Seq.length contents + 1)

let stream_pts_to
  (base: base_t) (len: len_t) (pos: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: slprop
= stream_pts_to_raw base pos contents v ** pure (bound_ok len pos contents)

(* [x] is a truncation of [y]. Beyond the raw witness this records what
   [untruncate] needs in order to rebuild [y]'s bound from [x]'s: a truncated
   view is always bounded, and its bound falls short of its parent's by exactly
   the suffix that was withheld. *)
let stream_is_prefix_of
  (base_x: base_t) (len_x: len_t) (pos_x: pos_t)
  (base_y: base_t) (len_y: len_t) (pos_y: pos_t)
  (contents: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: slprop
= stream_is_prefix_of_raw base_x pos_x base_y pos_y contents suffix **
  pure (
    pos_x == pos_y /\
    bounded len_x /\
    SZ.fits (SZ.v len_x + Seq.length suffix) /\
    (bounded len_y ==> SZ.v len_y == SZ.v len_x + Seq.length suffix)
  )

noextract
inline_for_extraction
let pts_to_inst : I.input_stream_pts_to base_t len_t pos_t = {
  pts_to = stream_pts_to;
  is_prefix_of = stream_is_prefix_of;
}
