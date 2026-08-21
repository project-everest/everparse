module EverParse3d.InputStream.Extern
open Pulse.Lib.Pervasives
#lang-pulse

(* The [extern] backend: the input stream is an abstract, client-provided C
   object. Everything about it is assumed, exactly as in the Low* version
   (src/3d/prelude/extern/EverParse3d.InputStream.Extern.Base.fsti): the C
   client is trusted to implement the EverParseHas/Read/Peep/Skip/Empty
   primitives declared in EverParse.h.

   Since the stream carries its own length and position, [len_t] and [pos_t]
   are [unit]: KaRaMeL erases unit arguments, so the extracted C validators
   take the stream as a single argument, as in Low*. *)

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I = EverParse3d.InputStream.Base
module LP = LowParse.Spec.Base
module LPL = LowParse.PulseParse.Base
module Common = EverParse3d.Actions.Common

open EverParse3d.InputStream.Base { seq_is_suffix_of }

assume val input_stream_base : Type0

inline_for_extraction
noextract
let base_t = input_stream_base
inline_for_extraction
noextract
let len_t = unit
inline_for_extraction
noextract
let pos_t = unit

assume val stream_pts_to
  (base: base_t) (len: len_t) (pos: pos_t)
  (contents: Seq.seq U8.t) (v: Seq.seq U8.t)
: slprop

assume val stream_is_prefix_of
  (base_x: base_t) (len_x: len_t) (pos_x: pos_t)
  (base_y: base_t) (len_y: len_t) (pos_y: pos_t)
  (contents: Seq.seq U8.t) (suffix: Seq.seq U8.t)
: slprop

noextract
inline_for_extraction
let pts_to_inst : I.input_stream_pts_to base_t len_t pos_t = {
  pts_to = stream_pts_to;
  is_prefix_of = stream_is_prefix_of;
}

assume val stream_pts_to_is_suffix_of :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (contents: Seq.seq U8.t) ->
    (v: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
      (stream_pts_to base len pos contents v)
      (fun _ -> stream_pts_to base len pos contents v ** pure (v `seq_is_suffix_of` contents))

assume val stream_get_position :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      stream_pts_to base len pos contents v
    ))
    (ensures fun res ->
      stream_pts_to base len pos contents v **
      pure (
        SZ.v res + Seq.length v == Seq.length contents
      )
    )

assume val stream_has :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      stream_pts_to base len pos contents v
    ))
    (ensures (fun res ->
      stream_pts_to base len pos contents v **
      pure (res == true <==> SZ.v n <= Seq.length v)
    ))

(* [has_at base len pos off n] tests whether [n] bytes are available
     starting [off] bytes after the current position, without consuming
     anything. This is what the "no read" (non-consuming) validators need,
     since they track their position in a separate [SZ.t] reference. *)
assume val stream_has_at :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (off: SZ.t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      stream_pts_to base len pos contents v ** pure (
      SZ.v off <= Seq.length v
    )))
    (ensures (fun res ->
      stream_pts_to base len pos contents v ** pure (
      (res == true <==> SZ.v off + SZ.v n <= Seq.length v) /\
      (res == true ==> SZ.fits (SZ.v off + SZ.v n))
    )))

assume val stream_read :
(t': Type0) ->
    (k: LP.parser_kind) ->
    (p: LP.parser k t') ->
    (r: LPL.leaf_reader p) ->
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt t'
    (requires (
      stream_pts_to base len pos contents v ** pure (
      k.LP.parser_kind_subkind == Some LP.ParserStrong /\
      k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
      k.LP.parser_kind_low == SZ.v n /\
      Some? (LP.parse p v)
    )))
    (ensures (fun dst' -> exists* v' .
      stream_pts_to base len pos contents v' ** pure (
      Seq.length v >= SZ.v n /\
      LP.parse p (Seq.slice v 0 (SZ.v n)) == Some (dst', SZ.v n) /\
      LP.parse p v == Some (dst', SZ.v n) /\
      Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
    )))

assume val stream_skip :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
    (requires (
      stream_pts_to base len pos contents v ** pure (
      Seq.length v >= SZ.v n
    )))
    (ensures (fun _ -> exists* v' .
      stream_pts_to base len pos contents v' ** pure (
      Seq.length v >= SZ.v n /\
      v' `Seq.equal` Seq.slice v (SZ.v n) (Seq.length v)
    )))

assume val stream_empty :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      stream_pts_to base len pos contents v
    ))
    (ensures (fun res ->
      stream_pts_to base len pos contents Seq.empty ** pure (
      SZ.v res == Seq.length v
    )))

assume val stream_truncate :
(base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt (base_t & len_t & pos_t)
    (requires (
      stream_pts_to base len pos contents v ** pure (
      SZ.v n <= Seq.length v
    )))
    (ensures (fun res -> exists* contents' v1 v2 .
      stream_pts_to res._1 res._2 res._3 contents' v1 **
      stream_is_prefix_of res._1 res._2 res._3 base len pos contents v2 **
      pure (
      	SZ.v n <= Seq.length v /\
        Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
	Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
	Seq.length v <= Seq.length contents /\
	Seq.equal contents' (Seq.append (Seq.slice contents 0 (Seq.length contents - Seq.length v)) v1) /\
	Ghost.reveal v == Seq.append v1 v2
    )))

assume val stream_untruncate :
(base_x: base_t) ->
    (len_x: len_t) ->
    (pos_x: pos_t) ->
    (base_y: base_t) ->
    (len_y: len_t) ->
    (pos_y: pos_t) ->
    (contents: Seq.seq U8.t) ->
    (v: Seq.seq U8.t) ->
    (contents0: Seq.seq U8.t) ->
    (suffix: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
    (requires (
       stream_pts_to base_x len_x pos_x contents v **
       stream_is_prefix_of base_x len_x pos_x base_y len_y pos_y contents0 suffix **
       pure (contents0 == Seq.append contents suffix)
    ))
    (ensures (fun _ ->
       stream_pts_to base_y len_y pos_y contents0 (Seq.append v suffix)
    ))

noextract
inline_for_extraction
instance input_stream_extern : I.input_stream_inst base_t len_t pos_t = {
  pts_to_inst = pts_to_inst;
  pts_to_is_suffix_of = stream_pts_to_is_suffix_of;
  get_position = stream_get_position;
  has = stream_has;
  has_at = stream_has_at;
  read = stream_read;
  skip = stream_skip;
  empty = stream_empty;
  truncate = stream_truncate;
  untruncate = stream_untruncate;
}

(* The error handler used when 3d is invoked with `--use_error_handler_macro`.
   Each backend provides its own; the 3D frontend passes the one matching the
   selected `--input_stream` to `validate_with_error_handler`. *)
[@@CMacro]
assume val error_handler_macro : Common.error_handler #base_t #len_t #pos_t

(* No `copy_buffer` instance: probing is unavailable for the `extern` backend,
   as in Low*. *)
