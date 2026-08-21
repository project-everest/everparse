module EverParse3d.InputStream.Static
open Pulse.Lib.Pervasives
#lang-pulse

(* The [static] backend.

   In Low*, `static` is not a separate F* development at all: `Batch.ml` maps
   "static" to "extern" for the F*/krml include directory, and the two backends
   differ *only* by the C linkage of the five primitives declared in
   `EverParse.h` (`EverParseHas`, `EverParseRead`, `EverParsePeep`,
   `EverParseSkip`, `EverParseEmpty` are `extern` in one and `static [inline]`
   in the other).

   Here the two backends must nevertheless be distinct F* modules, because each
   backend owns its own `[@@CMacro] assume val error_handler_macro`, which the
   3D frontend passes to `validate_with_error_handler`. So this module is a thin
   re-export of the `extern` instance, with its own error handler macro. The
   `static`/`extern` difference remains entirely in the emitted `EverParse.h`. *)

module E = EverParse3d.InputStream.Extern
module I = EverParse3d.InputStream.Base
module Common = EverParse3d.Actions.Common

inline_for_extraction
noextract
let base_t = E.base_t
inline_for_extraction
noextract
let len_t = E.len_t
inline_for_extraction
noextract
let pos_t = E.pos_t

noextract
inline_for_extraction
instance input_stream_static : I.input_stream_inst base_t len_t pos_t =
  E.input_stream_extern

(* The error handler used when 3d is invoked with `--use_error_handler_macro`.
   Each backend provides its own; the 3D frontend passes the one matching the
   selected `--input_stream` to `validate_with_error_handler`. *)
[@@CMacro]
assume val error_handler_macro : Common.error_handler #base_t #len_t #pos_t

(* No `copy_buffer` instance: probing is unavailable for the `static` backend,
   as in Low*. *)
