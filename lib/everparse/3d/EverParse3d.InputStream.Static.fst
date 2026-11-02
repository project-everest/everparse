module EverParse3d.InputStream.Static
open Pulse.Lib.Pervasives
#lang-pulse

(* The static backend shares the verified extern implementation. Its foreign
   primitives have stable supplying-header bindings; the selected profile's
   EverParseStreamPrimitives.h supplies static-inline rather than external
   declarations. No source rewriting or profile-specific verification is
   needed. This facade retains its own error-handler macro. *)

module E = EverParse3d.InputStream.Extern
module I = EverParse3d.InputStream.Base
module Common = EverParse3d.Actions.Common
module AB = EverParse3d.Actions.Base
open EverParse3d.State

inline_for_extraction
noextract
let base_t = E.base_t
inline_for_extraction
noextract
let len_t = E.len_t
inline_for_extraction
noextract
let pos_t = E.pos_t

(* The client context, re-exported so that generated code can name it as
   `B.extra_t` under either backend. *)
inline_for_extraction
noextract
let extra_t = E.extra_t

noextract
inline_for_extraction
instance input_stream_static : I.input_stream_inst base_t len_t pos_t =
  E.input_stream_extern

(* Inherit the native SizeT scan policy and unit-returning high-level empty
   adapter as well; the underlying client primitive signatures are unchanged. *)

(* The error handler used when 3d is invoked with `--use_error_handler_macro`.
   Each backend provides its own; the 3D frontend passes the one matching the
   selected `--input_stream` to `validate_with_error_handler`. *)
[@@CMacro; FStar.Attributes.custard_extern "EVERPARSE_ERROR_HANDLER_MACRO"; FStar.Attributes.custard_c_header "EverParse.h"]
assume val error_handler_macro : Common.error_handler #base_t #len_t #pos_t

(* `field_ptr_after` is available here for the same reason it is available in
   `extern`: it rests on the client's Peep primitive, which both backends
   provide. Re-exported rather than redefined, so that the two backends share
   one assumed primitive. *)
noextract
inline_for_extraction
let ___PUINT8 = E.___PUINT8

[@@Common.specialize_backend]
noextract
inline_for_extraction
let field_ptr_after
: option (AB.field_ptr_after_t base_t len_t pos_t #input_stream_static ___PUINT8)
= E.field_ptr_after

[@@Common.specialize_backend]
noextract
inline_for_extraction
let field_ptr_after_with_setter (extra_state: state_dict)
: option (AB.field_ptr_after_setter_t base_t len_t pos_t #input_stream_static extra_state ___PUINT8)
= E.field_ptr_after_with_setter extra_state

(* No `copy_buffer` instance: probing is unavailable for the `static` backend,
   as in Low*. *)
