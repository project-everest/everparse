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

(* The error-handler callback type.

   This is the instance's [error_handler_t] member rather than the arrow type
   itself, so that it extracts to a 0-ary, per-backend alias that KaRaMeL can
   preserve as EVERPARSE_ERROR_HANDLER. See EverParse3d.InputStream.Base for
   why, and [I.error_handler_arrow] for the shape it is equal to.

   [unfold]: this is a *generic* projection out of the instance. If a
   declaration survives to extraction, KaRaMeL gets an unrepresentable type
   (`void *`) which, under the `EverParse` bundle's rename-prefix, additionally
   steals the C name from the backend alias it is supposed to resolve to.
   Unfolding it at each use site is what lets extraction resolve the
   projection to that alias.

   [noextract_to "krml"]: `unfold` removes it from every use site, but F* still
   emits a declaration for it, which extracts as an opaque `any`; KaRaMeL drops
   its (now unused) type parameters and turns it into a 0-ary
   `typedef void *`, stealing the C name from the backend alias. *)
[@@noextract_to "krml"]
unfold
let error_handler
    {| inst: I.input_stream_inst 'base_t 'len_t 'pos_t  |}
= inst.error_handler_t

(* Erased at extraction: every instance discharges [error_handler_arrow_of_t]
   with the identity. *)
unfold
let error_handler_arrow_of
    (#base_t #len_t #pos_t: Type0)
    {| inst: I.input_stream_inst base_t len_t pos_t |}
    (h: error_handler #base_t #len_t #pos_t)
: I.error_handler_arrow base_t len_t pos_t
= inst.error_handler_arrow_of_t h

(*
// The C macro used as the error handler when 3d is invoked with
// `--use_error_handler_macro`. It lives here (rather than in
// EverParse3d.Actions.Base) so that it is also reachable from
// EverParse3d.ProbeActions, which must select between the dynamic
// error-handler callback and this macro just like the validators do.
[@@CMacro]
assume val error_handler_macro: error_handler
