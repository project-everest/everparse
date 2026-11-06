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

(* Recasing of the names that `rename_let` gives to the locals of the
   generated C code, so that a 3D field `__bitfield_0` yields `bitfield0`,
   `resultAfterBitfield0`, ... This follows the conventions of KaRaMeL's
   former `-fmicrosoft` option (`GlobalNames.pascal_case`): underscores are
   dropped and start a new word, and when the name has underscores, letters
   following an upper-case letter or a digit are lower-cased.

   These functions are evaluated by the normalizer when the combinators are
   inlined, so they must only use primitive string operations: in particular,
   `FStar.Char.uppercase` is not a primitive, hence the detour through
   one-character strings. *)
inline_for_extraction noextract
let rec pascal_case_aux (has_underscore: bool) (what_next: nat) (l: list FStar.String.char)
  : Tot string (decreases l)
= match l with
  | [] -> ""
  | c :: cs ->
    if c = '_'
    then pascal_case_aux has_underscore 1 cs
    else
      let s = FStar.String.string_of_list [c] in
      let up = FStar.String.uppercase s in
      let low = FStar.String.lowercase s in
      let out = if what_next = 1 then up else if what_next = 2 && has_underscore then low else s in
      let what_next' = if up = s then 2 else if low = s then 0 else what_next in
      out ^ pascal_case_aux has_underscore what_next' cs

inline_for_extraction noextract
let pascal_case_impl (s: string) : Tot string =
  let l = FStar.String.list_of_string s in
  pascal_case_aux (List.Tot.mem '_' l) 1 l

inline_for_extraction noextract
let camel_case_impl (s: string) : Tot string =
  match FStar.String.list_of_string (pascal_case_impl s) with
  | [] -> ""
  | c :: cs ->
    FStar.String.lowercase (FStar.String.string_of_list [c]) ^
    FStar.String.string_of_list cs

(* Custard does not reduce recursive functions (it normalizes without zeta),
   hence the explicit [normalize_term]. *)
inline_for_extraction noextract
let pascal_case (s: string) : Tot string = normalize_term (pascal_case_impl s)

inline_for_extraction noextract
let camel_case (s: string) : Tot string = normalize_term (camel_case_impl s)

[@@FStar.Attributes.rename_let "EVERPARSE_APP_CTXT"; FStar.Attributes.custard_no_unfold]
let app_ctxt = AppCtxt.app_ctxt

(* The error-handler callback type.

   Each instance supplies a monomorphic [error_handler_t] alias that Custard
   preserves as EVERPARSE_ERROR_HANDLER. See EverParse3d.InputStream.Base and
   [I.error_handler_arrow] for the corresponding function-pointer signature.

   This generic projection is unfolded at use sites and excluded from
   standalone extraction, leaving the selected backend's alias as the public
   C typedef. *)
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
