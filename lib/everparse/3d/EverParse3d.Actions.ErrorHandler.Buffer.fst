module EverParse3d.Actions.ErrorHandler.Buffer

(* The `buffer` backend's error handler type, monomorphic.

   EverParse3d.InputStream.Base.error_handler_arrow is parameterized by the
   input stream types, because the Pulse prelude is built once and instantiated
   through a typeclass. KaRaMeL has no parameterized typedefs, so it inlines
   such an abbreviation at every use site and emits nothing for it -- which
   would drop the public EVERPARSE_ERROR_HANDLER typedef that the Low* backend
   provides, silently breaking clients that name it, and would spell the whole
   function-pointer type out in every generated validator's prototype.

   Instantiating it here at this backend's stream types makes it monomorphic
   again, so `-no-inline-type-abbrev` can preserve it, and generated validators
   name it in their prototypes.

   The backend's [input_stream_inst] instance carries this type as its
   [error_handler_t] member, so a validator's argument type reaches extraction
   as a projection out of that instance, which specialization iota-reduces to
   this definition. Specialization does not delta-unfold further here (its
   normalization steps are `delta_attr`/`delta_only`, not `delta_namespace`),
   so the 0-ary alias survives for KaRaMeL to preserve.

   [error_handler_arrow_of] is how the instance discharges
   [error_handler_arrow_of_t]: the alias is transparent here, so it is the
   identity and needs no coercion.

   This module is an API module of the `EverParse` bundle, whose rename-prefix
   plus -fmicrosoft turn `error_handler` into `EVERPARSE_ERROR_HANDLER`. See
   lib/everparse/3d/krml/header.Makefile.

   It holds nothing else: the bundle makes a whole module public at a time, and
   only one of the ErrorHandler modules may be public per backend, or the two
   would collide on that name. *)

module I = EverParse3d.InputStream.Base
module B = EverParse3d.InputStream.Buffer.Types

let error_handler = I.error_handler_arrow B.base_t B.len_t B.pos_t

(* [noextract_to "krml"] + [unfold]: this is the identity, and it must leave no
   trace in the extracted code. A public [inline_for_extraction] definition
   would be materialized as a real C function in this API module of the
   `EverParse` bundle, which is header-only. *)
[@@noextract_to "krml"]
unfold
let error_handler_arrow_of (h: error_handler) : I.error_handler_arrow B.base_t B.len_t B.pos_t = h
