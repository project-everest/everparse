module EverParse3d.Actions.ErrorHandler.Buffer

(* The `buffer` backend's error handler type, monomorphic.

   EverParse3d.Actions.Common.error_handler is parameterized by the input
   stream types, because the Pulse prelude is built once and instantiated
   through a typeclass. KaRaMeL has no parameterized typedefs, so it inlines
   such an abbreviation at every use site and emits nothing for it -- which
   would drop the public EVERPARSE_ERROR_HANDLER typedef that the Low* backend
   provides, silently breaking clients that name it.

   Instantiating it here at this backend's stream types makes it monomorphic
   again, so `-no-inline-type-abbrev` can preserve it. This module is an API
   module of the `EverParse` bundle, whose rename-prefix plus -fmicrosoft turn
   `error_handler` into `EVERPARSE_ERROR_HANDLER`. See
   lib/everparse/3d/krml/header.Makefile.

   It holds nothing else: the bundle makes a whole module public at a time, and
   only one of the ErrorHandler modules may be public per backend, or the two
   would collide on that name. *)

module AC = EverParse3d.Actions.Common
module B = EverParse3d.InputStream.Buffer

let error_handler = AC.error_handler #B.base_t #B.len_t #B.pos_t
