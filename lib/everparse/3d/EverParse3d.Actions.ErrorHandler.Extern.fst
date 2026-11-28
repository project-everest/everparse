module EverParse3d.Actions.ErrorHandler.Extern

(* The `extern` backend's error handler type, monomorphic. Shared with the
   `static` backend, which re-exports the same input stream instance.

   See EverParse3d.Actions.ErrorHandler.Buffer for why this module exists. The
   signature genuinely differs from the buffer one: an extern stream tracks its
   own position, so the position is passed by value rather than by pointer. *)

module I = EverParse3d.InputStream.Base
module E = EverParse3d.InputStream.Extern.Types

[@@FStar.Attributes.rename_let "EVERPARSE_ERROR_HANDLER"; FStar.Attributes.custard_no_unfold]
let error_handler = I.error_handler_arrow E.base_t E.len_t E.pos_t

(* Unfold this identity coercion and exclude it from standalone extraction:
   it must leave no runtime function in the header-only library. *)
[@@noextract_to "krml"]
unfold
let error_handler_arrow_of (h: error_handler) : I.error_handler_arrow E.base_t E.len_t E.pos_t = h
