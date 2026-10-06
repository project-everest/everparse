module EverParse3d.Actions.ErrorHandler.Extern

(* The `extern` backend's error handler type, monomorphic. Shared with the
   `static` backend, which re-exports the same input stream instance.

   See EverParse3d.Actions.ErrorHandler.Buffer for why this module exists. The
   signature genuinely differs from the buffer one: an extern stream tracks its
   own position, so the position is passed by value rather than by pointer. *)

module I = EverParse3d.InputStream.Base
module E = EverParse3d.InputStream.Extern.Types

let error_handler = I.error_handler_arrow E.base_t E.len_t E.pos_t

(* [noextract_to "krml"] + [unfold]: this is the identity, and it must leave no
   trace in the extracted code. A public [inline_for_extraction] definition
   would be materialized as a real C function in this API module of the
   `EverParse` bundle, which is header-only. *)
[@@noextract_to "krml"]
unfold
let error_handler_arrow_of (h: error_handler) : I.error_handler_arrow E.base_t E.len_t E.pos_t = h
