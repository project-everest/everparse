module EverParse3d.Actions.ErrorHandler.Extern

(* The `extern` backend's error handler type, monomorphic. Shared with the
   `static` backend, which re-exports the same input stream instance.

   See EverParse3d.Actions.ErrorHandler.Buffer for why this module exists. The
   signature genuinely differs from the buffer one: an extern stream tracks its
   own position, so the position is passed by value rather than by pointer. *)

module AC = EverParse3d.Actions.Common
module E = EverParse3d.InputStream.Extern

let error_handler = AC.error_handler #E.base_t #E.len_t #E.pos_t
