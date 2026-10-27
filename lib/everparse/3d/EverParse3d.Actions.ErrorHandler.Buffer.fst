module EverParse3d.Actions.ErrorHandler.Buffer

(* The `buffer` backend's error handler type, monomorphic.

   EverParse3d.InputStream.Base.error_handler_arrow is parameterized by the
   input stream types. Instantiating it here supplies a monomorphic alias
   that Custard preserves as EVERPARSE_ERROR_HANDLER, so generated validator
   prototypes and clients can name the callback type.

   The backend's [input_stream_inst] instance carries this type as its
   [error_handler_t] member, so a validator's argument type reaches extraction
   as a projection out of that instance, which specialization iota-reduces to
   this definition. Specialization does not delta-unfold further here (its
   normalization steps are `delta_attr`/`delta_only`, not `delta_namespace`),
   so the alias reaches Custard without being unfolded.

   [error_handler_arrow_of] is how the instance discharges
   [error_handler_arrow_of_t]: the alias is transparent here, so it is the
   identity and needs no coercion.

   The attributes below give the alias its C name and preserve it during
   extraction. Runtime header generation selects the error-handler module
   matching each profile; see src/3d/runtime/header.Makefile. *)

module I = EverParse3d.InputStream.Base
module B = EverParse3d.InputStream.Buffer.Types

[@@FStar.Attributes.rename_let "EVERPARSE_ERROR_HANDLER"; FStar.Attributes.custard_no_unfold]
let error_handler = I.error_handler_arrow B.base_t B.len_t B.pos_t

(* Unfold this identity coercion and exclude it from standalone extraction:
   it must leave no runtime function in the header-only library. *)
[@@noextract_to "krml"]
unfold
let error_handler_arrow_of (h: error_handler) : I.error_handler_arrow B.base_t B.len_t B.pos_t = h
