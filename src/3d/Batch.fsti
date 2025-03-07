module Batch
open HashingOptions
open FStar.All

val cl_wrapper: unit -> ML string

(* The --print_in_place step has to be performed at source generation
   time, not at verification time, because if the user requests files
   to be processed by a Makefile, they must not be modified again
   after they are generated. Thus, we do it always, regardless of
   --batch. *)

val pretty_print_source_modules
  (fstar_exe : string)
  (_: input_stream_binding_t)
  (out_dir: string)
  (files_and_modules: list (string & string))
: ML unit

val verify_fst_file
  (fstar_exe : string)
  (_: input_stream_binding_t)
  (out_dir: string)
  (file: string)
: ML unit

val extract_fst_file
  (fstar_exe : string)
  (_: input_stream_binding_t)
  (out_dir: string)
  (file: string)
: ML unit

val check_inplace_hashes
  (files_3d_c: list string)
: ML unit

val copy_clang_format
  (out_dir: string)
: ML unit

val copy_everparse_h
  (clang_format: bool)
  (clang_format_executable: string)
  (_: input_stream_binding_t)
  (out_dir: string)
: ML unit

val produce_and_postprocess_one_c
  (_: input_stream_binding_t)
  (emit_output_types_defs: bool)
  (add_include: list string)
  (clang_format: bool)
  (clang_format_executable: string)
  (out_dir: string)
  (file: string)
  (modul: string)
  (dep_files_and_modules: list (string & string))
: ML unit

val postprocess_wrappers
  (_: input_stream_binding_t)
  (clang_format: bool)
  (clang_format_executable: string)
  (out_dir: string)
  (files_and_modules: list (string & string))
: ML unit

val postprocess_fst
  (fstar_exe : string)
  (_: input_stream_binding_t)
  (emit_output_types_defs: bool)
  (add_include: list string)
  (clang_format: bool)
  (clang_format_executable: string)
  (skip_c_makefiles: bool)
  (cleanup: bool)
  (no_everparse_h: bool)
  (save_hashes: bool)
  (out_dir: string)
  (files_and_modules: list (string & string))
: ML unit

val check_all_hashes
  (ch: check_hashes_t)
  (out_dir: string)
  (files_and_modules: list (string & string))
: ML unit
