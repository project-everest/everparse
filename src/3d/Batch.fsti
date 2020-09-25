module Batch
open HashingOptions
open FStar.All

val postprocess
  (clang_format: bool)
  (clang_format_executable: string)
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
