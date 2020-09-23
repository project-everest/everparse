module Batch
open FStar.All

val postprocess
  (clang_format: bool)
  (clang_format_executable: string)
  (cleanup: bool)
  (no_everparse_h: bool)
  (out_dir: string)
  (files_and_modules: list (string & string))
: ML unit
