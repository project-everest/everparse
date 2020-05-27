module Batch
open FStar.All

val postprocess
  (out_dir: string)
  (files_and_modules: list (string & string))
: ML unit
