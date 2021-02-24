module GenMakefile

val write_gnu_makefile
  (skip_o_rules: bool)
  (files: list string)
: FStar.All.ML unit
