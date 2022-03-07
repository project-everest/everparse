module GenMakefile

val write_makefile
  (mtype: HashingOptions.makefile_type)
  (_: HashingOptions.input_stream_binding_t)
  (skip_types_and_interfaces: bool) (* true for --interpret *)
  (skip_o_rules: bool)
  (clang_format: bool)
  (files: list string)
: FStar.All.ML unit
