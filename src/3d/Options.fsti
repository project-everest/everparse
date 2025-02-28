module Options
open HashingOptions
open FStar.All

val display_usage : unit -> ML unit

val compute_options (ignore: list string) : ML string

val parse_cmd_line : unit -> ML (list string)

val get_file_name (mname:string) : ML string

val get_module_name (file: string) : ML string

val get_output_dir : unit -> ML string

val debug_print_string (s:string) : ML unit

val get_batch : unit -> ML bool

val get_clang_format : unit -> ML bool

val get_clang_format_executable : unit -> ML string

val get_cleanup : unit -> ML bool

val get_skip_c_makefiles : unit -> ML bool

val get_no_everparse_h : unit -> ML bool

val get_check_hashes : unit -> ML (option check_hashes_t)

val get_save_hashes : unit -> ML bool

val get_check_inplace_hashes : unit -> ML (list string)

val get_equate_types_list : unit -> ML (list (string & string))

val get_micro_step : unit -> ML (option micro_step_t)

val get_produce_c_from_existing_krml : unit -> ML bool

val get_skip_deps : unit -> ML bool

val get_makefile : unit -> ML (option makefile_type)

val get_makefile_name : unit -> ML string

val get_skip_o_rules : unit -> ML bool

val get_json : unit -> ML bool

val get_input_stream_binding : unit -> ML input_stream_binding_t

val get_emit_output_types_defs : unit -> ML bool

val get_config_file : unit -> ML (option string)

val get_add_include : unit -> ML (list string)

val make_includes : unit -> ML string

val config_module_name : unit -> ML (option string)

val get_emit_smt_encoding: unit -> ML bool

val get_z3_test: unit -> ML (option string)

val get_z3_pos_test: unit -> ML bool

val get_z3_neg_test: unit -> ML bool

val get_z3_witnesses: unit -> ML pos

val get_debug: unit -> ML bool

val get_z3_diff_test: unit -> ML (option (string & string))

val get_save_z3_transcript: unit -> ML (option string)

val get_test_checker: unit -> ML (option string)

val get_z3_branch_depth: unit -> ML nat

val get_produce_testcases_c: unit -> ML bool

val get_fstar_exe: unit -> ML string
