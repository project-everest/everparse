module Options
include Options.Base
open HashingOptions
open FStar.All

val file_name (mname:string) : ML string

val debug_print_string (s:string) : ML unit

val batch : unit -> ML bool

val clang_format : unit -> ML bool

val clang_format_executable : unit -> ML string

val get_clang_format_use_custom_config: unit -> ML bool

val cleanup : unit -> ML bool

val skip_c_makefiles : unit -> ML bool

val no_everparse_h : unit -> ML bool

val get_hoist_locals : unit -> ML bool

val get_goto_for_early_return : unit -> ML bool

val get_blank_lines : unit -> ML bool

val get_line_comments : unit -> ML bool

val get_init_locals : unit -> ML (option string)

val save_hashes : unit -> ML bool

val equate_types_list : unit -> ML (list (string & string))

val micro_step : unit -> ML (option micro_step_t)

val produce_c_from_existing_krml : unit -> ML bool

val skip_deps : unit -> ML bool

val makefile : unit -> ML (option makefile_type)

val makefile_name : unit -> ML string

val skip_o_rules : unit -> ML bool

val json : unit -> ML bool

val input_stream_binding : unit -> ML input_stream_binding_t

val emit_output_types_defs : unit -> ML bool

val config_file : unit -> ML (option string)

val add_include : unit -> ML (list string)

val make_includes : unit -> ML string

val config_module_name : unit -> ML (option string)

val emit_smt_encoding: unit -> ML bool

val z3_test: unit -> ML (option string)

val z3_pos_test: unit -> ML bool

val z3_neg_test: unit -> ML bool

val z3_witnesses: unit -> ML pos

val debug: unit -> ML bool

val z3_diff_test: unit -> ML (option (string & string))

val save_z3_transcript: unit -> ML (option string)

val test_checker: unit -> ML (option string)

val z3_branch_depth: unit -> ML nat

val get_z3_flight_name: unit -> ML string

val get_produce_testcases_c: unit -> ML bool

val get_z3_skip_c_initializers: unit -> ML bool

val get_use_error_handler_macro: unit -> ML bool

val get_z3_use_ptr: unit -> ML bool

val get_fstar_exe: unit -> ML string
