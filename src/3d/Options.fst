module Options
include Options.Base
friend Options.Base
open HashingOptions
open FStar.All

module U8 = FStar.UInt8
module OS = OS
open Utils

let get_file_name mname = mname ^ ".3d"

let debug_print_string (s:string): ML unit =
  if !_debug
  then FStar.IO.print_string s
  else ()

let get_batch () =
  !_batch

let get_clang_format () =
  !_clang_format

let get_clang_format_executable () =
  match !_clang_format_executable with
  | None -> ""
  | Some s -> s

let get_clang_format_use_custom_config () =
  !clang_format_use_custom_config

let get_cleanup () =
  !_cleanup

let get_skip_c_makefiles () =
  !_skip_c_makefiles

let get_no_everparse_h () =
  !_no_copy_everparse_h

let get_hoist_locals () =
  !hoist_locals

let get_goto_for_early_return () =
  !goto_for_early_return

let get_blank_lines () =
  !blank_lines

let get_line_comments () =
  !line_comments

let get_init_locals () : ML (option string) =
  match !init_locals with
  | Some s -> Some (s <: string)
  | None -> None

let get_save_hashes () =
  !_save_hashes

let get_equate_types_list () =
  List.map
    (fun (x: valid_string valid_equate_types) ->
      let [a; b] = String.split [','] x in (a, b)
    )
    !_equate_types_list

let get_micro_step _ =
  match !_micro_step with
  | None -> None
  | Some "verify" -> Some MicroStepVerify
  | Some "extract" -> Some MicroStepExtract
  | Some "copy_clang_format" -> Some MicroStepCopyClangFormat
  | Some "copy_everparse_h" -> Some MicroStepCopyEverParseH
  | Some "emit_config" -> Some MicroStepEmitConfig
  | Some "save_hashes" -> Some MicroStepSaveHashes

let get_produce_c_from_existing_krml _ =
  !_produce_c_from_existing_krml

let get_skip_deps _ =
  !_skip_deps

let get_makefile _ =
  match !_makefile with
  | None -> None
  | Some "gmake" -> Some MakefileGMake
  | Some "nmake" -> Some MakefileNMake

let get_makefile_name _ =
  match !_makefile_name with
  | None -> OS.concat (output_dir ()) "EverParse.Makefile"
  | Some mf -> OS.concat_if_not_absolute (output_dir ()) mf

let get_skip_o_rules _ =
  !_skip_o_rules

let get_json () =
  !_json

let get_input_stream_binding () : ML input_stream_binding_t =
  let input_stream_include () : ML string =
    match !_input_stream_include with
    | None -> ""
    | Some s -> s
  in
  match !_input_stream_binding with
  | None
  | Some "buffer" -> InputStreamBuffer
  | Some "extern" ->
    InputStreamExtern (input_stream_include ())
  | Some "static" ->
    InputStreamStatic (input_stream_include ())

let get_emit_output_types_defs () = !_emit_output_types_defs

let get_config_file () = 
  match !_config_file with
  | None -> None
  | Some s -> Some s

let get_add_include () =
  !_add_include

let make_includes () =
  let incs = get_add_include () in
  List.Tot.fold_left
    (fun accu inc ->
      Printf.sprintf
        "%s#include %s\n"
        accu
        inc
    )
    ""
    incs

let config_module_name () =
  match !_config_file with
  | None -> None
  | Some s -> Some (strip_suffix (OS.basename s) ".3d.config")

let get_emit_smt_encoding () =
  !_emit_smt_encoding

let get_z3_test () = !_z3_test

let get_z3_pos_test () =
  match !_z3_test with
  | None -> false
  | _ -> match !_z3_test_mode with
  | Some "neg" -> false
  | _ -> true

let get_z3_neg_test () =
  match !_z3_test with
  | None -> false
  | _ -> match !_z3_test_mode with
  | Some "pos" -> false
  | _ -> true

let get_z3_witnesses () =
  match !_z3_witnesses with
  | None -> 1
  | Some s ->
  try
    let n = OS.int_of_string s in
    if n < 1 then (1 <: pos) else begin
      assert (n >= 1);
      (n <: pos)
    end
  with _ -> 1

let get_debug _ = !_debug

let get_z3_diff_test _ =
  match !_z3_diff_test with
  | None -> None
  | Some s -> let [p1; p2] = String.split [','] s in Some (p1, p2)

let z3_executable () =
  match !_z3_executable with
  | None -> "z3"
  | Some z3 -> z3

let get_save_z3_transcript () = !_save_z3_transcript

let get_test_checker () = !_test_checker

let get_z3_branch_depth () =
  match !_z3_branch_depth with
  | None -> 0
  | Some s ->
  try
    let n = OS.int_of_string s in
    if n < 0 then (0 <: nat) else begin
      assert (n >= 0);
      (n <: nat)
    end
  with _ -> 0

let z3_options () : ML string = 
  match !_z3_options with
  | None -> ""
  | Some s -> s

let get_z3_flight_name () : ML string =
  match !z3_flight_name with
  | None -> ""
  | Some s -> s

let get_produce_testcases_c () : ML bool =
  not !no_produce_testcases_c

let get_z3_skip_c_initializers () : ML bool =
  !z3_skip_c_initializers

let get_use_error_handler_macro () : ML bool =
  !use_error_handler_macro

let get_pulse () : ML bool =
  !pulse

let pulse_backend_module () : ML string =
  match get_input_stream_binding () with
  | HashingOptions.InputStreamBuffer -> "EverParse3d.InputStream.Buffer"
  | HashingOptions.InputStreamExtern _ -> "EverParse3d.InputStream.Extern"
  | HashingOptions.InputStreamStatic _ -> "EverParse3d.InputStream.Static"

let pulse_inst () : ML string =
  match get_input_stream_binding () with
  | HashingOptions.InputStreamBuffer -> "B.input_stream_buffer"
  | HashingOptions.InputStreamExtern _ -> "B.input_stream_extern"
  | HashingOptions.InputStreamStatic _ -> "B.input_stream_static"

let get_z3_use_ptr () : ML bool =
  !use_ptr_for_probe

let get_fstar_exe () : ML string =
  match !fstar_exe with
  | None ->
    begin match OS.getenv_opt "FSTAR_EXE" with
    | Some s -> s
    | None ->
      let opt_fstar = OS.concat (OS.concat (OS.concat (OS.concat (OS.concat OS.everparse_home "opt") "FStar") "out") "bin") "fstar.exe" in
      if OS.file_exists opt_fstar
      then opt_fstar
      else
        let fstar_exe = OS.concat (OS.concat OS.everparse_home "bin") "fstar.exe" in
        if OS.file_exists fstar_exe
        then fstar_exe
        else "fstar.exe"
    end
  | Some s -> s
