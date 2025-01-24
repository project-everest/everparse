module Options
open HashingOptions
open FStar.All
open FStar.ST
module U8 = FStar.UInt8
module OS = OS
open Utils
#push-options "--warn_error -272" //top-level effects are okay

let check_config_file_name (fn:string) 
  : bool
  = let fn = OS.basename fn in
    starts_with_capital fn &&
    ends_with fn ".3d.config"

let strip_suffix (fn:string) (sfx:string { ends_with fn sfx })
  : string
  = String.sub fn 0 (String.length fn - String.length sfx)
  
inline_for_extraction
let vstring = valid_string always_valid

(* NOTE: default arguments here MUST be set to false, [] or None *)

let arg0 : ref (option vstring) = alloc None
let add_include : ref (list vstring) = alloc []
let batch : ref bool = alloc false
let clang_format : ref bool = alloc false
let clang_format_executable : ref (option vstring) = alloc None
let cleanup : ref bool = alloc false
let config_file : ref (option (valid_string check_config_file_name)) = alloc None
let debug : ref bool = alloc false
let inplace_hashes : ref (list vstring) = alloc []
let input_file : ref (list string) = alloc []
let json : ref bool = alloc false
let no_copy_everparse_h : ref bool = alloc false
let output_dir : ref (option vstring) = alloc None
let save_hashes : ref bool = alloc false
let save_z3_transcript: ref (option vstring) = alloc None
let skip_c_makefiles : ref bool = alloc false
let skip_deps: ref bool = alloc false
let skip_o_rules: ref bool = alloc false

let valid_micro_step (str: string) : Tot bool = match str with
  | "verify"
  | "extract"
  | "copy_clang_format"
  | "copy_everparse_h"
  | "emit_config"
    -> true
  | _ -> false

let micro_step : ref (option (valid_string valid_micro_step)) = alloc None

let produce_c_from_existing_krml : ref bool = alloc false

let valid_makefile (str: string) : Tot bool = match str with
  | "gmake"
  | "nmake"
  -> true
  | _ -> false

let makefile : ref (option (valid_string valid_makefile)) = alloc None
let makefile_name : ref (option vstring) = alloc None

let valid_equate_types (str: string) : Tot bool =
     let l = String.split [','] str in
     match l with
     | [m1;m2] -> true
     | _ -> false

let equate_types_list : ref (list (valid_string valid_equate_types)) = alloc []

let valid_check_hashes : string -> Tot bool = function
| "weak"
| "strong"
| "inplace"
  -> true
| _ -> false

let check_hashes : ref (option (valid_string valid_check_hashes)) = alloc None

let valid_input_stream_binding : string -> Tot bool = function
| "buffer"
| "extern"
| "static"
  -> true
| _ -> false

let input_stream_binding : ref (option (valid_string valid_input_stream_binding)) = alloc None

let input_stream_include : ref (option vstring) = alloc None

let emit_output_types_defs : ref bool = alloc true

let emit_smt_encoding : ref bool = alloc false

let fstar_exe : ref (option (valid_string always_valid)) = alloc None

let z3_diff_test: ref (option (valid_string valid_equate_types)) = alloc None

let z3_test : ref (option vstring) = alloc None

let valid_z3_test_mode : string -> Tot bool = function
| "pos"
| "neg"
| "all"
-> true
| _ -> false

let z3_test_mode : ref (option (valid_string valid_z3_test_mode)) = alloc None

let z3_witnesses : ref (option vstring) = alloc None

let z3_executable : ref (option vstring) = alloc None

let test_checker : ref (option vstring) = alloc None

let z3_branch_depth : ref (option vstring) = alloc None

let z3_options : ref (option vstring) = alloc None

noeq
type cmd_option_kind =
  | OptBool:
      (v: ref bool) ->
      cmd_option_kind
  | OptStringOption:
      (arg_desc: string) ->
      (valid: (string -> Tot bool)) ->
      (v: ref (option (valid_string valid))) ->
      cmd_option_kind
  | OptList:
      (arg_desc: string) ->
      (valid: (string -> Tot bool)) ->
      (v: ref (list (valid_string valid))) ->
      cmd_option_kind

let fstar_opt = Getopt.opt & string

noeq
type cmd_option
= | CmdOption:
    (name: string) ->
    (kind: cmd_option_kind) ->
    (desc: string) ->
    (implies: list string) (* name of OptBool to set to true *) ->
    cmd_option
  | CmdFStarOption of fstar_opt

let cmd_option_name (a: cmd_option) : Tot string =
  match a with
  | CmdFStarOption ((_, name', _), _)
  | CmdOption name' _ _ _
    -> name'

let rec find_cmd_option (name: string) (l: list cmd_option): Tot (option cmd_option) = match l with
  | [] -> None
  | a :: q ->
    if name = cmd_option_name a then Some a else find_cmd_option name q

let cmd_option_description (a: cmd_option) : Tot string =
  match a with
  | CmdOption _ _ desc _
  | CmdFStarOption (_, desc) ->
    desc

let cmd_option_arg_desc (a: cmd_option) : Tot string =
  match a with
  | CmdFStarOption ((_, _, arg), _) ->
    begin match arg with
    | Getopt.OneArg (_, argdesc) -> argdesc
    | _ -> ""
    end
  | CmdOption _ kind _ _ ->
    begin match kind with
    | OptStringOption argdesc _ _
    | OptList argdesc _ _
      -> argdesc
    | _ -> ""
    end

let set_implies (options: ref (list cmd_option)) (implies: list string) : ML unit =
  List.iter
    (fun name ->
      match find_cmd_option name !options with
      | Some (CmdOption _ (OptBool x) _ _) -> x := true
      | _ -> ()
    )
    implies

let negate_string_gen (s: string) (negation: string) =
  if s `string_starts_with` negation
  then String.sub s (String.length negation) (String.length s - String.length negation)
  else negation ^ s

let name_is_negated (s: string) : Tot bool = s `string_starts_with` "no_"
let negate_name (s: string) : Tot string = negate_string_gen s "no_"
let negate_description (s: string) : Tot string = negate_string_gen s "Do not"

let fstar_options_of_cmd_option
  (options: ref (list cmd_option))
  (o: cmd_option)
: Tot (list fstar_opt)
= match o with
  | CmdFStarOption f -> [f]
  | CmdOption name kind desc implies ->
    begin match kind with
    | OptBool v ->
      [
        ((Getopt.noshort, name, Getopt.ZeroArgs (fun _ -> set_implies options implies; v := true)), desc);
        ((Getopt.noshort, negate_name name, Getopt.ZeroArgs (fun _ -> v := false)), negate_description desc);
      ]
    | OptStringOption arg_desc valid v ->
      [
        (
          (
            Getopt.noshort, name,
            Getopt.OneArg (
              (fun (x: string) ->
                if valid x
                then begin
                  set_implies options implies;
                  v := Some x
                end else
                  failwith (Printf.sprintf "Bad argument to %s: got %s, expected %s" name x arg_desc)
              ),
              arg_desc
            )
          ),
          desc
        );
        ((Getopt.noshort, negate_name name, Getopt.ZeroArgs (fun _ -> v := None)), negate_description desc)
      ]
    | OptList arg_desc valid v ->
      [
        (
          (
            Getopt.noshort, name,
            Getopt.OneArg (
              (fun (x: string) ->
                if valid x
                then begin
                  set_implies options implies;
                  v := x :: !v
                end else
                  failwith (Printf.sprintf "Bad argument to %s: got %s, expected %s" name x arg_desc)
              ),
              arg_desc
            )
          ),
          desc
        );
        (
          (
            Getopt.noshort, negate_name name,
            Getopt.ZeroArgs (fun _ -> v := [])
          ),
          desc
        );
      ]
    end

let compute_current_options (options: ref (list cmd_option)) (ignore: list string) : ML string =
  (* we would like to output a normalized sequence of options so that its semantics does not depend on whether any other options are prepended (i.e. whether 3d is run from 3d or from everparse.cmd or from everparse.sh *)
  (* first print the values of current options except untoggled boolean options *)
  let print (msg: string) (opt: cmd_option) : ML string =
    if List.Tot.mem (cmd_option_name opt) ignore
    then msg
    else
    match opt with
    | CmdOption name kind desc implies ->
      begin match kind with
      | OptBool v ->
        if !v
        then Printf.sprintf "%s --%s" msg name
        else msg
      | OptStringOption _ _ v ->
        begin match !v with
        | None -> Printf.sprintf "%s --%s" msg (negate_name name)
        | Some v -> Printf.sprintf "%s --%s %s" msg name v
        end
      | OptList _ _ v ->
        let v = !v in
        let msg = Printf.sprintf "%s --%s" msg (negate_name name) in
        let app (msg: string) (s: string) = Printf.sprintf "%s --%s %s" msg name s in
        List.Tot.fold_left app msg (List.Tot.rev v) (* list was accumulated as a fifo *)
      end
    | _ -> msg
  in
  let msg = List.fold_left print "" !options in
  (* then print the untoggled boolean options *)
  let print_untoggle (msg: string) (opt: cmd_option) : ML string =
    match opt with
    | CmdOption name (OptBool v) _ _ ->
      if (if not (List.Tot.mem name ignore) then not !v else false)
      then Printf.sprintf "%s --%s" msg (negate_name name)
      else msg
    | _ -> msg
  in
  List.fold_left print_untoggle msg !options

let get_arg0 () : ML string =
  match !arg0 with
  | None -> "3d"
  | Some v -> v

let display_usage_1 (options: ref (list cmd_option)) : ML unit =
  FStar.IO.print_string "EverParse/3d: verified data validation with dependent data descriptions\n";
  FStar.IO.print_string "\n";
  FStar.IO.print_string (Printf.sprintf "Usage: %s [options] path_to_input_file1.3d path_to_input_file2.3d ... \n" (get_arg0 ()));
  FStar.IO.print_string "\n";
  FStar.IO.print_string "Options:\n";
  List.iter
    (fun x ->
      let m = cmd_option_name x in
      let desc = cmd_option_description x in
      let argdesc = cmd_option_arg_desc x in
      let argdesc = if argdesc = "" then "" else Printf.sprintf " <%s>" argdesc in
      let negate = if CmdOption? x then Printf.sprintf " (opposite is --%s)" (negate_name m) else "" in
      let visible = not (m `string_starts_with` "__") in
      if visible then FStar.IO.print_string (Printf.sprintf "--%s%s%s\n\t%s\n" m argdesc negate desc)
    )
    !options
    ;
  FStar.IO.print_string (Printf.sprintf "\nCurrent options are:%s\n" (compute_current_options options []))

let (display_usage_2, compute_options_2, fstar_options) =
  let options : ref (list cmd_option) = alloc [] in
  let display_usage () = display_usage_1 options in
  let compute_options = compute_current_options options in
  options := [
    CmdOption "add_include" (OptList "<include.h>|\"include.h\"" always_valid add_include) "Prepend #include ... to generated .c/.h files" [];
    CmdOption "batch" (OptBool batch) "Verify the generated F* code and extract C code" [];
    CmdOption "check_hashes" (OptStringOption "weak|strong|inplace" valid_check_hashes check_hashes) "Check hashes" ["batch"];
    CmdOption "check_inplace_hash" (OptList "file.3d=file.h" always_valid inplace_hashes) "Check hashes stored in one .h/.c file" [];
    CmdOption "clang_format" (OptBool clang_format) "Call clang-format on extracted .c/.h files (--batch only)" ["batch"];
    CmdOption "clang_format_executable" (OptStringOption "clang-format full path" always_valid clang_format_executable) "Set the path to clang-format if not reachable through PATH" ["batch"; "clang_format"];
    CmdOption "cleanup" (OptBool cleanup) "Remove *.fst*, *.krml and krml-args.rsp (--batch only)" [];
    CmdOption "config" (OptStringOption "config file" check_config_file_name config_file) "The name of a JSON formatted file containing configuration options" [];    
    CmdOption "emit_output_types_defs" (OptBool emit_output_types_defs) "Emit definitions of output types in a .h file" [];
    CmdOption "emit_smt_encoding" (OptBool emit_smt_encoding) "Emit an SMT encoding of parser specifications" [];
    CmdOption "fstar" (OptStringOption "executable" always_valid fstar_exe) "The F* command to run. Default: 'fstar.exe'" [];
    CmdOption "input_stream" (OptStringOption "buffer|extern|static" valid_input_stream_binding input_stream_binding) "Input stream binding (default buffer)" [];
    CmdOption "input_stream_include" (OptStringOption ".h file" always_valid input_stream_include) "Include file defining the EverParseInputStreamBase type (only for --input_stream extern or static)" [];
    CmdOption "no_copy_everparse_h" (OptBool no_copy_everparse_h) "Do not Copy EverParse.h (--batch only)" [];
    CmdOption "debug" (OptBool debug) "Emit a lot of debugging output" [];
    CmdFStarOption (('h', "help", Getopt.ZeroArgs (fun _ -> display_usage (); exit 0)), "Show this help message");
    CmdOption "json" (OptBool json) "Dump the AST in JSON format" [];
    CmdOption "makefile" (OptStringOption "gmake|nmake" valid_makefile makefile) "Do not produce anything, other than a Makefile to produce everything" [];
    CmdOption "makefile_name" (OptStringOption "some file name" always_valid makefile_name) "Name of the Makefile to produce (with --makefile, default <output directory>/EverParse.Makefile" [];
    CmdOption "odir" (OptStringOption "output directory" always_valid output_dir) "output directory (default '.'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory" [];
    CmdOption "save_hashes" (OptBool save_hashes) "Save hashes" [];
    CmdOption "save_z3_transcript" (OptStringOption "some file name" always_valid save_z3_transcript) "Save the Z3 transcript (input and output) to a file" [];
    CmdOption "skip_c_makefiles" (OptBool skip_c_makefiles) "Do not Generate Makefile.basic, Makefile.include" [];
    CmdOption "skip_o_rules" (OptBool skip_o_rules) "With --makefile, do not generate rules for .o files" [];
    CmdOption "test_checker" (OptStringOption "parser name" always_valid test_checker) "produce a test checker executable" [];
    CmdFStarOption ((let open Getopt in noshort, "version", ZeroArgs (fun _ -> FStar.IO.print_string (Printf.sprintf "EverParse/3d %s\nCopyright 2018, 2019, 2020 Microsoft Corporation\n" Version.everparse_version); exit 0)), "Show this version of EverParse");
    CmdOption "equate_types" (OptList "an argument of the form A,B, to generate asserts of the form (A.t == B.t)" valid_equate_types equate_types_list) "Takes an argument of the form A,B and then for each entrypoint definition in B, it generates an assert (A.t == B.t) in the B.Types file, useful when refactoring specs, you can provide multiple equate_types on the command line" [];
    CmdOption "z3_branch_depth" (OptStringOption "nb" always_valid z3_branch_depth) "enumerate branch choices up to depth nb (default 0)" [];
    CmdOption "z3_diff_test" (OptStringOption "parser1,parser2" valid_equate_types z3_diff_test) "produce differential tests for two parsers" [];
    CmdOption "z3_executable" (OptStringOption "path/to/z3" always_valid z3_executable) "z3 executable for test case generation (default `z3`; does not affect verification of generated F* code)" [];
    CmdOption "z3_options" (OptStringOption "'options to z3'" always_valid z3_options) "command-line options to pass to z3 for test case generation (does not affect verification of generated F* code)" [];
    CmdOption "z3_test" (OptStringOption "parser name" always_valid z3_test) "produce positive and/or negative test cases for a given parser" [];
    CmdOption "z3_test_mode" (OptStringOption "pos|neg|all" valid_z3_test_mode z3_test_mode) "produce positive, negative, or all kinds of test cases (default all)" [];
    CmdOption "z3_witnesses" (OptStringOption "nb" always_valid z3_witnesses) "ask for nb distinct test witnesses per branch case (default 1)" [];
    CmdOption "__arg0" (OptStringOption "executable name" always_valid arg0) "executable name to use for the help message" [];
    CmdOption "__micro_step" (OptStringOption "verify|extract|copy_clang_format|copy_everparse_h|emit_config" valid_micro_step micro_step) "micro step" [];
    CmdOption "__produce_c_from_existing_krml" (OptBool produce_c_from_existing_krml) "produce C from .krml files" [];
    CmdOption "__skip_deps" (OptBool skip_deps) "skip dependency analysis, assume all dependencies are specified on the command line" [];
  ];
  let fstar_options =
    List.Tot.concatMap (fstar_options_of_cmd_option options) !options
  in
  (display_usage, compute_options, fstar_options)

let display_usage = display_usage_2

let compute_options = compute_options_2

let parse_cmd_line () : ML (list string) =
  let open Getopt in
  let res = Getopt.parse_cmdline (List.Tot.map fst fstar_options) (fun file -> input_file := file :: !input_file; Success) in
  match res with
  | Success -> !input_file
  | Help -> display_usage(); exit 0
  | Error s -> FStar.IO.print_string s; exit 1
  | _ -> exit 2

let split_3d_file_name fn =
  let fn = OS.basename fn in
  if OS.extension fn = ".3d"
  then Some (OS.remove_extension fn)
  else None

let get_file_name mname = mname ^ ".3d"

let get_module_name (file: string) =
    match split_3d_file_name file with
    | Some nm ->
      if starts_with_capital nm
      then nm
      else failwith (Printf.sprintf "Input file name %s must start with a capital letter" file)
    | None -> failwith (Printf.sprintf "Input file name %s must end with .3d" file)

let get_output_dir () =
  match !output_dir with
  | None -> "."
  | Some s -> s

let debug_print_string (s:string): ML unit =
  if !debug
  then FStar.IO.print_string s
  else ()

let get_batch () =
  !batch

let get_clang_format () =
  !clang_format

let get_clang_format_executable () =
  match !clang_format_executable with
  | None -> ""
  | Some s -> s

let get_cleanup () =
  !cleanup

let get_skip_c_makefiles () =
  !skip_c_makefiles

let get_no_everparse_h () =
  !no_copy_everparse_h

let get_check_hashes () =
  if !batch then match !check_hashes with
  | None -> None
  | Some "weak" -> Some WeakHashes
  | Some "strong" -> Some StrongHashes
  | Some "inplace" -> Some InplaceHashes
  else None

let get_save_hashes () =
  !save_hashes

let get_check_inplace_hashes () =
  List.rev !inplace_hashes

let get_equate_types_list () =
  List.map
    (fun (x: valid_string valid_equate_types) ->
      let [a; b] = String.split [','] x in (a, b)
    )
    !equate_types_list

let get_micro_step _ =
  match !micro_step with
  | None -> None
  | Some "verify" -> Some MicroStepVerify
  | Some "extract" -> Some MicroStepExtract
  | Some "copy_clang_format" -> Some MicroStepCopyClangFormat
  | Some "copy_everparse_h" -> Some MicroStepCopyEverParseH
  | Some "emit_config" -> Some MicroStepEmitConfig

let get_produce_c_from_existing_krml _ =
  !produce_c_from_existing_krml

let get_skip_deps _ =
  !skip_deps

let get_makefile _ =
  match !makefile with
  | None -> None
  | Some "gmake" -> Some MakefileGMake
  | Some "nmake" -> Some MakefileNMake

let get_makefile_name _ =
  match !makefile_name with
  | None -> OS.concat (get_output_dir ()) "EverParse.Makefile"
  | Some mf -> mf

let get_skip_o_rules _ =
  !skip_o_rules

let get_json () =
  !json

let get_input_stream_binding _ =
  let get_include () =
    match !input_stream_include with
    | None -> ""
    | Some s -> s
  in
  match !input_stream_binding with
  | None
  | Some "buffer" -> InputStreamBuffer
  | Some "extern" ->
    InputStreamExtern (get_include ())
  | Some "static" ->
    InputStreamStatic (get_include ())

let get_emit_output_types_defs () = !emit_output_types_defs

let get_config_file () = 
  match !config_file with
  | None -> None
  | Some s -> Some s

let get_add_include () =
  !add_include

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
  match !config_file with
  | None -> None
  | Some s -> Some (strip_suffix (OS.basename s) ".3d.config")

let get_emit_smt_encoding () =
  !emit_smt_encoding

let get_z3_test () = !z3_test

let get_z3_pos_test () =
  match !z3_test with
  | None -> false
  | _ -> match !z3_test_mode with
  | Some "neg" -> false
  | _ -> true

let get_z3_neg_test () =
  match !z3_test with
  | None -> false
  | _ -> match !z3_test_mode with
  | Some "pos" -> false
  | _ -> true

let get_z3_witnesses () =
  match !z3_witnesses with
  | None -> 1
  | Some s ->
  try
    let n = OS.int_of_string s in
    if n < 1 then (1 <: pos) else begin
      assert (n >= 1);
      (n <: pos)
    end
  with _ -> 1

let get_debug _ = !debug

let get_z3_diff_test _ =
  match !z3_diff_test with
  | None -> None
  | Some s -> let [p1; p2] = String.split [','] s in Some (p1, p2)

let get_z3_executable () =
  match !z3_executable with
  | None -> "z3"
  | Some z3 -> z3

let get_save_z3_transcript () = !save_z3_transcript

let get_test_checker () = !test_checker

let get_z3_branch_depth () =
  match !z3_branch_depth with
  | None -> 0
  | Some s ->
  try
    let n = OS.int_of_string s in
    if n < 0 then (0 <: nat) else begin
      assert (n >= 0);
      (n <: nat)
    end
  with _ -> 0

let get_z3_options () : ML string = 
  match !z3_options with
  | None -> ""
  | Some s -> s

let get_fstar_exe () : ML string =
  match !fstar_exe with
  | None -> "fstar.exe"
  | Some s -> s
