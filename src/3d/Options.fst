module Options
open HashingOptions
open FStar.All
open FStar.ST
module U8 = FStar.UInt8
module OS = OS

#push-options "--warn_error -272" //top-level effects are okay

inline_for_extraction
let valid_string
  (valid: (string -> Tot bool))
: Tot Type0
= (s: string { valid s == true })

let always_valid (_: string) : Tot bool = true

let starts_with_capital (s: string) : Tot bool =
  String.length s >= 1 &&
  begin let first = String.sub s 0 1 in
    String.compare first "A" >= 0 && String.compare first "Z" <= 0
  end

let ends_with (s:string) (suffix:string) : bool =
  let l = String.length s in
  let sl = String.length suffix in
  if sl > l || sl = 0
  then false
  else let suffix' = String.sub s (l - sl) sl in
       suffix = suffix'

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

let _arg0 : ref (option vstring) = alloc None
let _add_include : ref (list vstring) = alloc []
let _batch : ref bool = alloc false
let _clang_format : ref bool = alloc false
let _clang_format_executable : ref (option vstring) = alloc None
let _cleanup : ref bool = alloc false
let _config_file : ref (option (valid_string check_config_file_name)) = alloc None
let _debug : ref bool = alloc false
let _inplace_hashes : ref (list vstring) = alloc []
let _input_file : ref (list string) = alloc []
let _json : ref bool = alloc false
let _no_copy_everparse_h : ref bool = alloc false
let _output_dir : ref (option vstring) = alloc None
let _save_hashes : ref bool = alloc false
let _save_z3_transcript: ref (option vstring) = alloc None
let _skip_c_makefiles : ref bool = alloc false
let _skip_deps: ref bool = alloc false
let _skip_o_rules: ref bool = alloc false

let valid_micro_step (str: string) : Tot bool = match str with
  | "verify"
  | "extract"
  | "copy_clang_format"
  | "copy_everparse_h"
  | "emit_config"
    -> true
  | _ -> false

let _micro_step : ref (option (valid_string valid_micro_step)) = alloc None

let _produce_c_from_existing_krml : ref bool = alloc false

let valid_makefile (str: string) : Tot bool = match str with
  | "gmake"
  | "nmake"
  -> true
  | _ -> false

let _makefile : ref (option (valid_string valid_makefile)) = alloc None
let _makefile_name : ref (option vstring) = alloc None

let valid_equate_types (str: string) : Tot bool =
     let l = String.split [','] str in
     match l with
     | [m1;m2] -> true
     | _ -> false

let _equate_types_list : ref (list (valid_string valid_equate_types)) = alloc []

let valid_check_hashes : string -> Tot bool = function
| "weak"
| "strong"
| "inplace"
  -> true
| _ -> false

let _check_hashes : ref (option (valid_string valid_check_hashes)) = alloc None

let valid_input_stream_binding : string -> Tot bool = function
| "buffer"
| "extern"
| "static"
  -> true
| _ -> false

let _input_stream_binding : ref (option (valid_string valid_input_stream_binding)) = alloc None

let _input_stream_include : ref (option vstring) = alloc None

let _emit_output_types_defs : ref bool = alloc true

let _emit_smt_encoding : ref bool = alloc false

let _z3_diff_test: ref (option (valid_string valid_equate_types)) = alloc None

let _z3_test : ref (option vstring) = alloc None

let valid_z3_test_mode : string -> Tot bool = function
| "pos"
| "neg"
| "all"
-> true
| _ -> false

let _z3_test_mode : ref (option (valid_string valid_z3_test_mode)) = alloc None

let _z3_witnesses : ref (option vstring) = alloc None

let _z3_executable : ref (option vstring) = alloc None

let _test_checker : ref (option vstring) = alloc None

let _z3_branch_depth : ref (option vstring) = alloc None

let _z3_options : ref (option vstring) = alloc None

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

module Getopt = FStarGetopt

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

let string_starts_with (big small: string) : Tot bool =
  let small_len = String.length small in
  if String.length big < small_len
  then false
  else String.sub big 0 small_len = small

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

let arg0 () : ML string =
  match !_arg0 with
  | None -> "3d"
  | Some v -> v

let display_usage_1 (options: ref (list cmd_option)) : ML unit =
  FStar.IO.print_string "EverParse/3d: verified data validation with dependent data descriptions\n";
  FStar.IO.print_string "\n";
  FStar.IO.print_string (Printf.sprintf "Usage: %s [options] path_to_input_file1.3d path_to_input_file2.3d ... \n" (arg0 ()));
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
    CmdOption "add_include" (OptList "<include.h>|\"include.h\"" always_valid _add_include) "Prepend #include ... to generated .c/.h files" [];
    CmdOption "batch" (OptBool _batch) "Verify the generated F* code and extract C code" [];
    CmdOption "check_hashes" (OptStringOption "weak|strong|inplace" valid_check_hashes _check_hashes) "Check hashes" ["batch"];
    CmdOption "check_inplace_hash" (OptList "file.3d=file.h" always_valid _inplace_hashes) "Check hashes stored in one .h/.c file" [];
    CmdOption "clang_format" (OptBool _clang_format) "Call clang-format on extracted .c/.h files (--batch only)" ["batch"];
    CmdOption "clang_format_executable" (OptStringOption "clang-format full path" always_valid _clang_format_executable) "Set the path to clang-format if not reachable through PATH" ["batch"; "clang_format"];
    CmdOption "cleanup" (OptBool _cleanup) "Remove *.fst*, *.krml and krml-args.rsp (--batch only)" [];
    CmdOption "config" (OptStringOption "config file" check_config_file_name _config_file) "The name of a JSON formatted file containing configuration options" [];    
    CmdOption "emit_output_types_defs" (OptBool _emit_output_types_defs) "Emit definitions of output types in a .h file" [];
    CmdOption "emit_smt_encoding" (OptBool _emit_smt_encoding) "Emit an SMT encoding of parser specifications" [];
    CmdOption "input_stream" (OptStringOption "buffer|extern|static" valid_input_stream_binding _input_stream_binding) "Input stream binding (default buffer)" [];
    CmdOption "input_stream_include" (OptStringOption ".h file" always_valid _input_stream_include) "Include file defining the EverParseInputStreamBase type (only for --input_stream extern or static)" [];
    CmdOption "no_copy_everparse_h" (OptBool _no_copy_everparse_h) "Do not Copy EverParse.h (--batch only)" [];
    CmdOption "debug" (OptBool _debug) "Emit a lot of debugging output" [];
    CmdFStarOption (('h', "help", Getopt.ZeroArgs (fun _ -> display_usage (); exit 0)), "Show this help message");
    CmdOption "json" (OptBool _json) "Dump the AST in JSON format" [];
    CmdOption "makefile" (OptStringOption "gmake|nmake" valid_makefile _makefile) "Do not produce anything, other than a Makefile to produce everything" [];
    CmdOption "makefile_name" (OptStringOption "some file name" always_valid _makefile_name) "Name of the Makefile to produce (with --makefile, default <output directory>/EverParse.Makefile" [];
    CmdOption "odir" (OptStringOption "output directory" always_valid _output_dir) "output directory (default '.'); writes <module_name>.fst and <module_name>_wrapper.c to the output directory" [];
    CmdOption "save_hashes" (OptBool _save_hashes) "Save hashes" [];
    CmdOption "save_z3_transcript" (OptStringOption "some file name" always_valid _save_z3_transcript) "Save the Z3 transcript (input and output) to a file" [];
    CmdOption "skip_c_makefiles" (OptBool _skip_c_makefiles) "Do not Generate Makefile.basic, Makefile.include" [];
    CmdOption "skip_o_rules" (OptBool _skip_o_rules) "With --makefile, do not generate rules for .o files" [];
    CmdOption "test_checker" (OptStringOption "parser name" always_valid _test_checker) "produce a test checker executable" [];
    CmdFStarOption ((let open Getopt in noshort, "version", ZeroArgs (fun _ -> FStar.IO.print_string (Printf.sprintf "EverParse/3d %s\nCopyright 2018, 2019, 2020 Microsoft Corporation\n" Version.everparse_version); exit 0)), "Show this version of EverParse");
    CmdOption "equate_types" (OptList "an argument of the form A,B, to generate asserts of the form (A.t == B.t)" valid_equate_types _equate_types_list) "Takes an argument of the form A,B and then for each entrypoint definition in B, it generates an assert (A.t == B.t) in the B.Types file, useful when refactoring specs, you can provide multiple equate_types on the command line" [];
    CmdOption "z3_branch_depth" (OptStringOption "nb" always_valid _z3_branch_depth) "enumerate branch choices up to depth nb (default 0)" [];
    CmdOption "z3_diff_test" (OptStringOption "parser1,parser2" valid_equate_types _z3_diff_test) "produce differential tests for two parsers" [];
    CmdOption "z3_executable" (OptStringOption "path/to/z3" always_valid _z3_executable) "z3 executable for test case generation (default `z3`; does not affect verification of generated F* code)" [];
    CmdOption "z3_options" (OptStringOption "'options to z3'" always_valid _z3_options) "command-line options to pass to z3 for test case generation (does not affect verification of generated F* code)" [];
    CmdOption "z3_test" (OptStringOption "parser name" always_valid _z3_test) "produce positive and/or negative test cases for a given parser" [];
    CmdOption "z3_test_mode" (OptStringOption "pos|neg|all" valid_z3_test_mode _z3_test_mode) "produce positive, negative, or all kinds of test cases (default all)" [];
    CmdOption "z3_witnesses" (OptStringOption "nb" always_valid _z3_witnesses) "ask for nb distinct test witnesses per branch case (default 1)" [];
    CmdOption "__arg0" (OptStringOption "executable name" always_valid _arg0) "executable name to use for the help message" [];
    CmdOption "__micro_step" (OptStringOption "verify|extract|copy_clang_format|copy_everparse_h|emit_config" valid_micro_step _micro_step) "micro step" [];
    CmdOption "__produce_c_from_existing_krml" (OptBool _produce_c_from_existing_krml) "produce C from .krml files" [];
    CmdOption "__skip_deps" (OptBool _skip_deps) "skip dependency analysis, assume all dependencies are specified on the command line" [];
  ];
  let fstar_options =
    List.Tot.concatMap (fstar_options_of_cmd_option options) !options
  in
  (display_usage, compute_options, fstar_options)

let display_usage = display_usage_2

let compute_options = compute_options_2

let parse_cmd_line () : ML (list string) =
  let open Getopt in
  let res = Getopt.parse_cmdline (List.Tot.map fst fstar_options) (fun file -> _input_file := file :: !_input_file; Success) in
  match res with
  | Success -> !_input_file
  | Help -> display_usage(); exit 0
  | Error s -> FStar.IO.print_string s; exit 1
  | _ -> exit 2

let split_3d_file_name fn =
  let fn = OS.basename fn in
  if OS.extension fn = ".3d"
  then Some (OS.remove_extension fn)
  else None

let file_name mname = mname ^ ".3d"

let module_name (file: string) =
    match split_3d_file_name file with
    | Some nm ->
      if starts_with_capital nm
      then nm
      else failwith (Printf.sprintf "Input file name %s must start with a capital letter" file)
    | None -> failwith (Printf.sprintf "Input file name %s must end with .3d" file)

let output_dir () =
  match !_output_dir with
  | None -> "."
  | Some s -> s

let debug_print_string (s:string): ML unit =
  if !_debug
  then FStar.IO.print_string s
  else ()

let batch () =
  !_batch

let clang_format () =
  !_clang_format

let clang_format_executable () =
  match !_clang_format_executable with
  | None -> ""
  | Some s -> s

let cleanup () =
  !_cleanup

let skip_c_makefiles () =
  !_skip_c_makefiles

let no_everparse_h () =
  !_no_copy_everparse_h

let check_hashes () =
  if !_batch then match !_check_hashes with
  | None -> None
  | Some "weak" -> Some WeakHashes
  | Some "strong" -> Some StrongHashes
  | Some "inplace" -> Some InplaceHashes
  else None

let save_hashes () =
  !_save_hashes

let check_inplace_hashes () =
  List.rev !_inplace_hashes

let equate_types_list () =
  List.map
    (fun (x: valid_string valid_equate_types) ->
      let [a; b] = String.split [','] x in (a, b)
    )
    !_equate_types_list

let micro_step _ =
  match !_micro_step with
  | None -> None
  | Some "verify" -> Some MicroStepVerify
  | Some "extract" -> Some MicroStepExtract
  | Some "copy_clang_format" -> Some MicroStepCopyClangFormat
  | Some "copy_everparse_h" -> Some MicroStepCopyEverParseH
  | Some "emit_config" -> Some MicroStepEmitConfig

let produce_c_from_existing_krml _ =
  !_produce_c_from_existing_krml

let skip_deps _ =
  !_skip_deps

let makefile _ =
  match !_makefile with
  | None -> None
  | Some "gmake" -> Some MakefileGMake
  | Some "nmake" -> Some MakefileNMake

let makefile_name _ =
  match !_makefile_name with
  | None -> OS.concat (output_dir ()) "EverParse.Makefile"
  | Some mf -> mf

let skip_o_rules _ =
  !_skip_o_rules

let json () =
  !_json

let input_stream_binding _ =
  let input_stream_include () =
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

let emit_output_types_defs () = !_emit_output_types_defs

let config_file () = 
  match !_config_file with
  | None -> None
  | Some s -> Some s

let add_include () =
  !_add_include

let make_includes () =
  let incs = add_include () in
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

let emit_smt_encoding () =
  !_emit_smt_encoding

let z3_test () = !_z3_test

let z3_pos_test () =
  match !_z3_test with
  | None -> false
  | _ -> match !_z3_test_mode with
  | Some "neg" -> false
  | _ -> true

let z3_neg_test () =
  match !_z3_test with
  | None -> false
  | _ -> match !_z3_test_mode with
  | Some "pos" -> false
  | _ -> true

let z3_witnesses () =
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

let debug _ = !_debug

let z3_diff_test _ =
  match !_z3_diff_test with
  | None -> None
  | Some s -> let [p1; p2] = String.split [','] s in Some (p1, p2)

let z3_executable () =
  match !_z3_executable with
  | None -> "z3"
  | Some z3 -> z3

let save_z3_transcript () = !_save_z3_transcript

let test_checker () = !_test_checker

let z3_branch_depth () =
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
