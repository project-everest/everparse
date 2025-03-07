module Main
open FStar.IO
open FStar.All
open Ast
open ParserDriver
module T = Target
open FStar.ST
#push-options "--z3rlimit_factor 2"

let open_write_file (s:string) : ML FStar.IO.fd_write =
  FStar.IO.print_string (FStar.Printf.sprintf "Writing file %s\n" s);
  FStar.IO.open_write_file s

let parse_prog (fn:string) : ML prog =
  let decls, type_refinement_opt = ParserDriver.parse fn in
  if decls
     |> List.tryFind is_entrypoint_or_export
     |> Some?
  then decls, type_refinement_opt
  else raise (Error (Printf.sprintf "File %s does not have an entry point or an exported definition, exiting\n" fn))

noeq
type env = {
  binding_env : Binding.global_env;
  typesizes_env : TypeSizes.size_env;
  translate_env : (TranslateForInterpreter.translate_env & InterpreterTarget.env);
}

let initial_env () : ML env = {
  binding_env = Binding.initial_global_env ();
  typesizes_env = TypeSizes.initial_senv ();
  translate_env = 
    (TranslateForInterpreter.initial_translate_env(), InterpreterTarget.create_env());
}

let left (x:either 'a 'b)
  : ML 'a
  = match x with
    | Inl x -> x
    | _ -> failwith "Expected left"

let right (x:either 'a 'b)
  : ML 'b
  = match x with
    | Inr x -> x
    | _ -> failwith "Expected right"

let parse_check_and_desugar (en:env) (mname:string) (fn:string)
  : ML (list Ast.decl &
        StaticAssertions.static_asserts &
        env) =
  Options.debug_print_string (FStar.Printf.sprintf "Processing file: %s\nModule name: %s\n" fn mname);
  let decls, refinement =
    parse_prog fn
  in

  Options.debug_print_string "=============After parsing=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls, refinement = Desugar.desugar en.binding_env mname (decls, refinement) in

  Options.debug_print_string "=============After desugaring=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls, benv = Binding.bind_decls en.binding_env decls in

  Options.debug_print_string "=============After binding=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  if Options.get_json()
  then (
    IO.print_string (JSON.prog_to_json (decls, refinement));
    IO.print_string "\n"
  );
  
  let decls = BitFields.eliminate_decls benv decls in
  
  Options.debug_print_string "=============After bitflds=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";
  
  let decls = TypeSizes.size_of_decls benv en.typesizes_env decls in

  Options.debug_print_string "=============Finished typesizes pass=============\n";

  let static_asserts = StaticAssertions.compute_static_asserts benv en.typesizes_env refinement in

  Options.debug_print_string "=============Finished static asserts pass=============\n";

  let decls = Simplify.simplify_prog benv en.typesizes_env decls in
  
  Options.debug_print_string "=============After simplify============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls = InlineSingletonRecords.simplify_prog decls in
  
  Options.debug_print_string "=============After inline singletons============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let en = {
    en with 
      binding_env = benv
  } in
  decls,
  static_asserts,
  en
  
let translate_module (en:env) (mname:string) (fn:string)
  : ML (list Target.decl &
        list InterpreterTarget.decl &
        StaticAssertions.static_asserts &
        env) =

  let decls, static_asserts, en = 
      parse_check_and_desugar en mname fn
  in      
      
  let t_decls, i_decls, tenv = 
      let env, env' = en.translate_env in
      let decls, env =
        TranslateForInterpreter.translate_decls en.binding_env en.typesizes_env env decls
      in
      let tds = InterpreterTarget.translate_decls env' decls in
      decls, tds, (env, env')
  in
  let en = { en with translate_env = tenv } in
  t_decls,
  i_decls,
  static_asserts,
  en

let emit_fstar_code_for_interpreter (en:env)
                                    (modul:string)
                                    (tds:list T.decl)
                                    (itds:list InterpreterTarget.decl)
                                    (all_modules:list string)
  : ML unit
  = let _, en = en.translate_env in
    
    let impl, iface =
        InterpreterTarget.print_decls en modul itds
    in

    let has_external_types = T.has_output_types tds || T.has_extern_types tds in

    if has_external_types
    then begin
      let external_types_fsti_file =
        open_write_file
          (Printf.sprintf "%s/%s.ExternalTypes.fsti" (Options.get_output_dir ()) modul) in
      FStar.IO.write_string external_types_fsti_file (Target.print_external_types_fstar_interpreter modul tds);
      FStar.IO.close_write_file external_types_fsti_file
    end;

    let has_external_api = T.has_external_api tds in

    if has_external_api
    then begin
      let external_api_fsti_file =
        open_write_file
          (Printf.sprintf "%s/%s.ExternalAPI.fsti" (Options.get_output_dir ()) modul) in
      FStar.IO.write_string external_api_fsti_file (Target.print_external_api_fstar_interpreter modul tds);
      FStar.IO.close_write_file external_api_fsti_file
    end;
 
    let maybe_open_external_api =
      if has_external_api
      then Printf.sprintf "open %s.ExternalAPI" modul
      else ""
    in
 
    let module_prefix = 
       FStar.Printf.sprintf "module %s\n\
                             open EverParse3d.Prelude\n\
                             open EverParse3d.Actions.All\n\
                             open EverParse3d.Interpreter\n\
                             %s\n\
                             module T = FStar.Tactics\n\
                             module A = EverParse3d.Actions.All\n\
                             module P = EverParse3d.Prelude\n\
                             #set-options \"--fuel 0 --ifuel 0 --ext context_pruning\"\n"
                             modul maybe_open_external_api
    in

    let fst_file =
      open_write_file
        (Printf.sprintf "%s/%s.fst"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string fst_file module_prefix;
    FStar.IO.write_string fst_file impl;    
    FStar.IO.close_write_file fst_file;
                             
    let fsti_file =
      open_write_file
        (Printf.sprintf "%s/%s.fsti"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string fsti_file module_prefix;
    FStar.IO.write_string fsti_file iface;
    FStar.IO.close_write_file fsti_file;

    ()
   
let emit_entrypoint (produce_ep_error: Target.opt_produce_everparse_error)
                    (en:env) (modul:string) (t_decls:list Target.decl)
                    (static_asserts:StaticAssertions.static_asserts)
                    (emit_output_types_defs:bool)
  : ML unit =
  //print wrapper only if there is an entrypoint
  if List.tryFind (fun (d, _) ->
    let open Target in
    match d with
    | Type_decl td -> td.decl_name.td_entrypoint
    | _ -> false) t_decls |> Some?
  then begin
    let wrapper_header, wrapper_impl = Target.print_c_entry produce_ep_error modul en.binding_env t_decls in

    let c_file =
      open_write_file
        (Printf.sprintf "%s/%sWrapper.c"
          (Options.get_output_dir())
          modul) in
          
    FStar.IO.write_string c_file wrapper_impl;
    FStar.IO.close_write_file c_file;

    let h_file =
      open_write_file
        (Printf.sprintf "%s/%sWrapper.h"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string h_file wrapper_header;
    FStar.IO.close_write_file h_file
  end;

  let has_output_types = T.has_output_types t_decls in
  let has_out_exprs = T.has_output_type_exprs t_decls in
  let has_extern_types = T.has_extern_types t_decls in
  
  (*
   * If there are output types in the module
   *   and emit_output_types_defs flag is set,
   *   then emit output type definitions in M_OutputTypesDefs.h
   *)

  if emit_output_types_defs
  then begin
    if has_output_types
    then begin
      let output_types_defs_file = open_write_file
        (Printf.sprintf "%s/%s_OutputTypesDefs.h"
           (Options.get_output_dir ())
           modul) in
      FStar.IO.write_string output_types_defs_file (Target.print_output_types_defs modul t_decls);
      FStar.IO.close_write_file output_types_defs_file
    end;

    (*
     * Optimization: If the module has no extern types,
     *   then M_ExternalTypedefs.h, that we require the programmer to provide,
     *   only contains output type defs
     *
     * So generate M_ExteralTypedefs.h, with #include of M_OutputTypesDefs.h
     *)

    if has_output_types && not has_extern_types
    then begin
      let extern_typedefs_file = open_write_file
        (Printf.sprintf "%s/%s_ExternalTypedefs.h"
          (Options.get_output_dir ())
          modul) in
      FStar.IO.write_string extern_typedefs_file
        (Printf.sprintf
          "#ifndef __%s_ExternalTypedefs_H\n\
           #define __%s_ExternalTypedefs_H\n
           #if defined(__cplusplus)\n\
           extern \"C\" {\n\
           #endif\n\n\n\
           %s#include \"%s_OutputTypesDefs.h\"\n\n\
           #if defined(__cplusplus)\n\
           }\n\
           #endif\n\n\
           #define __%s_ExternalTypedefs_H_DEFINED\n\
           #endif\n"

          modul
          modul
          (Options.make_includes ())
          modul
          modul);
      FStar.IO.close_write_file extern_typedefs_file
    end
  end;

  // (*
  //  * Optimization: If M only has extern functions, and no types,
  //  *   then the external typedefs file is trivially empty
  //  *)

  // if has_extern_fns && not (has_out_exprs || has_extern_types)
  // then begin
  //   let extern_typedefs_file = open_write_file
  //     (Printf.sprintf "%s/%s_ExternalTypedefs.h"
  //       (Options.get_output_dir ())
  //       modul) in
  //   FStar.IO.write_string extern_typedefs_file "\n";
  //   FStar.IO.close_write_file extern_typedefs_file
  // end;

  if has_out_exprs
  then begin
    let output_types_c_file =
      open_write_file
        (Printf.sprintf "%s/%s_OutputTypes.c" (Options.get_output_dir ()) modul) in
    FStar.IO.write_string output_types_c_file (Target.print_out_exprs_c modul t_decls);
    FStar.IO.close_write_file output_types_c_file
  end;

  if StaticAssertions.has_static_asserts static_asserts then begin
    let c_static_asserts_file =
      open_write_file
        (Printf.sprintf "%s/%sStaticAssertions.c"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string c_static_asserts_file (StaticAssertions.print_static_asserts static_asserts);
    FStar.IO.close_write_file c_static_asserts_file
  end

let process_file_gen
                 (produce_ep_error: Target.opt_produce_everparse_error)
                 (en:env)
                 (fn:string)
                 (modul:string)
                 (emit_fstar:bool)
                 (emit_output_types_defs:bool)
                 (all_modules:list string)
  : ML (env & list InterpreterTarget.decl) =
  
  let t_decls, interpreter_decls, static_asserts, en =
      translate_module en modul fn
  in
  if emit_fstar 
  then (
    emit_fstar_code_for_interpreter en modul t_decls interpreter_decls all_modules;
    emit_entrypoint produce_ep_error en modul t_decls static_asserts emit_output_types_defs
  )
  else IO.print_string (Printf.sprintf "Not emitting F* code for %s\n" fn);

  let ds = Binding.get_exported_decls en.binding_env modul in
  TypeSizes.finish_module en.typesizes_env modul ds;

  { en with 
    binding_env = Binding.finish_module en.binding_env modul;
    translate_env = 
      en.translate_env;
  }, interpreter_decls

let process_file
                 (en:env)
                 (fn:string)
                 (modul:string)
                 (emit_fstar:bool)
                 (emit_output_types_defs: bool)
                 (all_modules:list string)
  : ML env =
  fst (process_file_gen None en fn modul emit_fstar emit_output_types_defs all_modules)

let emit_config_as_fstar_module ()
  : ML unit
  = match Deps.get_config () with
    | Some (cfg, config_module_name) ->
      let fst_file_contents = Config.emit_config_as_fstar_module config_module_name cfg in
      let fst_file =
        open_write_file
          (Printf.sprintf "%s/%s.fst"
            (Options.get_output_dir())
            config_module_name) in
      FStar.IO.write_string fst_file fst_file_contents;
      FStar.IO.close_write_file fst_file
    | _ -> ()
      
let process_files_gen
                  (#env: Type)
                  (initial_env: unit -> ML env)
                  (files_and_modules:list (string & string))
                  (emit_fstar:option (string -> ML bool))
                  (emit_output_types_defs:bool)
                  (process_file: (env -> string -> string -> bool -> bool -> list string -> ML env))
  : ML env =
  
  IO.print_string 
    (Printf.sprintf "Processing files: %s\n"
                    (List.map fst files_and_modules |> String.concat " "));
  let all_modules = List.map snd files_and_modules in
  let env = initial_env () in
  if Some? emit_fstar then
    if Options.get_batch() then emit_config_as_fstar_module();
  files_and_modules
  |> List.fold_left (fun env (fn, modul) ->
                    process_file env fn modul (match emit_fstar with Some f -> f modul | _ -> false) emit_output_types_defs all_modules) env

let process_files_t =
  (files_and_modules:list (string & string)) ->
  (emit_fstar:string -> ML bool) ->
  (emit_output_types_defs:bool) ->
  ML (option (unit -> ML unit))
  
let process_files : process_files_t = fun files_and_modules emit_fstar emit_output_types_defs ->
  process_files_gen
    initial_env
    files_and_modules
    (Some emit_fstar)
    emit_output_types_defs
    process_file
  |> ignore;
  (Some (fun _ -> ()))

let process_file_for_z3
                 (out: string -> ML unit)
                 (en_accu:(env & Z3TestGen.prog))
                 (fn:string)
                 (modul:string)
                 (emit_fstar:bool)
                 (emit_output_types_defs:bool)
                 (all_modules:list string)
  : ML (env & Z3TestGen.prog) =
  let (en, accu) = en_accu in
  let (en, interpreter_decls) = process_file_gen (Some Target.ProduceEverParseError) en fn modul emit_fstar emit_output_types_defs all_modules in
  let accu = Z3TestGen.produce_decls out accu interpreter_decls in
  (en, accu)

let process_files_for_z3
                  (out: string -> ML unit)
                  (files_and_modules:list (string & string))
                  (emit_fstar:option (string -> ML bool))
                  (emit_output_types_defs:bool)
  : ML Z3TestGen.prog =
  out Z3TestGen.prelude;
  process_files_gen
    (fun _ -> initial_env (), [])
    files_and_modules
    emit_fstar
    emit_output_types_defs
    (process_file_for_z3 out)
  |> snd

let produce_z3
  (files_and_modules:list (string & string))
: ML unit
= ignore (process_files_for_z3 FStar.IO.print_string files_and_modules None false)

let build_test_exe
  (out_dir: string)
: ML unit
=
  if not (Options.get_skip_c_makefiles ())
  then begin
    OS.run_cmd "make" ["-C"; out_dir; "-f"; "Makefile.basic"; "USER_TARGET=test.exe"; "USER_CFLAGS=-Wno-type-limits"]
  end

let build_and_run_test_exe
  (out_dir: string)
: ML unit
=
  if not (Options.get_skip_c_makefiles ())
  then begin
    build_test_exe out_dir;
    OS.run_cmd (OS.concat out_dir "test.exe") []
  end

let with_z3_thread_or
  (batch_and_produce_testcases_c: bool)
  (out_dir: string)
  (debug: bool)
  (transcript: option string)
  (f: (Z3.z3 -> ML unit))
: ML (option (unit -> ML unit))
= if batch_and_produce_testcases_c
  then
    let thr = Z3.with_z3_thread debug transcript f in
    Some (fun _ ->
      Z3.wait_for_z3_thread thr;
      build_and_run_test_exe out_dir
    )
  else begin
    Z3.with_z3 debug transcript f;
    None
  end

let testcases_c_file
  (out_dir: string)
: Tot string
= (OS.concat out_dir "testcases.c")

let produce_z3_and_test_gen
  (batch: bool)
  (produce_testcases_c: bool)
  (out_dir: string)
  (do_test: option string -> int -> Z3TestGen.prog -> Z3.z3 -> ML unit)
: Tot process_files_t
= fun
  (files_and_modules:list (string & string))
  (emit_fstar:string -> ML bool)
  (emit_output_types_defs:bool)
->
  let nbwitnesses = Options.get_z3_witnesses () in
  let testcases_c = testcases_c_file out_dir in
  if produce_testcases_c then OS.overwrite_file testcases_c; // because Batch.krml_args will add the testcase file only if it exists, so we need to create it before generating the parser, otherwise we might have a race
  let buf : ref string = alloc "" in
  let prog = process_files_for_z3 (fun s -> buf := !buf ^ s) files_and_modules (if batch then Some emit_fstar else None) emit_output_types_defs in
  with_z3_thread_or (batch && produce_testcases_c) out_dir (Options.get_debug ()) (Options.get_save_z3_transcript ()) (fun z3 ->
    z3.to_z3 !buf;
    do_test (if produce_testcases_c then Some testcases_c else None) nbwitnesses prog z3
  )

let produce_z3_and_test
  (batch: bool)
  (produce_testcases_c: bool)
  (out_dir: string)
  (name: string)
: Tot process_files_t
= produce_z3_and_test_gen batch produce_testcases_c out_dir (fun out_file nbwitnesses prog z3 ->
    Z3TestGen.do_test out_dir out_file z3 prog name nbwitnesses (Options.get_z3_branch_depth ()) (Options.get_z3_pos_test ()) (Options.get_z3_neg_test ())
  )

let produce_z3_and_diff_test
  (batch: bool)
  (produce_testcases_c: bool)
  (out_dir: string)
  (names: (string & string))
: Tot process_files_t
=
  let (name1, name2) = names in
  produce_z3_and_test_gen batch produce_testcases_c out_dir (fun out_file nbwitnesses prog z3 ->
    Z3TestGen.do_diff_test out_dir out_file z3 prog name1 name2 nbwitnesses (Options.get_z3_branch_depth ())
  )

let produce_test_checker_exe
  (batch: bool)
  (out_dir: string)
  (name1: string)
: Tot process_files_t
= fun
  (files_and_modules:list (string & string))
  (emit_fstar:string -> ML bool)
  (emit_output_types_defs:bool)
->
  let testcases_c = testcases_c_file out_dir in
  OS.overwrite_file testcases_c; // because Batch.krml_args will add the testcase file only if it exists, so we need to create it before generating the parser, otherwise we might have a race
  let prog = process_files_for_z3 (fun _ -> ()) files_and_modules (if batch then Some emit_fstar else None) emit_output_types_defs in
  Z3TestGen.produce_test_checker_exe testcases_c prog name1;
  Some (fun _ ->
    if batch then
    build_test_exe out_dir
  )

let produce_and_postprocess_c
  (out_dir: string)
  (file: string)
: ML unit
=
  let modul = Options.get_module_name file in
  let deps = Deps.collect_and_sort_dependencies [file] in
  let dep_files_and_modules = List.map (fun f -> (f, Options.get_module_name f)) deps in
  (* remove the current module from the deps *)
  let dep_files_and_modules = List.filter (fun (_, m) -> m <> modul) dep_files_and_modules in
  Batch.produce_and_postprocess_one_c
    (Options.get_input_stream_binding ())
    (Options.get_emit_output_types_defs ())
    (Options.get_add_include ())
    (Options.get_clang_format ())
    (Options.get_clang_format_executable ())
    out_dir
    file
    modul
    dep_files_and_modules

let go () : ML unit =
  (* Parse command-line options. This action is only accumulating values into globals, without any further action (other than --help and --version, which interrupt the execution.) *)
  let cmd_line_files = Options.parse_cmd_line() in
  let cfg_opt = Deps.get_config () in
  (* Special mode: --check_inplace_hashes *)
  let inplace_hashes = Options.get_check_inplace_hashes () in
  if Cons? inplace_hashes
  then Batch.check_inplace_hashes inplace_hashes
  else
  let micro_step = Options.get_micro_step () in
  if micro_step = Some HashingOptions.MicroStepEmitConfig
  then (
    emit_config_as_fstar_module ();
    exit 0
  )
  else
  if micro_step = Some HashingOptions.MicroStepCopyClangFormat
  then
  (* Special mode: --__micro_step copy_clang_format *)
    let _ = Batch.copy_clang_format (Options.get_output_dir ()) in
    exit 0
  else
  if micro_step = Some HashingOptions.MicroStepCopyEverParseH
  then
  (* Special mode: --__micro_step copy_everparse_h *)
    let _ = Batch.copy_everparse_h
      (Options.get_clang_format ())
      (Options.get_clang_format_executable ())
      (Options.get_input_stream_binding ())
      (Options.get_output_dir ())
    in
    exit 0
  else
  (* for other modes, a nonempty list of files is needed on the command line, so if none are there, then we shall print the help message *)
  let input_stream_binding = Options.get_input_stream_binding () in
  if Nil? cmd_line_files
  then let _ = Options.display_usage () in exit 1
  else
  let out_dir = Options.get_output_dir () in
  (* Special mode: --__micro_step *)
  match micro_step with
  | Some step ->
    let f = match step with
    | HashingOptions.MicroStepExtract -> Batch.extract_fst_file
    | HashingOptions.MicroStepVerify -> Batch.verify_fst_file
    in
    List.iter (f (Options.get_fstar_exe ()) input_stream_binding out_dir) cmd_line_files
  | None ->
  (* Special mode: --makefile" *)
  match Options.get_makefile () with
  | Some t ->
    GenMakefile.write_makefile
      t
      input_stream_binding
      (not (Options.get_no_everparse_h ()))
      (Options.get_emit_output_types_defs ())
      (Options.get_skip_o_rules ())
      (Options.get_clang_format ())
      cmd_line_files
  | None ->
  (* Special mode: --__produce_c_from_existing_krml *)
  if Options.get_produce_c_from_existing_krml ()
  then
    let _ = List.iter
      (produce_and_postprocess_c out_dir)
      cmd_line_files
    in
    FStar.IO.print_string "EverParse succeeded!\n"
  else
  (* for other modes, the list of files provided on the command line is assumed to be a list of .3d files, and the list of all .3d files in dependency order has to be inferred from the list of .3d input files provided by the user, unless --__skip_deps is provided *)
  let all_files =
    if Options.get_skip_deps ()
    then List.Tot.rev cmd_line_files (* files are accumulated in reverse on the command line *)
    else Deps.collect_and_sort_dependencies cmd_line_files
  in
  let all_files_and_modules = List.map (fun file -> (file, Options.get_module_name file)) all_files in
  (* Special mode: --check_hashes *)
  let check_hashes = Options.get_check_hashes () in
  if Some? check_hashes
  then Batch.check_all_hashes (Some?.v check_hashes) out_dir all_files_and_modules
  else
  (* Special mode: --emit_smt_encoding *)
  if Options.get_emit_smt_encoding ()
  then produce_z3 all_files_and_modules
  else
  (* Default mode: process .3d files *)
  let batch = Options.get_batch () in
  let should_emit_fstar_code : string -> ML bool =
    let cmd_line_modules = List.map Options.get_module_name cmd_line_files in
    fun modul ->
      batch || List.Tot.mem modul cmd_line_modules in
  let process : process_files_t =
    (* Special mode: --test_checker *)
    let test_checker = Options.get_test_checker () in
    if Some? test_checker
    then produce_test_checker_exe batch out_dir (Some?.v test_checker)
    else
    (* Special mode: --z3_diff_test *)
    let z3_diff_test = Options.get_z3_diff_test () in
    if Some? z3_diff_test
    then produce_z3_and_diff_test batch (Options.get_produce_testcases_c ()) out_dir (Some?.v z3_diff_test)
    else
    (* Special mode: --z3_test *)
    let z3_test = Options.get_z3_test () in
    if Some? z3_test
    then produce_z3_and_test batch (Options.get_produce_testcases_c ()) out_dir (Some?.v z3_test)
    else process_files
  in
  match process all_files_and_modules should_emit_fstar_code (Options.get_emit_output_types_defs ()) with
  | None -> ()
  | Some finalize ->
  (* we need to pretty-print source modules in all cases, regardless of --batch,
     because of the Makefile scenario
   *)
   (*
    * pretty print only the modules we emitted code for
    *)
  Batch.pretty_print_source_modules (Options.get_fstar_exe ()) input_stream_binding out_dir
    (List.filter (fun (_, m) -> should_emit_fstar_code m) all_files_and_modules);
  (* Sub-mode of the default mode: --batch *)
  let _ =
  if batch
  then
  let _ = Batch.postprocess_fst
        (Options.get_fstar_exe ())
        input_stream_binding
        (Options.get_emit_output_types_defs ())
        (Options.get_add_include ())
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        (Options.get_skip_c_makefiles ())
        (Options.get_cleanup ())
        (Options.get_no_everparse_h ())
        (Options.get_save_hashes ())
        out_dir all_files_and_modules
  in
  FStar.IO.print_string "EverParse succeeded!\n"
  else
    (* If --batch is not set, then we also need to postprocess the wrappers and assertions
       (copyright header and clang-format) *)
    Batch.postprocess_wrappers
        input_stream_binding
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        out_dir all_files_and_modules
  in
  finalize ()

#push-options "--warn_error -272" //top-level effects are okay
#push-options "--admit_smt_queries true" //explicitly not handling all exceptions, so that we can meaningful backtraces
let _ =
  try go()
  with
    | Error msg ->
      FStar.IO.print_string msg;
      exit 1
#pop-options
