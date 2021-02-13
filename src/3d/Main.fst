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

let has_entrypoint (l:list attribute) =
  List.tryFind (function Entrypoint -> true | _ -> false) l
  |> Some?

let is_entrypoint_or_export d = match d.d_decl.v with
  | Record names _ _ _
  | CaseType names _ _ ->
    if has_entrypoint (names.typedef_attributes)
    then true
    else d.d_exported
  | _ -> d.d_exported

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
  translate_env : Translate.translate_env
}

let initial_env () : ML env = {
  binding_env = Binding.initial_global_env ();
  typesizes_env = TypeSizes.initial_senv ();
  translate_env = Translate.initial_translate_env ();
}

let translate_module (en:env) (mname:string) (fn:string)
  : ML (list Ast.decl &
        list Target.decl &
        StaticAssertions.static_asserts &
        env) =

  Options.debug_print_string (FStar.Printf.sprintf "Processing file: %s\nModule name: %s\n" fn mname);
  let decls, refinement = parse_prog fn in

  Options.debug_print_string "=============After parsing=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls, refinement = Desugar.desugar mname (decls, refinement) in

  Options.debug_print_string "=============After desugaring=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls, benv = Binding.bind_decls en.binding_env decls in

  Options.debug_print_string "=============After binding=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls = BitFields.eliminate benv decls in
  
  Options.debug_print_string "=============After bitflds=============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";
  
  let decls, senv = TypeSizes.size_of_decls benv en.typesizes_env decls in

  let static_asserts = StaticAssertions.compute_static_asserts benv senv refinement in
  
  let decls = Simplify.simplify_prog benv senv decls in
  
  Options.debug_print_string "=============After simplify============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";

  let decls = InlineSingletonRecords.simplify_prog decls in
  
  Options.debug_print_string "=============After inline singletons============\n";
  Options.debug_print_string (print_decls decls);
  Options.debug_print_string "\n";
  
  let t_decls, tenv = Translate.translate_decls benv senv en.translate_env decls in

   decls,
   t_decls,
   static_asserts,
   { binding_env = benv;
     typesizes_env = senv;
     translate_env = tenv }

let emit_fstar_code (en:env) (modul:string) (t_decls:list Target.decl)
  (static_asserts:StaticAssertions.static_asserts)
  : ML unit =

  let types_fst_file =
    open_write_file
      (Printf.sprintf "%s/%s.Types.fst"
        (Options.get_output_dir ())
        modul) in
  FStar.IO.write_string types_fst_file (Target.print_types_decls modul t_decls);
  FStar.IO.close_write_file types_fst_file;

  let fst_file =
    open_write_file
      (Printf.sprintf "%s/%s.fst"
        (Options.get_output_dir())
        modul) in
  FStar.IO.write_string fst_file (Target.print_decls modul t_decls);
  FStar.IO.close_write_file fst_file;

  let fsti_file =
    open_write_file
      (Printf.sprintf "%s/%s.fsti"
        (Options.get_output_dir())
        modul) in
  FStar.IO.write_string fsti_file (Target.print_decls_signature modul t_decls);
  FStar.IO.close_write_file fsti_file;

  let wrapper_header, wrapper_impl = Target.print_c_entry modul en.binding_env t_decls in

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
  FStar.IO.close_write_file h_file;

  if StaticAssertions.has_static_asserts static_asserts then begin
    let c_static_asserts_file =
      open_write_file
        (Printf.sprintf "%s/%sStaticAssertions.c"
          (Options.get_output_dir())
          modul) in
    FStar.IO.write_string c_static_asserts_file (StaticAssertions.print_static_asserts static_asserts);
    FStar.IO.close_write_file c_static_asserts_file
  end

let process_file (en:env) (fn:string) : ML env =
  let modul = Options.get_module_name fn in
  let _decls, t_decls, static_asserts, en =
    translate_module en modul fn in
  emit_fstar_code en modul t_decls static_asserts;

  let ds = Binding.get_exported_decls en.binding_env modul in
  
  { binding_env = Binding.finish_module en.binding_env modul ds;
    typesizes_env = TypeSizes.finish_module en.typesizes_env modul ds;
    translate_env = Translate.finish_module en.translate_env modul ds }

let process_files (files:list string) : ML unit =
  IO.print_string (Printf.sprintf "Processing files: %s\n"
    (List.fold_left (fun acc fn -> Printf.sprintf "%s %s" acc fn) "" files));
  let env = initial_env () in
  files
  |> List.fold_left (fun env fn -> process_file env fn) env
  |> ignore

let go () : ML unit =
  (* Parse command-line options. This action is only accumulating values into globals, without any further action (other than --help and --version, which interrupt the execution.) *)
  let files = Options.parse_cmd_line() in
  (* Special mode: --check_inplace_hashes *)
  let inplace_hashes = Options.get_check_inplace_hashes () in
  if Cons? inplace_hashes
  then Batch.check_inplace_hashes inplace_hashes
  else
  (* for other modes, a nonempty list of files is needed on the command line, so if none are there, then we shall print the help message *)
  if Nil? files
  then let _ = Options.display_usage () in exit 1
  else
  let out_dir = Options.get_output_dir () in
  (* Special mode: --__micro_step *)
  match Options.get_micro_step () with
  | Some step ->
    let f = match step with
    | HashingOptions.MicroStepExtract -> Batch.extract_fst_file
    | HashingOptions.MicroStepVerify -> Batch.verify_fst_file
    in
    List.iter (f out_dir) files
  | None ->
  (* Special mode: --gnu_makefile" *)
  if Options.get_gnu_makefile ()
  then
    GenMakefile.write_gnu_makefile files
  else
  (* for other modes, the list of files provided on the command line is assumed to be a list of .3d files, and the list of all .3d files in dependency order has to be inferred from the list of .3d input files provided by the user, unless --__skip_deps is provided *)
  let all_files =
    if Options.get_skip_deps ()
    then List.Tot.rev files (* files are accumulated in reverse on the command line *)
    else Deps.collect_and_sort_dependencies files
  in
  let all_files_and_modules = List.map (fun file -> (file, Options.get_module_name file)) all_files in
  (* Special mode: --check_hashes *)
  let check_hashes = Options.get_check_hashes () in
  if Some? check_hashes
  then Batch.check_all_hashes (Some?.v check_hashes) out_dir all_files_and_modules
  else
  (* Special mode: --__produce_c_from_existing_krml *)
  if Options.get_produce_c_from_existing_krml ()
  then
    let _ = Batch.produce_and_postprocess_c
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        (Options.get_skip_makefiles ())
        (Options.get_cleanup ())
        (Options.get_no_everparse_h ())
        (Options.get_save_hashes ())
        out_dir all_files_and_modules
    in
    FStar.IO.print_string "EverParse succeeded!\n"
  else
  (* Default mode: process .3d files *)
  let _ = process_files all_files in
  (* we need to pretty-print source modules in all cases, regardless of --batch,
     because of the Makefile scenario
   *)
  let _ = Batch.pretty_print_source_modules out_dir all_files_and_modules in
  (* Sub-mode of the default mode: --batch *)
  if Options.get_batch ()
  then
  let _ = Batch.postprocess_fst
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        (Options.get_skip_makefiles ())
        (Options.get_cleanup ())
        (Options.get_no_everparse_h ())
        (Options.get_save_hashes ())
        out_dir all_files_and_modules
  in
  FStar.IO.print_string "EverParse succeeded!\n"

#push-options "--warn_error -272" //top-level effects are okay
#push-options "--admit_smt_queries true" //explicitly not handling all exceptions, so that we can meaningful backtraces
let _ =
  try go()
  with
    | Error msg ->
      FStar.IO.print_string msg;
      exit 1
#pop-options
