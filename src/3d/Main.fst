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

let parse_prog (fn:string) (must_have_entrypoint:bool) : ML prog =
  let decls, type_refinement_opt = ParserDriver.parse fn in
  if not must_have_entrypoint then decls, type_refinement_opt
  else if decls
          |> List.tryFind (fun d -> match d.v with
                                | Record names _ _ _
                                | CaseType names _ _ ->
                                  has_entrypoint (names.typedef_attributes)
                                | _ -> false)
          |> Some?
       then decls, type_refinement_opt
       else raise (Error (Printf.sprintf "File %s does not have an entry point definition, exiting\n" fn))

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

let translate_module (en:env) (mname:string) (fn:string) (must_have_entrypoint:bool)
  : ML (list Ast.decl &
        list Target.decl &
        StaticAssertions.static_asserts &
        env) =

  Options.debug_print_string (FStar.Printf.sprintf "Processing file: %s\nModule name: %s\n" fn mname);
  let decls, refinement = parse_prog fn must_have_entrypoint in

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

let process_file (en:env) (fn:string) (cmdline_modules:list string) : ML env =
  let modul = Options.get_module_name fn in
  let _decls, t_decls, static_asserts, en =
    translate_module en modul fn (List.mem modul cmdline_modules) in
  emit_fstar_code en modul t_decls static_asserts;
  en

let collect_and_sort_dependencies (files:list string) : ML (list string) =
  let dirname = files |> List.hd |> OS.dirname in
  let filename_of modul = Options.get_file_name (OS.concat dirname modul) in

  files
  |> List.collect Deps.get_sorted_deps
  |> List.fold_left (fun acc mod -> if List.mem mod acc then acc else mod::acc) []
  |> List.rev
  |> List.map filename_of

let process_files (files:list string) (cmdline_files:list string) : ML unit =
  IO.print_string (Printf.sprintf "Processing files: %s\n"
    (List.fold_left (fun acc fn -> Printf.sprintf "%s %s" acc fn) "" files));
  let cmdline_modules = List.map Options.get_module_name cmdline_files in
  let env = initial_env () in
  files
  |> List.fold_left (fun env fn -> process_file env fn cmdline_modules) env
  |> ignore

let go () : ML unit =
  let files = Options.parse_cmd_line() in
  let inplace_hashes = Options.get_check_inplace_hashes () in
  match inplace_hashes with
  | _ :: _ ->
    Batch.check_inplace_hashes inplace_hashes
  | [] ->
  match files with
  | [] -> Options.display_usage ()
  | _ ->
    let out_dir = Options.get_output_dir () in
    let all_files = collect_and_sort_dependencies files in
    let all_files_and_modules = List.map (fun file -> (file, Options.get_module_name file)) all_files in
  match Options.get_check_hashes () with
  | None ->
    process_files all_files files;
    if Options.get_batch ()
    then begin
      Batch.postprocess
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        (Options.get_skip_makefiles ())
        (Options.get_cleanup ())
        (Options.get_no_everparse_h ())
        (Options.get_save_hashes ())
        out_dir all_files_and_modules;
      FStar.IO.print_string "EverParse succeeded!\n"
    end
  | Some ch ->
    Batch.check_all_hashes ch out_dir all_files_and_modules

#push-options "--warn_error -272" //top-level effects are okay
#push-options "--admit_smt_queries true" //explicitly not handling all exceptions, so that we can meaningful backtraces
let _ =
  try go()
  with
    | Error msg ->
      FStar.IO.print_string msg;
      exit 1
#pop-options
