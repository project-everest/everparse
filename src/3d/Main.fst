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

let parse_prog (fn:string) : ML prog =
  let decls, type_refinement_opt = ParserDriver.parse fn in
  if decls
     |> List.tryFind (fun d -> match d.v with
                           | Record names _ _ _
                           | CaseType names _ _ ->
                             has_entrypoint (names.typedef_attributes)
                           | _ -> false)
     |> Some?
  then decls, type_refinement_opt
  else raise (Error (Printf.sprintf "File %s does not have an entry point definition, exiting\n" fn))

let process_file (fn: string) : ML unit =
    let modul = Options.get_module_name fn in
    Options.debug_print_string (FStar.Printf.sprintf "Processing file: %s\nModule name: %s\n" fn modul);
    let decls, refinement = parse_prog fn in
    Options.debug_print_string "=============After parsing=============\n";
    Options.debug_print_string (print_decls decls);
    Options.debug_print_string "\n";
    let decls = Desugar.desugar decls in
    Options.debug_print_string "=============After desugaring=============\n";
    Options.debug_print_string (print_decls decls);
    Options.debug_print_string "\n";
    let decls, env = Binding.bind_decls decls in
    Options.debug_print_string "=============After binding=============\n";
    Options.debug_print_string (print_decls decls);
    Options.debug_print_string "\n";
    let decls = BitFields.eliminate env decls in
    Options.debug_print_string "=============After bitflds=============\n";
    Options.debug_print_string (print_decls decls);
    Options.debug_print_string "\n";
    let senv = TypeSizes.size_of_decls env decls in
    let static_asserts = StaticAssertions.compute_static_asserts senv refinement in
    let decls = Simplify.simplify_prog senv decls in
    Options.debug_print_string "=============After simplify============\n";
    Options.debug_print_string (print_decls decls);
    Options.debug_print_string "\n";
    let decls = InlineSingletonRecords.simplify_prog decls in
    Options.debug_print_string "=============After inline singletons============\n";
    Options.debug_print_string (print_decls decls);
    Options.debug_print_string "\n";
    let t_decls = Translate.translate_decls env senv decls in

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

    let wrapper_header, wrapper_impl = Target.print_c_entry modul env t_decls in

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

let go () : ML unit =
  let files = Options.parse_cmd_line() in
  let inplace_hashes = Options.get_check_inplace_hashes () in
  match inplace_hashes with
  | _ :: _ ->
    Batch.check_inplace_hashes inplace_hashes
  | [] ->
  match files with
  | [] -> Options.display_usage ()
  | files ->
  let out_dir = Options.get_output_dir () in
  let files_and_modules = List.map (fun file -> (file, Options.get_module_name file)) files in
  match Options.get_check_hashes () with
  | None ->
    List.iter process_file files;
    if Options.get_batch ()
    then begin
      Batch.postprocess
        (Options.get_clang_format ())
        (Options.get_clang_format_executable ())
        (Options.get_skip_makefiles ())
        (Options.get_cleanup ())
        (Options.get_no_everparse_h ())
        (Options.get_save_hashes ())
        out_dir files_and_modules;
      FStar.IO.print_string "EverParse succeeded!\n"
    end
  | Some ch ->
    Batch.check_all_hashes ch out_dir files_and_modules

#push-options "--warn_error -272" //top-level effects are okay
#push-options "--admit_smt_queries true" //explicitly not handling all exceptions, so that we can meaningful backtraces
let _ =
  try go()
  with
    | Error msg ->
      FStar.IO.print_string msg;
      exit 1
#pop-options
