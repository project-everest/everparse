module Main
open FStar.All
open Ast
open ParserDriver
module T = Target
open FStar.ST
#push-options "--warn_error -272" //top-level effects are okay
let test =
  let files = Options.parse_cmd_line() in
  match files with
  | [fn] ->
    let decls = ParserDriver.parse fn in
    let decls, env = Binding.bind_prog decls in
    let decls = Simplify.simplify_prog env decls in
    // FStar.IO.print_string (String.concat "\n" (List.map Ast.print_decl decls));
    let t_decls = List.map Translate.translate_decl decls in

    let fst_file =
      FStar.IO.open_write_file
        (Printf.sprintf "%s/%s.fst"
          (Options.get_output_dir())
          (Options.get_module_name())) in
    FStar.IO.write_string fst_file (Target.print_decls t_decls);
    FStar.IO.close_write_file fst_file;

    let c_file =
      FStar.IO.open_write_file
        (Printf.sprintf "%s/%s_wrapper.c"
          (Options.get_output_dir())
          (Options.get_module_name())) in
    FStar.IO.write_string c_file (Target.print_c_entry t_decls);
    FStar.IO.close_write_file c_file

  | _ ->
    List.iter (fun x -> FStar.IO.print_string x) files;
    failwith "Not enough arguments"
