(* Helper for the roundtrip test infrastructure.

   Reads a set of .cddl files, runs the EverCDDL OCaml parser
   (ParseFromFile.parse_from_files), pretty-prints the resulting
   `program` value via CDDL.Spec.AST.Print.program_to_string, and
   writes the result as an F* module of the form:

     module <Mname>
     open CDDL.Spec.AST.Base
     let ast : program = [ ... ]
*)

let usage () =
  prerr_endline "Usage: gen_fst.exe <Mname> <odir> <file1.cddl> [file2.cddl ...]";
  exit 2

let () =
  if Array.length Sys.argv < 4 then usage ();
  let mname = Sys.argv.(1) in
  let odir  = Sys.argv.(2) in
  let cddls = Array.to_list (Array.sub Sys.argv 3 (Array.length Sys.argv - 3)) in
  match ParseFromFile.parse_from_files cddls with
  | None ->
     prerr_endline ("gen_fst: failed to parse " ^ String.concat " " cddls);
     exit 1
  | Some prog ->
     let body = CDDL_Spec_AST_Print.program_to_string prog in
     let path = Filename.concat odir (mname ^ ".fst") in
     let tmp  = path ^ ".tmp" in
     let oc = open_out tmp in
     output_string oc ("module " ^ mname ^ "\n");
     output_string oc "open CDDL.Spec.AST.Base\n";
     output_string oc ("let ast : program = " ^ body ^ "\n");
     close_out oc;
     Sys.rename tmp path;
     print_endline ("gen_fst: wrote " ^ path)
