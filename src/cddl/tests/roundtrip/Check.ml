(* Generic check driver for the roundtrip test infrastructure.

   Per-target main_<T>.ml calls:
     Check.run [ <absolute paths to .cddl inputs> ] <Mname>.ast

   This re-runs the OCaml CDDL parser on the same inputs and compares
   its (post-solve_names, post-plug_empty_sockets) result with the
   F*-extracted constant `<Mname>.ast`. They must be structurally
   equal under OCaml polymorphic =, which works on the extracted AST
   (Prims.int = Zarith Z.t carries a custom comparator; strings,
   lists, sums and products are trivial).

   On mismatch we dump both sides via CDDL.Spec.AST.Print.program_to_string
   so a textual diff is immediately useful.
*)

let run files (expected : (string * CDDL_Spec_AST_Base.decl) list) : unit =
  match ParseFromFile.parse_from_files files with
  | None ->
     prerr_endline ("Check: parsing failed for " ^ String.concat " " files);
     exit 2
  | Some got ->
     if got = expected then begin
       print_endline "Check: OK";
       exit 0
     end else begin
       prerr_endline "Check: roundtrip mismatch.";
       prerr_endline "Expected (extracted from F*):";
       prerr_endline (CDDL_Spec_AST_Print.program_to_string expected);
       prerr_endline "Got (fresh parser run):";
       prerr_endline (CDDL_Spec_AST_Print.program_to_string got);
       exit 1
     end
