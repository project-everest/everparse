let rev_filenames : string list ref = ref []

let process_file filename =
  if String.contains filename '"'
  then failwith "ERROR: Filenames with \" are disallowed";
  rev_filenames := filename :: !rev_filenames;
  ()

let mname = ref "CDDLTest.Test"

let lang = ref "C"

let _ =
  Arg.parse [] process_file "Usage: %0 [file1 ...]";
  let filenames = List.rev !rev_filenames in
  match ParseFromFile.parse_from_files filenames with
  | None -> failwith "Parsing failed"
  | Some l ->
     let filenames_str = List.fold_left (fun accu fn -> accu ^ "\"" ^ fn ^ "\";") "" filenames in
     let str = CDDL_Tool_Gen.produce_defs_fst !mname !lang filenames_str l in
     if String.starts_with ~prefix:"Error: " str
     then failwith str
     else print_endline str
