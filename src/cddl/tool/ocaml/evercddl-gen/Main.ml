let rev_filenames : string list ref = ref []

let process_file filename =
  if String.contains filename '"'
  then failwith "ERROR: Filenames with \" are disallowed";
  rev_filenames := filename :: !rev_filenames;
  ()

let mname = ref "CDDLTest.Test"

let lang = ref "C"

let _ =
  let argspec = ref [
      ("--rust", Arg.Unit (fun _ -> lang := "Rust"), "Use the Rust EverCBOR library");
      ("--mname", Arg.String (fun m -> mname := m), "Set the module name");
    ]
  in
  let usagemsg = "EverCDDL: Produces a F* file to generate formally verified parsers and serializers from CDDL specifications.\nUsage: "^Sys.argv.(0) ^" [options] file1 [file2 ...]" in
  let help () =
    Arg.usage !argspec usagemsg;
    exit 0
  in
  argspec := ("--help", Arg.Unit help, "Display this help message") :: !argspec;
  Arg.parse !argspec process_file usagemsg;
  if List.is_empty !rev_filenames then help ();
  let filenames = List.rev !rev_filenames in
  match ParseFromFile.parse_from_files filenames with
  | None -> failwith "Parsing failed"
  | Some l ->
     let filenames_str = List.fold_left (fun accu fn -> accu ^ "\"" ^ fn ^ "\";") "" filenames in
     let str = CDDL_Tool_Gen.produce_defs_fst !mname !lang filenames_str l in
     if String.starts_with ~prefix:"Error: " str
     then failwith str
     else print_endline str
