let rev_filenames : string list ref = ref []

let get_absolute_path name =
  if Filename.is_relative name
  then Filename.concat (Sys.getcwd ()) name
  else name

let process_file filename =
  let filename = get_absolute_path filename in
  if String.contains filename '"'
  then failwith ("ERROR: Absolute filename is " ^ filename ^ ". Filenames with \" are disallowed");
  rev_filenames := filename :: !rev_filenames;
  ()

let mname = ref "CDDLTest.Test"

let lang = ref "C"

let odir = ref "."

let list_is_empty = function
  | [] -> true
  | _ -> false

let fstar_only = ref false

let produce_fst_file (dir: string) : string =
  let filenames = List.rev !rev_filenames in
  match ParseFromFile.parse_from_files filenames with
  | None -> failwith "Parsing failed"
  | Some l ->
     let filenames_str = List.fold_left (fun accu fn -> accu ^ "\"" ^ fn ^ "\";") "" filenames in
     let str = CDDL_Tool_Gen.produce_defs_fst !mname !lang filenames_str l in
     if String.starts_with ~prefix:"Error: " str
     then failwith str
     else begin
         let basename = !mname ^ ".fst" in
         let filename = Filename.concat dir basename in
         let filename_tmp = filename ^ ".tmp" in
         if not (Sys.file_exists dir && Sys.is_directory dir) then Sys.mkdir dir 0o755;
         let ch = open_out filename_tmp in
         output_string ch str;
         close_out ch;
         Sys.rename filename_tmp filename;
         print_endline ("Success, output F* to: " ^ filename);
         basename
       end

let regexp_fractional = Re.Posix.compile_pat "\\..*"

(* NOTE: In OCaml 5.1+, this could be replaced with Filename.temp_dir *)
let mk_tmp_dir_name () =
  Filename.concat
    (Filename.get_temp_dir_name ())
    ("evercddl" ^ Re.replace_string regexp_fractional ~by:".tmp" (Float.to_string (Unix.time ())))

let _ =
  let argspec = ref [
      ("--rust", Arg.Unit (fun _ -> lang := "Rust"), "Use the Rust EverCBOR library");
      ("--mname", Arg.String (fun m -> mname := m), "Set the module name");
      ("--odir", Arg.String (fun d -> odir := d), "Set the output directory (default .)");
      ("--fstar_only", Arg.Unit (fun _ -> fstar_only := true), "Only generate F*");
    ]
  in
  let usagemsg = "EverCDDL: Produces a F* file to generate formally verified parsers and serializers from CDDL specifications.\nUsage: "^Sys.argv.(0) ^" [options] file1 [file2 ...]" in
  let help () =
    Arg.usage !argspec usagemsg;
    exit 0
  in
  argspec := ("--help", Arg.Unit help, "Display this help message") :: !argspec;
  Arg.parse !argspec process_file usagemsg;
  if list_is_empty !rev_filenames then help ();
  let dir = if !fstar_only then !odir else mk_tmp_dir_name () in
  let basename = produce_fst_file dir in
  if !fstar_only then exit 0;
  prerr_endline ("ERROR: Should implement extraction to C, Rust");
  exit 1
