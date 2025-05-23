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

let tmpdir = ref ""

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

let run_cmd prog args =
  let cmd = Filename.quote_command prog args in
  prerr_endline ("Running: " ^ cmd);
  Sys.command cmd

let regexp_path_drive = Re.Posix.compile_pat "^[a-zA-Z]+:[\\/]"

let string_matches_regexp s r = Re.execp r s

let filename_is_relative n =
  if Filename.is_relative n
  then true
  else if Sys.cygwin
  then not (string_matches_regexp n regexp_path_drive)
  else false

let get_absolute_filename n =
  if filename_is_relative n
  then Filename.concat (Sys.getcwd ()) n
  else n

let everparse_home =
  try
    Sys.getenv "EVERPARSE_HOME"
  with
  | Not_found ->
     (* assume the executable is in the bin/ subdirectory *)
     get_absolute_filename (Filename.concat (Filename.dirname Sys.executable_name) Filename.parent_dir_name)

let fstar_exe =
  try
    Sys.getenv "FSTAR_EXE"
  with
  | Not_found ->
     let opt_fstar_exe = Filename.concat (Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "FStar") "bin") "fstar.exe" in
     if Sys.file_exists opt_fstar_exe
     then opt_fstar_exe
     else "fstar.exe" (* rely on PATH *)

let krml_home =
  try
    Sys.getenv "KRML_HOME"
  with
  | Not_found -> Filename.concat (Filename.concat everparse_home "opt") "karamel"

let pulse_home =
  try
    Sys.getenv "PULSE_HOME"
  with
  | Not_found -> Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "pulse") "out"

let z3_version = "4.8.5"

let z3_executable_option =
  let test = run_cmd fstar_exe ["--locate_z3"; z3_version] in
  if test = 0
  then []
  else
    let opt_z3 = Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "z3") ("z3-" ^ z3_version) in
    if Sys.file_exists opt_z3
    then ["--z3_executable"; opt_z3]
    else []

let include_option_of_paths =
  List.concat_map (fun l -> ["--include"; l])

let everparse_src = Filename.concat everparse_home "src"
let everparse_src_cbor = Filename.concat everparse_src "cbor"
let everparse_src_cbor_spec = Filename.concat everparse_src_cbor "spec"
let everparse_src_cbor_pulse = Filename.concat everparse_src_cbor "pulse"
let everparse_src_cddl = Filename.concat everparse_src "cddl"
let everparse_src_cddl_spec = Filename.concat everparse_src_cddl "spec"
let everparse_src_cddl_pulse = Filename.concat everparse_src_cddl "pulse"
let krml_home_krmllib = Filename.concat krml_home "krmllib"
let everparse_home_lib = Filename.concat everparse_home "lib"
let everparse_home_lib_evercddl = Filename.concat everparse_home_lib "evercddl"

let include_options =
  include_option_of_paths
    [
      everparse_src_cbor_spec;
      everparse_src_cbor_pulse;
      everparse_src_cddl_spec;
      everparse_src_cddl_pulse;
      Filename.concat everparse_src_cddl "tool";
      krml_home_krmllib;
      Filename.concat krml_home_krmllib "obj";
      Filename.concat (Filename.concat pulse_home "lib") "pulse";
      Filename.concat everparse_home_lib_evercddl "lib";
      Filename.concat everparse_home_lib_evercddl "plugin";
    ]

(* TODO: honor OTHERFLAGS. This would require implementing Bash word
   splitting, since we are using lists of arguments. *)

let fstar_options =
  z3_executable_option @
    [
      "--cache_checked_modules";
      "--warn_error"; "@241";
      "--cmi";
      "--ext"; "context_pruning";
      "--load_cmxs"; "evercddl_lib";
      "--load_cmxs"; "evercddl_plugin";
    ] @
      include_options

let _ =
  let argspec = ref [
      ("--rust", Arg.Unit (fun _ -> lang := "Rust"), "Use the Rust EverCBOR library");
      ("--mname", Arg.String (fun m -> mname := m), "Set the module name");
      ("--odir", Arg.String (fun d -> odir := d), "Set the output directory (default .)");
      ("--fstar_only", Arg.Unit (fun _ -> fstar_only := true), "Only generate F*");
      ("--tmpdir", Arg.String (fun d -> tmpdir := d), "Set the temporary directory (default automatically generated)");
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
  let dir = if !fstar_only then !odir else if !tmpdir <> "" then !tmpdir else mk_tmp_dir_name () in
  let basename = produce_fst_file dir in
  if !fstar_only then exit 0;
  let res = run_cmd fstar_exe
    (
      [
        Filename.concat dir basename;
        "--cache_dir"; dir;
        "--already_cached"; ("*,-" ^ !mname);
      ] @
        fstar_options
    )
  in
  if res <> 0
  then
    begin
      prerr_endline "Verification failed";
      exit res
    end;
  ()
