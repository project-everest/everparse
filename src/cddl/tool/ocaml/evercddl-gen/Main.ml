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

let mkdir dir =
  if Sys.file_exists dir && Sys.is_directory dir
  then ()
  else try Sys.mkdir dir 0o755 with _ -> ()

let produce_fst_file (dir: string) : string =
  let filenames = List.rev !rev_filenames in
  match ParseFromFile.parse_from_files filenames with
  | None -> failwith "Parsing failed"
  | Some l ->
     let filenames_str = List.fold_left (fun accu fn -> accu ^ "\"" ^ fn ^ "\";") "" filenames in
     let str = CDDL_Tool_Gen.produce_defs_fst !mname !lang filenames_str l in
     if String.starts_with ~prefix:"Error: " str
     then begin
         print_endline str;
         failwith "Failure"
       end
     else begin
         let basename = !mname ^ ".fst" in
         let filename = Filename.concat dir basename in
         let filename_tmp = filename ^ ".tmp" in
         mkdir dir;
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
    ("evercddl_" ^ string_of_int (Unix.getpid ()) ^ "_" ^ Re.replace_string regexp_fractional ~by:".tmp" (Float.to_string (Unix.time ())))

let run_cmd ?silent:(silent=false) prog args =
  let f = Filename.quote_command prog in
  let cmd = if silent then f ~stdout:Filename.null ~stderr:Filename.null args else f args in (* FIXME: can we avoid repeating `args`? *)
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
     else
       (* assume a binary package *)
       let fstar_exe = Filename.concat (Filename.concat everparse_home "bin") "fstar.exe" in
       if Sys.file_exists fstar_exe
       then fstar_exe
       else "fstar.exe" (* rely on PATH *)

let krml_home =
  try
    Sys.getenv "KRML_HOME"
  with
  | Not_found ->
     let opt_krml = Filename.concat (Filename.concat everparse_home "opt") "karamel" in
     if Sys.file_exists opt_krml
     then opt_krml
     else
       (* assume a binary package *)
       everparse_home

let _ = Unix.putenv "KRML_HOME" krml_home

let krml_exe =
  let krml = "krml" ^ (if Sys.cygwin then ".exe" else "") in
  let res1 = Filename.concat krml_home krml in
  if Sys.file_exists res1
  then res1
  else Filename.concat (Filename.concat krml_home "bin") krml

let pulse_home =
  try
    Sys.getenv "PULSE_HOME"
  with
  | Not_found ->
     let opt_pulse = Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "pulse") "out" in
     if Sys.file_exists opt_pulse
     then opt_pulse
     else
       (* assume a binary package *)
       everparse_home

let z3_version = "4.13.3"

let z3_executable_option =
  let test = run_cmd ~silent:true fstar_exe ["--locate_z3"; z3_version] in
  if test = 0
  then ["--z3version"; z3_version]
  else
    let opt_z3 = Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "z3") ("z3-" ^ z3_version) in
    if Sys.file_exists opt_z3
    then ["--smt"; opt_z3]
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
let everparse_src_cddl_tool = Filename.concat everparse_src_cddl "tool"
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
      everparse_src_cddl_tool;
      krml_home_krmllib;
      Filename.concat krml_home_krmllib "obj";
      Filename.concat (Filename.concat pulse_home "lib") "pulse";
      Filename.concat everparse_home_lib_evercddl "lib";
      Filename.concat everparse_home_lib_evercddl "plugin";
    ]

let everparse_src_cbor_spec_raw = Filename.concat everparse_src_cbor_spec "raw"
let everparse_src_cbor_pulse_raw = Filename.concat everparse_src_cbor_pulse "raw"
let everparse_src_lowparse = Filename.concat everparse_src "lowparse"

let include_options_for_rust =
  include_option_of_paths
    [
      everparse_src_cbor_spec_raw;
      Filename.concat everparse_src_cbor_spec_raw "everparse";
      everparse_src_cbor_pulse_raw;
      Filename.concat everparse_src_cbor_pulse_raw "everparse";
      everparse_src_lowparse;
      Filename.concat everparse_src_lowparse "pulse";
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

let admit = ref false

let is_rust () = !lang = "Rust"

let regexp_period = Re.Posix.compile_pat "[.]"

let load_krml_list dir file =
  let res = ref [] in
  let ch = open_in (Filename.concat dir file) in
  let rec aux () =
    match
      try
        Some (input_line ch)
      with End_of_file -> None
    with
    | Some ln ->
       res := Filename.concat dir ln :: !res;
       aux ()
    | None ->
       close_in ch;
       !res
  in
  aux ()

let c_krml_list =
  load_krml_list
    (Filename.concat everparse_src_cddl_tool "extraction-c")
    "c.lst"

let rust_krml_list =
  load_krml_list
    (Filename.concat everparse_src_cddl_tool "extraction-rust")
    "rust.lst"

let skip_compilation = ref false

let _ =
  let argspec = ref [
      ("--admit", Arg.Unit (fun _ -> admit := true), "Admit proofs");
      ("--rust", Arg.Unit (fun _ -> lang := "Rust"), "Produce Rust code; use the EverCDDL F* interface for Rust extraction.");
      ("--mname", Arg.String (fun m -> mname := m), "Set the module name");
      ("--odir", Arg.String (fun d -> odir := d), "Set the output directory (default .)");
      ("--fstar_only", Arg.Unit (fun _ -> fstar_only := true), "Only generate F*");
      ("--skip_compilation", Arg.Unit (fun _ -> skip_compilation := true), "Do not compile produced C files");
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
  if (not !fstar_only) && is_rust () && string_matches_regexp !mname regexp_period then
    begin
      prerr_endline ("ERROR: Module name " ^ !mname ^ " contains a period. This has unintended consequences for Rust code generation. Please specify a module name with --mname");
      exit 1
    end;
  let dir = if !fstar_only then !odir else if !tmpdir <> "" then !tmpdir else mk_tmp_dir_name () in
  let basename = produce_fst_file dir in
  if !fstar_only then exit 0;
  let filename = Filename.concat dir basename in
  let res = run_cmd fstar_exe
    (
      [
        filename;
        "--cache_dir"; dir;
        "--already_cached"; ("*,-" ^ !mname);
      ] @
        (if !admit then [ "--admit_smt_queries"; "true" ] else []) @
        fstar_options
    )
  in
  if res <> 0
  then
    begin
      prerr_endline "Verification failed";
      exit res
    end;
  let res =
    run_cmd fstar_exe
      (
        [
          filename;
          "--cache_dir"; dir;
          "--odir"; dir;
          "--already_cached"; "*,";
          "--codegen"; "krml";
          "--extract_module"; !mname;
        ] @
          (if is_rust () then include_options_for_rust else []) @
          fstar_options
      )
  in
  if res <> 0
  then
    begin
      prerr_endline "Extraction to krml failed";
      exit res
    end;
  let mname_subst = Re.replace_string regexp_period ~by:"_" !mname in
  let krml_file = Filename.concat dir (mname_subst ^ ".krml") in
  let krml_options =
    if is_rust () then
      [
        "-backend"; "rust";
        "-fno-box";
        "-fkeep-tuples";
        "-fcontained-type"; "cbor_raw_iterator";
        "-warn-error"; "@1..27";
	"-bundle"; (!mname ^ "=[rename=" ^ mname_subst ^ "]");
	"-bundle"; "CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]";
	"-bundle"; "CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type=\\*[rename=CBORDetVerAux]";
        "-tmpdir"; !odir;
        "-skip-compilation";
        krml_file;
      ] @
        rust_krml_list
    else
      [
          "-warn-error"; "@1..27";
          (if !skip_compilation then "-skip-compilation" else "-skip-linking");
          "-tmpdir"; !odir;
          "-header"; Filename.concat everparse_src_cddl_tool "noheader.txt";
        "-fnoshort-enums";
        "-bundle"; "FStar.\\*,LowStar.\\*,C.\\*,C,PulseCore.\\*,Pulse.\\*[rename=fstar]";
        "-no-prefix"; "CBOR.Pulse.API.Det.C";
        "-no-prefix"; "CBOR.Pulse.API.Det.Type";
        "-no-prefix"; "CBOR.Spec.Constants";
        "-bundle"; "CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\\*[rename=CBORDetAPI]";
	"-bundle"; (!mname ^ "=\\*");
	"-add-include"; "\"CBORDetAbstract.h\"";
        "-I"; Filename.concat (Filename.concat everparse_src_cbor_pulse "det") "c";
        krml_file;
      ] @
        c_krml_list
  in
  let res =
    run_cmd
      krml_exe
      krml_options
  in
  if res = 0 then print_endline "EverCDDL succeeded!";
  exit res
