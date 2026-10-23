open OS
open HashingOptions

let lowparse_home = filename_concat (filename_concat (filename_concat everparse_home "lib") "everparse") "lowparse"

(* The 3d runtime support: the Pulse combinator backend the generated code is
   checked against (which also needs lib/everparse/lowparse and the Pulse
   library itself on the include path), the pre-extracted C, and the static
   headers such as EverParseEndianness.h. *)
let lib_3d_home = filename_concat (filename_concat (filename_concat everparse_home "lib") "everparse") "3d"
let pulse_makefile_basic =
  filename_concat lib_3d_home "Makefile.basic"

let cl_wrapper () = filename_concat lib_3d_home "cl-wrapper.cmd"

(* The directory holding the pre-generated EverParse.h for this backend.
   See src/3d/krml/header.Makefile. *)
let pulse_actions_c_home input_stream_binding =
  filename_concat
    (filename_concat lib_3d_home "krml")
    (string_of_input_stream_binding input_stream_binding)

let lowstar_api () = Options_Base.get_api () = HashingOptions.ApiLowstar

let everparse_h_home input_stream_binding =
  if lowstar_api () then
    filename_concat (filename_concat lib_3d_home "krml/lowstar")
      (string_of_input_stream_binding input_stream_binding)
  else pulse_actions_c_home input_stream_binding

let everparse_static_headers input_stream_binding out_dir =
  match input_stream_binding with
  | HashingOptions.InputStreamStatic _ | HashingOptions.InputStreamExtern _ ->
    [filename_concat out_dir "EverParseStreamPrimitives.h"]
  | _ -> []

(* command lines *)
let fstar_args0 input_stream_binding =
  let runtime = everparse_h_home input_stream_binding in
  ["--already_cached"; "Prims,LowStar,FStar,LowParse,C,PulseCore,Pulse,EverParse3d.\\*,Spec";
   "--include"; lowparse_home;
   "--include"; filename_concat runtime "src";
   "--include"; filename_concat runtime "checked";
   "--warn_error"; "@241"] @ OS.getenv_array "EVERPARSE_FSTAR_OPTIONS"

let list_snoc q a =
  q @ [a]

let fstar_args
  ?output_dir
  input_stream_binding
  out_dir
=
    let output_dir = Option.value output_dir ~default:out_dir in
    "--odir" :: output_dir ::
      "--cache_dir" :: out_dir ::
        "--include" :: out_dir ::
            fstar_args0 input_stream_binding

let verify_fst_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  let fstar_args = list_snoc (fstar_args input_stream_binding out_dir) file in
  let fstar_args = ["--smt"; Z3Executable.resolve fstar_exe] @ fstar_args in
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args)

let fstar_modul_of_filename fst =
  let basename = remove_extension (basename fst) in
  String.concat "." (List.map String.capitalize_ascii (String.split_on_char '.' basename))

let pretty_print_source_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  let fstar_args = list_snoc (fstar_args input_stream_binding out_dir) file in
  run_cmd fstar_exe ("--print_in_place" :: fstar_args)

let pretty_print_source_module
      fstar_exe
      input_stream_binding
      out_dir
      (file, modul)
    : unit
  =
  let external_types_fsti_file = filename_concat out_dir (Printf.sprintf "%s.ExternalTypes.fsti" modul) in
  let external_api_fsti_file = filename_concat out_dir (Printf.sprintf "%s.ExternalAPI.fsti" modul) in
  let fst_file = filename_concat out_dir (Printf.sprintf "%s.fst" modul) in
  let types_fst_file = filename_concat out_dir (Printf.sprintf "%s.Types.fst" modul) in
  let fsti_file = Printf.sprintf "%si" fst_file in
  let all_files =
    List.filter file_exists [external_types_fsti_file;
                             external_api_fsti_file;
                             types_fst_file;
                             fsti_file;
                             fst_file] in
  List.iter (pretty_print_source_file fstar_exe input_stream_binding out_dir) all_files

let pretty_print_source_modules
      fstar_exe
      input_stream_binding
      (out_dir: string)
      (files_and_modules: (string * string) list)
=
  List.iter (pretty_print_source_module fstar_exe input_stream_binding out_dir) files_and_modules

let verify_module
      fstar_exe
      input_stream_binding
      out_dir
      (file, modul)
    : unit
  =
  let external_types_fsti_file =
    filename_concat out_dir (Printf.sprintf "%s.ExternalTypes.fsti" modul)
  in
  let external_api_fsti_file =
    filename_concat out_dir (Printf.sprintf "%s.ExternalAPI.fsti" modul)
  in
  let fst_file = 
      filename_concat out_dir (Printf.sprintf "%s.fst" modul)
  in
  let types_fst_file = 
      filename_concat out_dir (Printf.sprintf "%s.Types.fst" modul)
  in
  let fsti_file = 
      Printf.sprintf "%si" fst_file
  in
  let all_files = [external_types_fsti_file;
                   external_api_fsti_file;
                   types_fst_file;
                   fsti_file;
                   fst_file] in
  let all_files =
    match Deps.get_config () with
    | None -> all_files
    | Some (_, module_name) -> 
      let cfg_fst_name = filename_concat out_dir (Printf.sprintf "%s.fst" module_name) in
      cfg_fst_name::all_files
  in
  List.iter (verify_fst_file fstar_exe input_stream_binding out_dir) (List.filter file_exists all_files)

let remove_intermediate_files
      out_dir
      (_, modul)
  =
  let root_name = filename_concat out_dir modul in
  List.iter remove_if_exists [
      Printf.sprintf "%s.ExternalTypes.fsti" root_name;
      Printf.sprintf "%s.ExternalAPI.fsti" root_name;
      Printf.sprintf "%s.Types.fst" root_name;
      Printf.sprintf "%s.fst" root_name;
      Printf.sprintf "%s.fsti" root_name;
      Printf.sprintf "%s.ExternalTypes.fsti.checked" root_name;
      Printf.sprintf "%s.ExternalAPI.fsti.checked" root_name;
      Printf.sprintf "%s.Types.fst.checked" root_name;
      Printf.sprintf "%s.fst.checked" root_name;
      Printf.sprintf "%s.fsti.checked" root_name;
      Printf.sprintf "%s_Types.krml" root_name;
      Printf.sprintf "%s_ExternalAPI.krml" root_name;
      Printf.sprintf "%s_ExternalTypes.krml" root_name;
      Printf.sprintf "%s.krml" root_name;
      Printf.sprintf "%s.cui" root_name;
    ]

let produce_unit
      input_stream_binding
      add_include
      out_dir
      modul
      dep_files_and_modules
  =
  let runtime_cui = filename_concat (everparse_h_home input_stream_binding) "EverParse.cui" in
  if not (file_exists runtime_cui) then begin
    prerr_endline ("Missing runtime unit " ^ runtime_cui ^ "; rebuild the 3D runtime headers.");
    exit 1
  end;
  if OS.getenv_array "EVERPARSE_KRML_OPTIONS" <> [] then begin
    prerr_endline "EVERPARSE_KRML_OPTIONS: not implemented yet for Custard direct-to-C extraction";
    exit 1
  end;
  let module_file suffix = filename_concat out_dir (modul ^ suffix) in
  let auxiliary_modules =
    List.filter_map
      (fun (suffix, extension) ->
        if file_exists (module_file (suffix ^ extension))
        then Some (modul ^ suffix)
        else None)
      [".ExternalTypes", ".fsti"; ".ExternalAPI", ".fsti"; ".Types", ".fst"]
  in
  let config_modules = match Options.config_module_name () with
    | None -> []
    | Some name -> [name]
  in
  let roots =
    List.concat_map (fun name -> ["--custard_entry_module"; name])
      (modul :: auxiliary_modules @ config_modules)
  in
  let units = runtime_cui ::
    List.map (fun (_, name) -> filename_concat out_dir (name ^ ".cui")) dep_files_and_modules
  in
  List.iter (fun file ->
    if not (file_exists file) then begin
      prerr_endline ("Missing dependency unit " ^ file ^ "; extract dependencies first.");
      exit 1
    end) units;
  let links = List.concat_map (fun file -> ["--custard_link"; file]) units in
  (* Publish only complete units; a failed extraction must leave the previous
     outputs older than their prerequisites so that make retries it. *)
  let staging = filename_concat out_dir (".custard-" ^ modul) in
  if not (Sys.file_exists staging) then Unix.mkdir staging 0o700;
  let staged name = filename_concat staging name in
  let forwarding_headers =
    List.filter_map (fun suffix ->
      if file_exists (module_file (suffix ^ ".fsti"))
      then Some (String.concat "_" (String.split_on_char '.' (modul ^ suffix)) ^ ".h")
      else None) [".ExternalTypes"; ".ExternalAPI"]
  in
  let outputs = [modul ^ ".c"; modul ^ ".h"] @ forwarding_headers @ [modul ^ ".cui"] in
  List.iter (fun name -> remove_if_exists (staged name)) outputs;
  let fstar_exe = Options.get_fstar_exe () in
  let args =
    ["--smt"; Z3Executable.resolve fstar_exe;
     "--codegen"; "C"; "--custard_unit"; modul;
     "--custard_monomorphize_types"; "true"] @ roots @ links @
    fstar_args ~output_dir:staging input_stream_binding out_dir @
    [module_file ".fst"; "-o"; staged (modul ^ ".c")]
  in
  run_cmd fstar_exe args;
  let include_file name = "#include \"" ^ name ^ "\"\n" in
  let includes =
    List.map (fun inc -> "#include " ^ inc ^ "\n") add_include @
    (let name = HashingOptions.input_stream_include input_stream_binding in
     if name = "" then [] else [include_file name]) @
    (match Deps.get_config () with
     | None -> []
     | Some (cfg, _) -> [include_file (Config.config_compile_time_flags cfg).include_file])
  in
  let header = staged (modul ^ ".h") in
  let original = open_in_bin header in
  let contents = really_input_string original (in_channel_length original) in
  close_in original;
  let channel = open_out_bin header in
  List.iter (output_string channel) includes;
  output_string channel contents;
  close_out channel;
  List.iter (fun name ->
    let channel = open_out (staged name) in
    output_string channel (include_file (modul ^ ".h"));
    close_out channel) forwarding_headers;
  List.iter (fun name -> rename (staged name) (filename_concat out_dir name)) outputs;
  Unix.rmdir staging

let module_dependencies file modul =
  Deps.collect_and_sort_dependencies [file] |>
  List.filter_map (fun file ->
    let name = Options_Base.module_name file in
    if name = modul then None else Some (file, name))

let produce_c_files
      input_stream_binding
      (_emit_output_types_defs: bool)
      (add_include: string list)
      (skip_c_makefiles: bool)
      (cleanup: bool)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  List.iter (fun (file, modul) ->
    produce_unit input_stream_binding add_include out_dir modul
      (module_dependencies file modul)) files_and_modules;
  if lowstar_api () && not skip_c_makefiles then
    copy pulse_makefile_basic (filename_concat out_dir "Makefile.basic");
  if cleanup then begin
    List.iter (remove_intermediate_files out_dir) files_and_modules;
    match Options.config_module_name () with
    | None -> ()
    | Some name -> remove_intermediate_files out_dir ("", name)
  end

let produce_one_c_file
      input_stream_binding
      (_emit_output_types_defs: bool)
      (add_include: string list)
      (out_dir: string)
      (_file: string)
      (modul: string)
      (dep_files_and_modules: (string * string) list)
    : unit
  =
  produce_unit input_stream_binding add_include out_dir modul dep_files_and_modules

(* Update EVERPARSEVERSION and FILENAME *)

let regexp_EVERPARSEVERSION = Re.Posix.compile_pat "EVERPARSEVERSION"
let regexp_FILENAME = Re.Posix.compile_pat "FILENAME"
let regexp_EVERPARSEHASHES = Re.Posix.compile_pat "EVERPARSEHASHES"

let replace_variables
      hash_comment
      filename
      file_in
      channel_out
  =
  let cin = open_in file_in in
  let rec aux () =
    match
      begin try
          Some (input_line cin)
        with End_of_file -> None
      end
    with
    | None -> ()
    | Some ln ->
       let ln = Re.replace_string regexp_EVERPARSEVERSION ~by:Version.everparse_version ln in
       let ln = Re.replace_string regexp_FILENAME ~by:filename ln in
       let ln =
         match hash_comment with
         | None -> ln
         | Some hash_comment ->
            Re.replace_string regexp_EVERPARSEHASHES ~by:hash_comment ln
       in
       output_line channel_out ln;
       aux ()
  in
  aux ();
  close_in cin

(* Copyright headers *)

let add_copyright_header
      hash_comment
      out_dir
      copyright_file
      target_file
  =
  if Sys.file_exists target_file
  then begin
      print_endline (Printf.sprintf "Adding copyright to %s from %s" target_file copyright_file);
      let tmp = Filename.temp_file "everparseaddcopyrightheader" ".tmp" in
      rename target_file tmp;
      let cout = open_out target_file in
      replace_variables hash_comment (basename target_file) copyright_file cout;
      cat tmp cout;
      close_out cout;
      Sys.remove tmp
    end

(* Collect all produced .c and .h files *)

let collect_file
      accu
      filename
  =
  if Sys.file_exists filename
  then filename :: accu
  else accu

let collect_files_from
      (produced_files: bool)
      (wrappers: bool)
      out_dir
      accu
      (_, modul)
  =
  let collect_file' accu file =
    collect_file accu (filename_concat out_dir file)
  in
  List.fold_left
    collect_file'
    accu
    begin
      begin if produced_files then
              [
                Printf.sprintf "%s.c" modul;
                Printf.sprintf "%s.h" modul;
                Printf.sprintf "%s_ExternalTypes.h" modul;
                Printf.sprintf "%s_ExternalAPI.h" modul;
              ]
            else []
      end @
      begin if wrappers then
              (* all C files emitted by 3d itself, cf. Main.emit_entrypoint.
                 Nonexistent ones are filtered out by collect_file. *)
              [
                Printf.sprintf "%sWrapper.c" modul;
                Printf.sprintf "%sWrapper.h" modul;
                Printf.sprintf "%sStaticAssertions.c" modul;
                Printf.sprintf "%sAutoStaticAssertions.c" modul;
                Printf.sprintf "%s_OutputTypesDefs.h" modul;
                Printf.sprintf "%s_ExternalTypedefs.h" modul;
                Printf.sprintf "%s_OutputTypes.c" modul;
              ]
            else []
      end
    end

let collect_files
      no_everparse_h
      (produced_files: bool)
      (wrappers: bool)
      out_dir
      files_and_modules
  =
  let accu = [] in
  let accu =
    if not no_everparse_h
    then
      let accu = collect_file accu (filename_concat out_dir "EverParse.h") in
      let accu = collect_file accu (filename_concat out_dir "EverParseEndianness.h") in
      let accu =
        List.fold_left collect_file accu
          (everparse_static_headers (Options.get_input_stream_binding ()) out_dir)
      in
      (* --api pulse copies two more headers into out_dir; treat them like the
         others (clang-format, cleanup, ...). *)
      let accu =
        if Options.uses_pulse_api ()
        then
          let accu = collect_file accu (filename_concat out_dir "EverParsePulse.h") in
          collect_file accu (filename_concat out_dir "EverParsePulseEndianness.h")
        else accu
      in
      accu
    else
      accu
  in
  List.fold_left (collect_files_from produced_files wrappers out_dir) accu files_and_modules

let add_copyright
      (produced_files: bool)
      (wrappers: bool)
      out_dir
      ((ddd_file, _) as dm)
  =
  let copyright_file = Printf.sprintf "%s.copyright.txt" ddd_file in
  if Sys.file_exists copyright_file
  then begin
      let h = Hashing_Hash.hash_as_comment ddd_file in
      List.iter (add_copyright_header (Some h) out_dir copyright_file) (collect_files_from produced_files wrappers out_dir [] dm)
    end

  
(* Call clang-format *)

let call_clang_format_on
  (clang_format_executable: string)
  (files: string list)
= match files with
  | [] -> ()
  | _ ->
  let clang_format_args =
    "-i" ::
      "--style=file" ::
        files
  in
  let clang_format_exe =
    if clang_format_executable <> ""
    then clang_format_executable
    else Printf.sprintf "clang-format%s" (if Sys.win32 then ".exe" else "")
  in
  run_cmd clang_format_exe clang_format_args

let call_clang_format
      (no_everparse_h: bool)
      (produced_files: bool)
      (wrappers: bool)
      (clang_format_exe0: string)
      (out_dir: string)
      (files_and_modules: (string * string) list)
  =
  let files = collect_files no_everparse_h produced_files wrappers out_dir files_and_modules in
  call_clang_format_on clang_format_exe0 files

(* Check and Save hashes *)

let check_inplace_hashes = Hashing_Hash.check_inplace_hashes Hashing.check_inplace_hashes_f

let save_hashes
      (out_dir: string)
      (file, modul)
  = let c = Hashing_Hash.hashed_files out_dir modul in
    let json = filename_concat out_dir (Printf.sprintf "%s.json" modul) in
    Hashing.save_hashes file (Some c) json

let save_hashes_for_module
      (out_dir: string)
      (file: string)
      (modul: string)
  = save_hashes out_dir (file, modul)

(* Copy .clang-format *)

let copy_clang_format out_dir =
  copy (filename_concat lib_3d_home ".clang-format") (filename_concat out_dir ".clang-format")

(* [only] restricts the run to the prelude headers it names, by basename. The
   generated EverParse.Makefile gives each header a rule of its own and has that
   rule name the file it is responsible for, so that no two rules ever write the
   same file and a parallel make cannot compile against a header another rule is
   busy rewriting. [] means "all of them", which is what --batch mode and
   postprocess_c want. *)
let copy_everparse_h_raw
      ?(only: string list = [])
      input_stream_binding
      out_dir =
      let wanted name = only = [] || List.mem name only in
      let dest_everparse_h = filename_concat out_dir "EverParse.h" in
      (* Each API ships a pre-generated, backend-specific EverParse.h: pulse
         from lib/everparse/3d/krml/<backend>, lowstar from
         lib/everparse/3d/krml/lowstar/<backend>. Validator extraction imports
         its CUI and does not write this shared header. *)
      let everparse_h_source = filename_concat (everparse_h_home input_stream_binding) "EverParse.h" in
      if wanted "EverParse.h" && (lowstar_api () || file_exists everparse_h_source)
      then copy everparse_h_source dest_everparse_h;
      List.iter
        (fun destination ->
          let name = Filename.basename destination in
          if wanted name then
            copy (filename_concat (everparse_h_home input_stream_binding) name) destination)
        (everparse_static_headers input_stream_binding out_dir);
      if Options.uses_pulse_api ()
      then begin
        let everparse_pulse_h_source = filename_concat lib_3d_home "EverParsePulse.h" in
        if wanted "EverParsePulse.h" && file_exists everparse_pulse_h_source
        then copy everparse_pulse_h_source (filename_concat out_dir "EverParsePulse.h")
        ;
        let everparse_pulse_endianness_h_source = filename_concat lib_3d_home "EverParsePulseEndianness.h" in
        if wanted "EverParsePulseEndianness.h" && file_exists everparse_pulse_endianness_h_source
        then copy everparse_pulse_endianness_h_source (filename_concat out_dir "EverParsePulseEndianness.h")
      end;
      let everparse_endianness_source = (filename_concat lib_3d_home (Printf.sprintf "EverParseEndianness%s.h" (if Sys.win32 then "_Windows_NT" else ""))) in
      if wanted "EverParseEndianness.h" && file_exists everparse_endianness_source
      then copy everparse_endianness_source (filename_concat out_dir "EverParseEndianness.h")

let everparse_pulse_headers out_dir =
  if Options.uses_pulse_api ()
  then [
      filename_concat out_dir "EverParsePulse.h";
      filename_concat out_dir "EverParsePulseEndianness.h";
    ]
  else []

let copy_everparse_h
      (clang_format: bool)
      (clang_format_executable: string)
      input_stream_binding
      out_dir
      (only: string list) =
  copy_everparse_h_raw ~only input_stream_binding out_dir;
  if clang_format
  then
    (* Only reformat what this run actually copied, for the same reason it only
       copies what it was asked for: another rule may own the rest. *)
    let copied =
      List.filter
        (fun f -> only = [] || List.mem (Filename.basename f) only)
        ([filename_concat out_dir "EverParse.h"; filename_concat out_dir "EverParseEndianness.h"]
         @ everparse_pulse_headers out_dir @ everparse_static_headers input_stream_binding out_dir)
    in
    call_clang_format_on clang_format_executable copied

(* Postprocess C files, assuming that they have already been processed *)

let postprocess_c
      input_stream_binding
      (produced_files: bool)
      (wrappers: bool)
      (clang_format: bool)
      (clang_format_executable: string)
      (copy_clang_format_opt: bool)
      (skip_c_makefiles: bool)
      (cleanup: bool)
      (no_everparse_h: bool)
      (save_hashes_opt: bool)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  if not no_everparse_h
  then begin
      copy_everparse_h_raw input_stream_binding out_dir
    end;
  (* clang-format the files if asked for *)
  if clang_format
  then begin
      if copy_clang_format_opt then copy_clang_format out_dir;
      call_clang_format no_everparse_h produced_files wrappers clang_format_executable out_dir files_and_modules;
    end;
  (* add copyright *)
  List.iter (add_copyright produced_files wrappers out_dir) files_and_modules;
  if not no_everparse_h
  then begin
      let copyright_txt = filename_concat lib_3d_home "copyright.txt" in
      add_copyright_header None out_dir copyright_txt (filename_concat out_dir "EverParse.h")
    end;
  (* save hashes *)
  if save_hashes_opt
  then List.iter (save_hashes out_dir) files_and_modules;
  ()

let produce_and_postprocess_c
      input_stream_binding
      (emit_output_types_defs: bool)
      (add_include: string list)
      (clang_format: bool)
      (clang_format_executable: string)
      (copy_clang_format_opt: bool)
      (skip_c_makefiles: bool)
      (cleanup: bool)
      (no_everparse_h: bool)
      (save_hashes_opt: bool)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  (* produce the C files *)
  produce_c_files input_stream_binding emit_output_types_defs add_include skip_c_makefiles cleanup out_dir files_and_modules;
  (* postprocess the produced C files *)
  postprocess_c input_stream_binding true true clang_format clang_format_executable copy_clang_format_opt skip_c_makefiles cleanup no_everparse_h save_hashes_opt out_dir files_and_modules

let produce_and_postprocess_one_c
      input_stream_binding
      (emit_output_types_defs: bool)
      (add_include: string list)
      (clang_format: bool)
      (clang_format_executable: string)
      (out_dir: string)
      (file: string)
      (modul: string)
      (dep_files_and_modules: (string * string) list)
    : unit
  =
  (* produce the .c and .h file. produce_one_c_file never writes
     out_dir/EverParse.h, so there is nothing to undo here -- which matters,
     because the generated makefiles run these concurrently and any
     save/restore or delete of that shared file would race. *)
  produce_one_c_file input_stream_binding emit_output_types_defs add_include out_dir file modul dep_files_and_modules;
  (* postprocess the produced .c and .h files for this module *)
  postprocess_c input_stream_binding true false clang_format clang_format_executable false true false true false out_dir [file, modul]

let postprocess_wrappers
      input_stream_binding
      (clang_format: bool)
      (clang_format_executable: string)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  postprocess_c input_stream_binding false true clang_format clang_format_executable false true false true false out_dir files_and_modules

let postprocess_fst
      fstar_exe
      input_stream_binding
      (emit_output_types_defs: bool)
      (add_include: string list)
      (clang_format: bool)
      (clang_format_executable: string)
      (copy_clang_format_opt: bool)
      (skip_c_makefiles: bool)
      (cleanup: bool)
      (no_everparse_h: bool)
      (save_hashes_opt: bool)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  (* Produce the .checked files.
     FIXME: modules can be processed in parallel *)
  List.iter (verify_module fstar_exe input_stream_binding out_dir) files_and_modules;
  (* produce the .c and .h files and format them *)
  produce_and_postprocess_c input_stream_binding emit_output_types_defs add_include clang_format clang_format_executable copy_clang_format_opt skip_c_makefiles cleanup no_everparse_h save_hashes_opt out_dir files_and_modules

let check_all_hashes = Hashing_Hash.check_all_hashes Hashing.check_inplace_hashes_f Hashing.load_hash
