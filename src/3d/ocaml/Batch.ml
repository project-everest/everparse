open OS
open HashingOptions

(* paths *)
let krml_home = OS.getenv "KRML_HOME"
let krmllib = filename_concat krml_home "krmllib"
let everparse_home = OS.getenv "EVERPARSE_HOME"
let lowparse_home = filename_concat (filename_concat everparse_home "src") "lowparse"
let ddd_home = filename_concat (filename_concat everparse_home "src") "3d"
let ddd_prelude_home = filename_concat (filename_concat (filename_concat everparse_home "src") "3d") "prelude"

let cl_wrapper () = filename_concat krml_home (filename_concat "misc" "cl-wrapper.bat")

let ddd_actions_home input_stream_binding =
  let input_stream_dir =
    match string_of_input_stream_binding input_stream_binding with
    | "static" -> "extern"
    | s -> s
  in
  filename_concat ddd_prelude_home input_stream_dir

let ddd_actions_c_home input_stream_binding =
  filename_concat ddd_prelude_home (string_of_input_stream_binding input_stream_binding)

(* krml: on Windows, needs to be copied into .exe *)
let krml out_dir =
  let rec aux exn = function
    | [] -> if exn then failwith "no krml found" else ""
    | (dir, file) :: q ->
       let candidate = filename_concat dir file in
       if Sys.file_exists candidate then candidate else aux exn q
  in
  let dir = krml_home in
  let dir_bin = filename_concat dir "bin" in
  if Sys.win32
  then
    let candidate =
      aux false [
          (dir_bin, "krml.exe"); (* binary package *)
          (dir, "krml.exe");
        ]
    in
    if candidate <> ""
    then (false, candidate)
    else begin
        let target = Filename.temp_file ~temp_dir:out_dir "krml" ".exe" in
        begin
          (* Here, Windows cannot even read symlinks *)
          let dir' = filename_concat (filename_concat (filename_concat dir "_build") "default") "src" in
          let candidate = aux true [(dir', "Karamel.exe")] in
          copy candidate target
        end;
        (true, target)
      end
  else
    (false, aux true [
                (dir_bin, "krml"); (* binary package *)
                (dir, "krml");
    ])

(* command lines *)
let fstar_args0 =
  "--z3version" :: "4.13.3" ::
  "--already_cached" :: "Prims,LowStar,FStar,LowParse,C,EverParse3d.\\*,Spec" ::
    "--include" :: lowparse_home ::
      "--include" :: krmllib ::
        "--include" :: (filename_concat krmllib "obj") ::
          "--include" :: ddd_prelude_home ::
            "--cmi" ::
            "--warn_error" :: "+241" ::
              OS.getenv_array "EVERPARSE_FSTAR_OPTIONS"

let list_snoc q a =
  q @ [a]

let fstar_args
  input_stream_binding
  out_dir
=
    "--odir" :: out_dir ::
      "--cache_dir" :: out_dir ::
        "--include" :: ddd_actions_home input_stream_binding ::
        "--include" :: out_dir ::
            fstar_args0

let verify_fst_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  let fstar_args = list_snoc (fstar_args input_stream_binding out_dir) file in
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args)

let fstar_modul_of_filename fst =
  let basename = remove_extension (basename fst) in
  String.concat "." (List.map String.capitalize_ascii (String.split_on_char '.' basename))

let fstar_extract_args input_stream_binding out_dir fst =
  "--extract_module" :: fstar_modul_of_filename fst ::
    "--codegen" :: "krml" ::
      (list_snoc (fstar_args input_stream_binding out_dir) fst)

let extract_fst_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  run_cmd fstar_exe (fstar_extract_args input_stream_binding out_dir file)

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

let verify_and_extract_module
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
  let all_extract_files = [external_types_fsti_file; external_api_fsti_file; types_fst_file; fst_file] in  
  let all_files, all_extract_files = 
    match Deps.get_config () with
    | None -> all_files, all_extract_files
    | Some (_, module_name) -> 
      let cfg_fst_name = filename_concat out_dir (Printf.sprintf "%s.fst" module_name) in
      cfg_fst_name::all_files,
      cfg_fst_name::all_extract_files
  in
  List.iter (verify_fst_file fstar_exe input_stream_binding out_dir) (List.filter file_exists all_files);
  List.iter (extract_fst_file fstar_exe input_stream_binding out_dir) (List.filter file_exists all_extract_files)

let is_krml
      filename
  = Filename.check_suffix filename "krml"

let krml_args0 = OS.getenv_array "EVERPARSE_KRML_OPTIONS"

let all_krmls_in_dir
      dir
  = let h = Unix.opendir dir in
    let rec aux accu =
      match
        begin try
            Some (Unix.readdir h)
          with End_of_file -> None
        end
      with
      | None -> accu
      | Some entry ->
         aux (if is_krml entry then (filename_concat dir entry :: accu) else accu)
    in
    let res = aux [] in
    Unix.closedir h;
    res

let all_everparse_krmls input_stream_binding =
  let prelude = all_krmls_in_dir ddd_prelude_home in
  let actions = all_krmls_in_dir (ddd_actions_home input_stream_binding) in
  let actions_base = List.map basename actions in
  let prelude' = List.filter (fun f -> not (List.mem (basename f) actions_base)) prelude in
  prelude' @ actions

let remove_fst_and_krml_files
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
    ]

let everparse_only_bundle = "Prims,LowParse.\\*,EverParse3d.\\*"

let fstar_krmllib_bundle = "FStar.\\*,LowStar.\\*,C.\\*"

let krml_args input_stream_binding emit_output_types_defs add_include skip_c_makefiles out_dir files_and_modules =
  let has_external_types modul =
    file_exists (filename_concat out_dir (Printf.sprintf "%s.ExternalTypes.fsti" modul)) in

  let has_external_api modul =
    file_exists (filename_concat out_dir (Printf.sprintf "%s.ExternalAPI.fsti" modul)) in

  let has_types modul =
    file_exists (filename_concat out_dir (Printf.sprintf "%s.Types.fst" modul))
  in

  let types_krml modul =
    if has_types modul
    then [filename_concat out_dir (Printf.sprintf "%s_Types.krml" modul)]
    else []
  in

  let external_types_krml modul =
    if has_external_types modul
    then [filename_concat out_dir (Printf.sprintf "%s_ExternalTypes.krml" modul)]
    else [] in

  let external_api_krml modul =
    if has_external_api modul
    then [filename_concat out_dir (Printf.sprintf "%s_ExternalAPI.krml" modul)]
    else [] in

  let external_types_lib_args modul =
    []
  in
  
  let external_api_lib_args modul =  
    if has_external_api modul
    then ["-library"; Printf.sprintf "%s.ExternalAPI" modul]
    else [] in

  let external_types_prefix_args modul =
    if has_external_types modul
    then ["-no-prefix"; Printf.sprintf "%s.ExternalTypes" modul]
    else [] in
  
  let external_api_prefix_args modul =
    if has_external_api modul
    then ["-no-prefix"; Printf.sprintf "%s.ExternalAPI" modul]
    else [] in

  let external_typedefs_include_args modul =
    if has_external_types modul && emit_output_types_defs
    then ["-add-include"; Printf.sprintf "\"%s_ExternalTypedefs.h\"" modul]
    else [] in

  let krml_files = List.fold_left
                     (fun accu (_, modul) ->
                       let l =
                         (types_krml modul)@
			 (external_types_krml modul)@(external_api_krml modul)@(filename_concat out_dir (Printf.sprintf "%s.krml" modul) ::
                                                    accu)
                       in

		       let c_wrapper = Printf.sprintf "%sWrapper.c" modul in
		       let l =
		         if (not skip_c_makefiles) && Sys.file_exists (filename_concat out_dir c_wrapper)
                         then c_wrapper :: l
                         else l in			 
		       
                       let static_asserts = Printf.sprintf "%sStaticAssertions.c" modul in
                       let l =
		         if (not skip_c_makefiles) && Sys.file_exists (filename_concat out_dir static_asserts)
                         then static_asserts :: l
                         else l in
		       l
                     )
                     (all_everparse_krmls input_stream_binding)
                     files_and_modules
  in
  let krml_files =
    if (not skip_c_makefiles) && Sys.file_exists (filename_concat out_dir "testcases.c")
    then "testcases.c" :: krml_files
    else krml_files
  in
  let krml_files =
    match Options.config_module_name () with
    | None -> krml_files
    | Some m -> filename_concat out_dir (Printf.sprintf "%s.krml" m) :: krml_files
  in
  let external_types_lib_args = List.fold_left (fun accu (_, modul) ->
                                    accu @ (external_types_lib_args modul)) [] files_and_modules in
  let external_api_lib_args = List.fold_left (fun accu (_, modul) ->
                                  accu @ (external_api_lib_args modul)) [] files_and_modules in
  let external_types_no_prefix_args = List.fold_left (fun accu (_, modul) ->
                                  accu @ (external_types_prefix_args modul)) [] files_and_modules in
  let external_api_no_prefix_args = List.fold_left (fun accu (_, modul) ->
                                  accu @ (external_api_prefix_args modul)) [] files_and_modules in
  let external_typedefs_include_args = List.fold_left (fun accu (_, modul) ->
                                           accu @ (external_typedefs_include_args modul)) [] files_and_modules in

  let krml_files = List.rev krml_files in
  let add_include_opt = "-add-early-include" in
  let krml_add_includes =
    List.fold_left
      (fun accu inc ->
        add_include_opt :: inc ::
          List.fold_left
            (fun accu (_, modul) ->
              add_include_opt :: Printf.sprintf "%s.c:%s" modul inc :: accu
            )
            accu
            files_and_modules
      )
      (krml_args0 @ krml_files)
      (List.rev add_include)
  in
  let krml_args =
    "-tmpdir" :: out_dir ::
      "-skip-compilation" ::
        "-static-header" :: "LowParse.Low.Base,EverParse3d.Prelude.StaticHeader,EverParse3d.ErrorCode,EverParse3d.CopyBuffer,EverParse3d.InputStream.\\*" ::
          "-no-prefix" :: "LowParse.Slice" ::
            "-no-prefix" :: "LowParse.Low.BoundedInt" ::
                "-library" :: everparse_only_bundle ::
                  "-warn-error" :: "-9@4-20" ::
                    "-fnoreturn-else" ::
                      "-fparentheses" ::
                        "-fcurly-braces" ::
                          "-fmicrosoft" ::
                          "-fno-shadow" ::
                            "-header" :: filename_concat ddd_home "noheader.txt" ::
                              "-minimal" ::
                                "-add-include" :: "\"EverParse.h\"" ::
                                  "-fextern-c" ::
                                    external_types_lib_args @
                                    external_api_lib_args @
                                    external_types_no_prefix_args @
                                    external_api_no_prefix_args @
                                    external_typedefs_include_args @
                                    krml_add_includes
  in
  let input_stream_include = HashingOptions.input_stream_include input_stream_binding in
  let krml_args =
      if input_stream_include = ""
      then krml_args
      else "-add-include" :: Printf.sprintf "\"%s\"" input_stream_include :: krml_args
  in
  let krml_args =
    if skip_c_makefiles
    then "-skip-makefiles" :: krml_args
    else krml_args
  in
  let krml_args =
    match Deps.get_config () with
    | None -> krml_args
    | Some (cfg, module_name) ->
      let include_file = Printf.sprintf "\"%s\"" cfg.compile_time_flags.include_file in
      "-no-prefix" :: module_name :: "-add-include" :: include_file  :: krml_args
  in
  krml_args
  

let call_krml files_and_modules_cleanup out_dir krml_args =
  (* append the everparse and krmllib bundles to the list of arguments *)
  let krml_args = krml_args @ [
        "-bundle" ;
        Printf.sprintf "%s[rename=Lib,rename-prefix]" fstar_krmllib_bundle;
        "-bundle" ;
        Printf.sprintf "%s[rename=EverParse,rename-prefix]" everparse_only_bundle;
  ]
  in
  (* the argument list is too long, so we need to go through an argument file *)
  let argfile = Filename.temp_file ~temp_dir:out_dir "krmlargs" ".rsp" in
  let h = open_out argfile in
  let rec aux = function
    | [] -> ()
    | a :: q ->
       output_string h (Printf.sprintf "%s\n" a);
       aux q
  in
  aux krml_args;
  close_out h;
  let (is_temp_krml, krml) = krml out_dir in
  print_endline (Printf.sprintf "KaRaMeL found at: %s" krml);
  run_cmd krml [Printf.sprintf "@%s" argfile];
  begin match files_and_modules_cleanup with
  | Some files_and_modules ->
      Sys.remove argfile;
      if is_temp_krml then Sys.remove krml;
      List.iter (remove_fst_and_krml_files out_dir) files_and_modules
  | _ -> ()
  end

let produce_c_files
      input_stream_binding
      (emit_output_types_defs: bool)
      (add_include: string list)
      (skip_c_makefiles: bool)
      (cleanup: bool)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  let krml_args = krml_args input_stream_binding emit_output_types_defs add_include skip_c_makefiles out_dir files_and_modules in
  (* if M.Types exists, then bundle M.Types.krml and EverParse into M *)
  let krml_args =
    let files_and_modules_with_types =
      List.filter
        (fun (_, modul) ->
          Sys.file_exists (filename_concat out_dir (Printf.sprintf "%s.Types.fst" modul))
        )
        files_and_modules
    in
    let bundle_types = List.fold_left (fun acc (_, modul) ->
                           "-bundle"::(Printf.sprintf "%s=%s.Types"
                                         modul
                                         modul)::acc) [] files_and_modules_with_types in
    krml_args@bundle_types
  in
  call_krml (if cleanup then Some files_and_modules else None) out_dir krml_args

let produce_one_c_file
      input_stream_binding
      (emit_output_types_defs: bool)
      (add_include: string list)
      (out_dir: string)
      (file: string)
      (modul: string)
      (dep_files_and_modules: (string * string) list)
    : unit
  =
  let krml_args = krml_args input_stream_binding emit_output_types_defs add_include true out_dir ((file, modul) :: dep_files_and_modules) in
  let krml_args =
    krml_args@
(*      List.concat (List.map (fun (_, m) -> ["-library"; Printf.sprintf "%s,%s.Types" m m]) dep_files_and_modules) @ *) [
        "-bundle" ;
        Printf.sprintf "%s=%s" modul (String.concat "," (Printf.sprintf "%s.Types" modul :: List.map (fun (_, m) -> Printf.sprintf "%s,%s.Types" m m) dep_files_and_modules));
      ]
  in
  call_krml None out_dir krml_args

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
              ]
            else []
      end @
      begin if wrappers then
              [
                Printf.sprintf "%sWrapper.c" modul;
                Printf.sprintf "%sWrapper.h" modul;
                Printf.sprintf "%sStaticAssertions.c" modul;
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
      let h = Hashing.hash_as_comment ddd_file in
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

let hashed_files
      (out_dir: string)
      (modul: string)
  =
  {
    Hashing.c = filename_concat out_dir (Printf.sprintf "%s.c" modul);
    Hashing.h = filename_concat out_dir (Printf.sprintf "%s.h" modul);
    Hashing.wrapper_c =
      begin
        let w = filename_concat out_dir (Printf.sprintf "%sWrapper.c" modul) in
        if Sys.file_exists w
        then Some w
        else None
      end;
    Hashing.wrapper_h =
      begin
        let w = filename_concat out_dir (Printf.sprintf "%sWrapper.h" modul) in
        if Sys.file_exists w
        then Some w
        else None
      end;
    Hashing.assertions =
      begin
        let assertions = filename_concat out_dir (Printf.sprintf "%sStaticAssertions.c" modul) in
        if Sys.file_exists assertions
        then Some assertions
        else None
      end;
  }

let check_inplace_hash
      file_3d_file_c
  =
  match String.split_on_char '=' file_3d_file_c with
  | [file_3d; file_c] ->
     if Hashing.check_inplace_hashes file_3d (Hashing.OneHash file_c)
     then begin
         print_endline (Printf.sprintf "EverParse check_inplace_hash succeeded on %s" file_3d)
       end else begin
         print_endline (Printf.sprintf "EverParse check_inplace_hash failed on %s" file_3d);
         exit 255
       end
  | _ -> failwith "check_inplace_hash: expected file.3d=file.h"

let check_inplace_hashes = List.iter check_inplace_hash

let check_hashes
      (ch: check_hashes_t)
      (out_dir: string)
      (file, modul)
  =
  let c = hashed_files out_dir modul in
  match ch with
  | InplaceHashes ->
     Hashing.check_inplace_hashes file (Hashing.AllHashes c)
  | _ ->
     let json = filename_concat out_dir (Printf.sprintf "%s.json" modul) in
     Hashing.check_hash file None json && (
       is_weak ch ||
         let c = hashed_files out_dir modul in
         Hashing.check_hash file (Some c) json
     )

let save_hashes
      (out_dir: string)
      (file, modul)
  = let c = hashed_files out_dir modul in
    let json = filename_concat out_dir (Printf.sprintf "%s.json" modul) in
    Hashing.save_hashes file (Some c) json

(* Copy .clang-format *)

let copy_clang_format out_dir =
  copy (filename_concat ddd_home ".clang-format") (filename_concat out_dir ".clang-format")

let copy_everparse_h_raw
      input_stream_binding
      out_dir =
      let dest_everparse_h = filename_concat out_dir "EverParse.h" in
      let everparse_h_source = (filename_concat (ddd_actions_c_home input_stream_binding) "EverParse.h") in
      if file_exists everparse_h_source
      then copy everparse_h_source dest_everparse_h;
      let everparse_endianness_source = (filename_concat ddd_home (Printf.sprintf "EverParseEndianness%s.h" (if Sys.win32 then "_Windows_NT" else ""))) in
      if file_exists everparse_endianness_source
      then copy everparse_endianness_source (filename_concat out_dir "EverParseEndianness.h")

let copy_everparse_h
      (clang_format: bool)
      (clang_format_executable: string)
      input_stream_binding
      out_dir =
  copy_everparse_h_raw input_stream_binding out_dir;
  if clang_format
  then call_clang_format_on clang_format_executable [filename_concat out_dir "EverParse.h"; filename_concat out_dir "EverParseEndianness.h"]

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
  (* copy EverParse.h unless prevented *)
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
      let copyright_txt = filename_concat ddd_home "copyright.txt" in
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
  let everparse_h_existed_before = Sys.file_exists (filename_concat out_dir "EverParse.h") in
  (* produce the C files *)
  produce_c_files input_stream_binding emit_output_types_defs add_include skip_c_makefiles cleanup out_dir files_and_modules;
  if Sys.file_exists (filename_concat out_dir "EverParse.h") && not everparse_h_existed_before
  then failwith "krml produced some EverParse.h, should not have happened";
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
  let everparse_h_existed_before = Sys.file_exists (filename_concat out_dir "EverParse.h") in
  (* produce the .c and .h file *)
  produce_one_c_file input_stream_binding emit_output_types_defs add_include out_dir file modul dep_files_and_modules;
  if Sys.file_exists (filename_concat out_dir "EverParse.h") && not everparse_h_existed_before
  then failwith "krml produced some EverParse.h, should not have happened";
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
  (* produce the .checked and .krml files.
     FIXME: modules can be processed in parallel *)
  List.iter (verify_and_extract_module fstar_exe input_stream_binding out_dir) files_and_modules;
  (* produce the .c and .h files and format them *)
  produce_and_postprocess_c input_stream_binding emit_output_types_defs add_include clang_format clang_format_executable copy_clang_format_opt skip_c_makefiles cleanup no_everparse_h save_hashes_opt out_dir files_and_modules

let check_all_hashes
      (ch: check_hashes_t)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  = if List.for_all (check_hashes ch out_dir) files_and_modules
    then print_endline "EverParse check_hashes succeeded!"
    else begin
        print_endline "EverParse check_hashes failed";
        exit 255
      end
