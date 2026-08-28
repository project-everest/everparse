open OS
open HashingOptions

(* paths *)
let krml =
  try
    Sys.getenv "KRML_EXE"
  with
  | Not_found ->
    let krml = "krml" ^ (if Sys.win32 then ".exe" else "") in
    let opt_krml = Filename.concat (Filename.concat (Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "karamel") "out") "bin") krml in
    if Sys.file_exists opt_krml
    then opt_krml
    else
       (* assume a binary package *)
       Filename.concat (Filename.concat everparse_home "bin") krml

let krml_locate k tmpdir =
  let tmpfile = Filename.temp_file ~temp_dir:tmpdir ("krml_locate_" ^ k) ".tmp" in
  let cmd = Filename.quote_command krml ~stdout:tmpfile ["-locate-" ^ k] in
  if Sys.command cmd <> 0 then failwith ("Unable to run krml -locate-" ^ k);
  let ch = open_in tmpfile in
  let res = input_line ch in
  close_in ch;
  Sys.remove tmpfile;
  res

let krmllib = krml_locate "krmllib"

let krmlinclude = krml_locate "include"

let lowparse_home = filename_concat (filename_concat everparse_home "src") "lowparse"
let ddd_home = filename_concat (filename_concat everparse_home "src") "3d"
let ddd_prelude_home = filename_concat (filename_concat (filename_concat everparse_home "src") "3d") "prelude"

(* TODO: implement krml -locate-misc *)
let cl_wrapper () =
  (* assume krml.exe is in bin/ *)
  let krml_home = Filename.dirname (Filename.dirname krml) in
  Filename.concat (Filename.concat (Filename.concat (Filename.concat krml_home "share") "krml") "misc") "cl-wrapper.bat"

(* --pulse: the code generated for the Pulse combinator backend is checked
   against lib/everparse/3d and src/lowparse/pulse rather than src/3d/prelude,
   and needs the Pulse library itself on the include path. *)
let pulse_3d_home = filename_concat (filename_concat (filename_concat everparse_home "lib") "everparse") "3d"
let lowparse_pulse_home = filename_concat lowparse_home "pulse"
let pulse_3d_krml_home = filename_concat (filename_concat pulse_3d_home "krml") "extracted"
let pulse_lib_home =
  let candidates =
    (match Sys.getenv_opt "PULSE_HOME" with
     | Some h -> [filename_concat (filename_concat h "lib") "pulse"]
     | None -> [])
    @ [ filename_concat (filename_concat everparse_home "lib") "pulse";
        filename_concat (filename_concat (filename_concat (filename_concat (filename_concat everparse_home "opt") "pulse") "out") "lib") "pulse" ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some d -> d
  | None -> filename_concat (filename_concat everparse_home "lib") "pulse"

(* In --pulse mode KaRaMeL is invoked with -skip-makefiles, so it emits neither
   Makefile.basic nor Makefile.include; EverParse ships its own instead. See
   share/everparse/3d/Makefile.basic for why. *)
let pulse_makefile_basic =
  filename_concat (filename_concat (filename_concat (filename_concat everparse_home "share") "everparse") "3d") "Makefile.basic"

let ddd_actions_home input_stream_binding =
  let input_stream_dir =
    match string_of_input_stream_binding input_stream_binding with
    | "static" -> "extern"
    | s -> s
  in
  filename_concat ddd_prelude_home input_stream_dir

let ddd_actions_c_home input_stream_binding =
  filename_concat ddd_prelude_home (string_of_input_stream_binding input_stream_binding)

(* command lines *)
let fstar_args0 krmllib =
  "--already_cached" :: "Prims,LowStar,FStar,LowParse,C,PulseCore,Pulse,EverParse3d.\\*,Spec" ::
    "--include" :: lowparse_home ::
      "--include" :: krmllib ::
        "--include" :: (filename_concat krmllib "obj") ::
          (if Options.get_pulse ()
           then "--include" :: pulse_lib_home ::
                "--include" :: lowparse_pulse_home ::
                "--include" :: pulse_3d_home :: []
           else "--include" :: ddd_prelude_home :: []) @
            "--cmi" ::
            "--warn_error" :: "+241" ::
              OS.getenv_array "EVERPARSE_FSTAR_OPTIONS"

let list_snoc q a =
  q @ [a]

let z3_version = "4.13.3"

let z3_executable_option fstar_exe =
  let test = run_cmd_with_code fstar_exe ["--locate_z3"; z3_version] in
  if test = 0
  then ["--z3version"; z3_version]
  else
    let opt_z3 = Filename.concat (Filename.concat (Filename.concat everparse_home "opt") "z3") ("z3-" ^ z3_version) in
    if Sys.file_exists opt_z3
    then ["--smt"; opt_z3]
    else []

let fstar_args
  krmllib
  input_stream_binding
  out_dir
=
    "--odir" :: out_dir ::
      "--cache_dir" :: out_dir ::
        (if Options.get_pulse ()
         then []
         else [ "--include"; ddd_actions_home input_stream_binding ]) @
        "--include" :: out_dir ::
            fstar_args0 krmllib

let verify_fst_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  let fstar_args = list_snoc (fstar_args (krmllib out_dir) input_stream_binding out_dir) file in
  let fstar_args = z3_executable_option fstar_exe @ fstar_args in
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args)

let fstar_modul_of_filename fst =
  let basename = remove_extension (basename fst) in
  String.concat "." (List.map String.capitalize_ascii (String.split_on_char '.' basename))

let fstar_extract_args krmllib input_stream_binding out_dir fst =
  "--extract_module" :: fstar_modul_of_filename fst ::
    "--codegen" :: "krml" ::
      (list_snoc (fstar_args krmllib input_stream_binding out_dir) fst)

let extract_fst_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  run_cmd fstar_exe (fstar_extract_args (krmllib out_dir) input_stream_binding out_dir file)

let pretty_print_source_file
  fstar_exe
  input_stream_binding
  out_dir
  file
=
  let fstar_args = list_snoc (fstar_args (krmllib out_dir) input_stream_binding out_dir) file in
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
  if Options.get_pulse ()
  then all_krmls_in_dir pulse_3d_krml_home
  else
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
  (* In --pulse mode the runtime is not a shipped library: KaRaMeL bundles the
     Pulse prelude into EverParse.h alongside the generated code. Warning 26
     (Top-type casts) is expected for the ref-dereference idiom.

     Everything that survives into that bundle is emitted `static inline` into
     the header (see the -static-header list below), so KaRaMeL writes no
     EverParse.c at all, matching the self-contained EverParse.h that the Low*
     backend ships as a prelude. *)
  let backend_args =
    if Options.get_pulse ()
    then
      (* With `--input_stream extern` (and `static`, which shares the module)
         the stream primitives are `assume val`s implemented by the client in
         C, so KaRaMeL's "no corresponding implementation" warning is expected
         and must not be fatal. The Low* backend gets this for free because it
         passes `-library EverParse3d.\*`, the whole runtime being shipped as a
         separate library; in `--pulse` mode the runtime is bundled into the
         generated code instead, so the warning has to be relaxed explicitly. *)
      let extern_warns =
        match string_of_input_stream_binding input_stream_binding with
        | "extern" | "static" -> "-2"
        | _ -> ""
      in
      (* Mirrors the Low* backend's -static-header list, minus
         EverParse3d.CopyBuffer and EverParse3d.InputStream.\*: those hold the
         `assume val`s that the client implements in C. Low* can list them
         because it also passes `-library`, which drops their declarations
         outright; with no `-library` here, KaRaMeL would instead emit them as
         `static` prototypes that never get a definition, clashing with the
         client's non-static one. Everything else in the bundle becomes
         `static inline` in the header, so no EverParse.c is emitted at all,
         matching the self-contained EverParse.h that Low* ships. *)
      "-add-include" :: "EverParse:\"EverParsePulseEndianness.h\"" ::
        "-static-header" :: "Pulse.\\*,EverParse3d.Prelude.StaticHeader,EverParse3d.ErrorCode" ::
        "-warn-error" :: Printf.sprintf "-9@4-20-26%s" extern_warns :: []
    else
      "-static-header" :: "LowParse.Low.Base,EverParse3d.Prelude.StaticHeader,EverParse3d.ErrorCode,EverParse3d.CopyBuffer,EverParse3d.InputStream.\\*" ::
        "-no-prefix" :: "LowParse.Slice" ::
          "-no-prefix" :: "LowParse.Low.BoundedInt" ::
            "-library" :: everparse_only_bundle ::
              "-warn-error" :: "-9@4-20" :: []
  in
  let krml_args =
    "-tmpdir" :: out_dir ::
      "-skip-compilation" ::
        backend_args @
                    "-fnoreturn-else" ::
                      "-fparentheses" ::
                        "-fcurly-braces" ::
                          "-fmicrosoft" ::
                          "-fno-shadow" ::
                            "-header" :: filename_concat ddd_home "noheader.txt" ::
                              "-minimal" ::
                                "-add-include" :: "\"EverParse.h\"" ::
                                  "-fextern-c" ::
                                    (* the Pulse error_handler abbreviation is
                                       parameterized by the input stream types,
                                       which KaRaMeL cannot keep opaque *)
                                    (if Options.get_pulse ()
                                     then []
                                     else ["-no-inline-type-abbrev"; "EverParse3d.Actions.Common.error_handler"]) @
                                    (if Options.get_hoist_locals ()
                                     then ["-fhoist-locals"]
                                     else []) @
                                    (if Options.get_goto_for_early_return ()
                                     then ["-goto_for_early_return"]
                                     else []) @
                                    (if Options.get_blank_lines ()
                                     then ["-fblank-lines"]
                                     else []) @
                                    (if Options.get_line_comments ()
                                     then ["-fline-comments"]
                                     else []) @
                                    (let init_locals_value = match Options.get_init_locals () with
                                     | Some v -> v
                                     | None -> "no"
                                     in
                                     ["-finitialize-locals"; init_locals_value]) @
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
    (* --pulse always skips KaRaMeL's makefiles: EverParse ships its own
       Makefile.basic, which does not need the Makefile.include that KaRaMeL
       would emit alongside it. This makes --skip_c_makefiles a no-op as far as
       KaRaMeL is concerned under --pulse. *)
    if skip_c_makefiles || Options.get_pulse ()
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
  

let call_krml input_stream_binding files_and_modules_cleanup out_dir krml_args =
  (* append the everparse and krmllib bundles to the list of arguments *)
  let krml_args = krml_args @ (
    if Options.get_pulse ()
    then
      (* The bundle's API modules -- those whose declarations stay public and so
         land in EverParse.h rather than internal/EverParse.h. Everything else
         in the bundle is marked private by KaRaMeL, and is either inlined into
         the generated validators or raised to internal/ if it survives as a
         cross translation unit symbol. Listing a module here is therefore only
         safe when *all* of its extracted declarations belong in the public ABI:
         adding EverParse3d.InputStream.Buffer, say, would also materialise
         every inline_for_extraction stream helper as a real function in
         EverParse.c, rather than letting it be inlined away. That is why the
         assumed copy-buffer projections live in a module of their own.

         Only the selected backend's module is listed: each of Buffer, Extern
         and Static owns a [@@CMacro] error_handler_macro, and making two of
         them public at once collides on EVERPARSE_ERROR_HANDLER_MACRO
         (KaRaMeL warning 23). Static re-exports Extern's instance and has no
         extracted declarations of its own, so it needs nothing public. *)
      let backend_api =
        match string_of_input_stream_binding input_stream_binding with
        | "extern" | "static" -> ["EverParse3d.InputStream.Extern"]
        | _ -> ["EverParse3d.CopyBuffer.Buffer"]
      in
      let api =
        String.concat "+" ([
            "EverParse3d.Actions.Common";
            "EverParse3d.ErrorCode";
            "EverParse3d.Prelude.StaticHeader";
          ] @ backend_api)
      in
      [
        "-bundle" ;
        "Prims,FStar.\\*,LowStar.\\*[rename=SHOULDNOTBETHERE]";
        "-bundle" ;
        Printf.sprintf "%s=Prims,LowParse.\\*,EverParse3d.\\*,Pulse.\\*[rename=EverParse,rename-prefix]" api;
      ]
    else [
        "-bundle" ;
        Printf.sprintf "%s[rename=Lib,rename-prefix]" fstar_krmllib_bundle;
        "-bundle" ;
        Printf.sprintf "EverParse3d.Actions.Common=%s[rename=EverParse,rename-prefix]" everparse_only_bundle;
  ])
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
  print_endline (Printf.sprintf "KaRaMeL found at: %s" krml);
  run_cmd krml [Printf.sprintf "@%s" argfile];
  begin match files_and_modules_cleanup with
  | Some files_and_modules ->
      Sys.remove argfile;
      List.iter (remove_fst_and_krml_files out_dir) files_and_modules
  | _ -> ()
  end

let with_preserved_everparse_h out_dir f =
  let everparse_h = filename_concat out_dir "EverParse.h" in
  let saved =
    if Sys.file_exists everparse_h
    then begin
        let cin = open_in_bin everparse_h in
        let n = in_channel_length cin in
        let buf = Bytes.create n in
        really_input cin buf 0 n;
        close_in cin;
        Some buf
      end
    else None
  in
  let res = f () in
  begin match saved with
  | None -> ()
  | Some buf ->
     let cout = open_out_bin everparse_h in
     output_bytes cout buf;
     close_out cout
  end;
  res

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
  with_preserved_everparse_h out_dir (fun () ->
    call_krml input_stream_binding (if cleanup then Some files_and_modules else None) out_dir krml_args
  )

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
  with_preserved_everparse_h out_dir (fun () ->
    call_krml input_stream_binding None out_dir krml_args
  )

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
  copy (filename_concat ddd_home ".clang-format") (filename_concat out_dir ".clang-format")

let copy_everparse_h_raw
      input_stream_binding
      out_dir =
      let dest_everparse_h = filename_concat out_dir "EverParse.h" in
      (* In --pulse mode EverParse.h is produced by KaRaMeL itself, so it must
         not be overwritten by the Low* one. *)
      if not (Options.get_pulse ())
      then begin
        let everparse_h_source = (filename_concat (ddd_actions_c_home input_stream_binding) "EverParse.h") in
        if file_exists everparse_h_source
        then copy everparse_h_source dest_everparse_h
      end else begin
        let everparse_pulse_h_source = filename_concat ddd_home "EverParsePulse.h" in
        if file_exists everparse_pulse_h_source
        then copy everparse_pulse_h_source (filename_concat out_dir "EverParsePulse.h")
        ;
        let everparse_pulse_endianness_h_source = filename_concat ddd_home "EverParsePulseEndianness.h" in
        if file_exists everparse_pulse_endianness_h_source
        then copy everparse_pulse_endianness_h_source (filename_concat out_dir "EverParsePulseEndianness.h")
      end;
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
      ?(remove_krml_produced_everparse_h: bool = false)
      (out_dir: string)
      (files_and_modules: (string * string) list)
    : unit
  =
  (* copy EverParse.h unless prevented; if prevented and Karamel produced its
   * own (due to preserved type abbreviations from -no-inline-type-abbrev),
   * remove it so the caller's expectations of "no EverParse.h here" hold.
   * In --pulse mode KaRaMeL's EverParse.h is the real one -- it carries the
   * bundled runtime -- so it must be kept. *)
  if not no_everparse_h
  then begin
      copy_everparse_h_raw input_stream_binding out_dir
    end
  else if remove_krml_produced_everparse_h && not (Options.get_pulse ())
  then begin
      let dest_everparse_h = filename_concat out_dir "EverParse.h" in
      if Sys.file_exists dest_everparse_h
      then Sys.remove dest_everparse_h
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
  (* Karamel may produce an EverParse.h containing preserved type abbreviations
   * (see -no-inline-type-abbrev). The postprocess step below copies the proper
   * full EverParse.h from the prelude, which already provides those typedefs.
   * If [no_everparse_h] is set and the file didn't exist before krml ran, we
   * also need to remove the krml-produced one. *)
  let remove_krml_produced_everparse_h = not everparse_h_existed_before in
  (* postprocess the produced C files *)
  postprocess_c input_stream_binding true true clang_format clang_format_executable copy_clang_format_opt skip_c_makefiles cleanup no_everparse_h save_hashes_opt ~remove_krml_produced_everparse_h out_dir files_and_modules

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
  (* See note in produce_and_postprocess_c. *)
  let remove_krml_produced_everparse_h = not everparse_h_existed_before in
  (* postprocess the produced .c and .h files for this module *)
  postprocess_c input_stream_binding true false clang_format clang_format_executable false true false true false ~remove_krml_produced_everparse_h out_dir [file, modul]

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

let check_all_hashes = Hashing_Hash.check_all_hashes Hashing.check_inplace_hashes_f Hashing.load_hash
