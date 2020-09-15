open OS

(* paths *)
let fstar_home = OS.getenv "FSTAR_HOME"
let kremlin_home = OS.getenv "KREMLIN_HOME"
let kremlib = filename_concat kremlin_home "kremlib"
let qd_home = OS.getenv "QD_HOME"
let lowparse_home = filename_concat (filename_concat qd_home "src") "lowparse"
let ddd_home = filename_concat (filename_concat qd_home "src") "3d"
let ddd_prelude_home = filename_concat (filename_concat (filename_concat qd_home "src") "3d") "prelude"

(* fstar.exe executable *)
let fstar_exe = (filename_concat (filename_concat fstar_home "bin") "fstar.exe")

(* krml: on Windows, needs to be copied into .exe *)
let krml out_dir =
  let rec aux exn = function
    | [] -> if exn then failwith "no krml found" else ""
    | (dir, file) :: q ->
      let candidate = filename_concat dir file in
      if Sys.file_exists candidate then candidate else aux exn q
  in
  let dir = kremlin_home in
  let dir_bin = filename_concat dir "bin" in
  if Sys.win32
  then
    let candidate =
      aux false [
        (dir_bin, "krml.exe"); (* binary package *)
        (dir, "krml.exe");
        (out_dir, "krml.exe"); (* has already been copied before *)
      ]
    in
    if candidate <> ""
    then (false, candidate)
    else begin
      let target = filename_concat out_dir "krml.exe" in
      if Unix.has_symlink ()
      then
        let candidate = aux true [(dir, "krml")] in
        Unix.symlink candidate target
      else begin
        (* Here, Windows cannot even read symlinks *)
        let dir' = filename_concat (filename_concat dir "_build") "src" in
        let candidate = aux true [(dir', "Kremlin.native")] in
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
  "--already_cached" :: "Prims,LowStar,FStar,LowParse,C,Prelude,Actions,ResultOps,Spec" ::
  "--include" :: lowparse_home ::
  "--include" :: kremlib ::
  "--include" :: (filename_concat kremlib "obj") ::
  "--include" :: ddd_prelude_home ::
  "--cmi" ::
  OS.getenv_array "EVERPARSE_FSTAR_OPTIONS"

let list_snoc q a =
  q @ [a]

let verify_and_extract_module
  out_dir
  (file, modul)
: unit
=
  let fst_file = filename_concat out_dir (Printf.sprintf "%s.fst" modul) in
  let types_fst_file = filename_concat out_dir (Printf.sprintf "%s.Types.fst" modul) in
  let types_modul = Printf.sprintf "%s.Types" modul in
  let fsti_file = Printf.sprintf "%si" fst_file in
  let fstar_args =
    "--odir" :: out_dir ::
    "--cache_dir" :: out_dir ::
    "--include" :: out_dir ::
    fstar_args0
  in
  let fstar_args_types_fst = list_snoc fstar_args (types_fst_file) in
  let fstar_args_fsti = list_snoc fstar_args (fsti_file) in
  let fstar_args_fst = list_snoc fstar_args (fst_file) in
  run_cmd fstar_exe ("--print_in_place" :: fstar_args_types_fst);
  run_cmd fstar_exe ("--print_in_place" :: fstar_args_fsti);
  run_cmd fstar_exe ("--print_in_place" :: fstar_args_fst);
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args_types_fst);
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args_fsti);
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args_fst);
  let fstar_extract_args fst modul =
    "--extract_module" :: modul ::
    "--codegen" :: "Kremlin" ::
      (list_snoc fstar_args fst)
  in
  run_cmd fstar_exe (fstar_extract_args types_fst_file types_modul);
  run_cmd fstar_exe (fstar_extract_args fst_file modul)

let is_krml
  filename
= Filename.check_suffix filename "krml"

let krml_args0 = OS.getenv_array "EVERPARSE_KREMLIN_OPTIONS"

let remove_fst_and_krml_files
  out_dir
  (_, modul)
=
  let root_name = filename_concat out_dir modul in
  List.iter remove_if_exists [
    Printf.sprintf "%s.Types.fst" root_name;
    Printf.sprintf "%s.fst" root_name;
    Printf.sprintf "%s.fsti" root_name;
    Printf.sprintf "%s.Types.fst.checked" root_name;
    Printf.sprintf "%s.fst.checked" root_name;
    Printf.sprintf "%s.fsti.checked" root_name;
    Printf.sprintf "%s_Types.krml" root_name;
    Printf.sprintf "%s.krml" root_name;
  ]

let produce_c_files
  (cleanup: bool)
  (out_dir: string)
  (files_and_modules: (string * string) list)
: unit
=
  let krml_files = List.fold_left
    (fun accu (_, modul) ->
       let l =
         filename_concat out_dir (Printf.sprintf "%s.krml" modul) ::
         Printf.sprintf "%sWrapper.c" modul ::
         filename_concat out_dir (Printf.sprintf "%s_Types.krml" modul) :: accu
       in
       let static_asserts = Printf.sprintf "%sStaticAssertions.c" modul in
       if Sys.file_exists (filename_concat out_dir static_asserts)
       then static_asserts :: l
       else l
     )
    []
    files_and_modules
  in
  let krml_args =
    "-tmpdir" :: out_dir ::
    "-skip-compilation" ::
     "-bundle" :: "ResultOps,Prims,C.\\*,FStar.\\*,LowStar.\\*,LowParse.\\*,Prelude,Prelude.\\*,Actions,EverParse3d.\\*[rename=EverParse,rename-prefix]" ::
    "-library" :: "ResultOps,Prims,C.\\*,FStar.\\*,LowStar.\\*,LowParse.\\*,Prelude,Prelude.\\*,Actions,EverParse3d.\\*" :: 
   "-warn-error" :: "-9@4" ::
    "-fnoreturn-else" ::
    "-fparentheses" ::
    "-fcurly-braces" ::
    "-fmicrosoft" ::
    "-header" :: filename_concat ddd_home "noheader.txt" ::
    "-minimal" ::
    "-add-include" :: "\"EverParse.h\"" ::
    "-static-header" :: "Prelude.StaticHeader,LowParse.Low.Base,Prelude,Actions,ResultOps,LowParse.Low.ErrorCode" ::
    "-no-prefix" :: "LowParse.Slice" ::
    "-no-prefix" :: "LowParse.Low.BoundedInt" ::
    "-no-prefix" :: "EverParse3d.InputBuffer.Aux" ::
    "-fextern-c" ::
    filename_concat ddd_prelude_home "LowStar_Endianness.krml" ::
    filename_concat ddd_prelude_home "LowParse_Slice.krml" ::
    filename_concat ddd_prelude_home "LowParse_Low_ErrorCode.krml" ::
    filename_concat ddd_prelude_home "ResultOps.krml" ::
    filename_concat ddd_prelude_home "EverParse3d_InputBuffer_Aux.krml" ::
    (krml_args0 @ krml_files)
  in
  (* bundle M.Types.krml into M *)
  let krml_args =
      let bundle_types = List.fold_left (fun acc (_, modul) ->
        "-bundle"::(Printf.sprintf "%s=%s.Types" modul modul)::acc) [] files_and_modules in
      krml_args@bundle_types in
  (* the argument list is too long, so we need to go through an argument file *)
  let argfile = filename_concat out_dir "kremlin_args.rsp" in
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
  print_endline (Printf.sprintf "KReMLin found at: %s" krml);
  run_cmd krml [Printf.sprintf "@%s" argfile];
  if cleanup
  then begin
    List.iter Sys.remove [
      argfile;
      filename_concat out_dir "Makefile.basic";
      filename_concat out_dir "Makefile.include";
    ];
    if is_temp_krml then Sys.remove krml;
    List.iter (remove_fst_and_krml_files out_dir) files_and_modules
  end

(* Update EVERPARSEVERSION and FILENAME *)

let regexp_EVERPARSEVERSION = Str.regexp "EVERPARSEVERSION"
let regexp_FILENAME = Str.regexp "FILENAME"

let replace_variables
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
         let ln = Str.global_replace regexp_EVERPARSEVERSION Version.everparse_version ln in
         let ln = Str.global_replace regexp_FILENAME filename ln in
         output_line channel_out ln;
         aux ()
  in
  aux ();
  close_in cin

(* Copyright headers *)

let add_copyright_header
  out_dir
  copyright_file
  target_file_base
=
  let target_file = filename_concat out_dir target_file_base in
  if Sys.file_exists target_file
  then begin
    print_endline (Printf.sprintf "Adding copyright to %s from %s" target_file copyright_file);
    let tmp = Filename.temp_file "everparseaddcopyrightheader" ".tmp" in
    rename target_file tmp;
    let cout = open_out target_file in
    replace_variables target_file_base copyright_file cout;
    cat tmp cout;
    close_out cout;
    Sys.remove tmp
  end

let add_copyright
  out_dir
  (ddd_file, modul)
=
  let copyright_file = Printf.sprintf "%s.copyright.txt" ddd_file in
  if Sys.file_exists copyright_file
  then begin
    List.iter (add_copyright_header out_dir copyright_file) [
      Printf.sprintf "%s.c" modul;
      Printf.sprintf "%s.h" modul;
      Printf.sprintf "%sWrapper.c" modul;
      Printf.sprintf "%sWrapper.h" modul;
      Printf.sprintf "%sStaticAssertions.c" modul;
    ]
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
    [
      Printf.sprintf "%s.c" modul;
      Printf.sprintf "%s.h" modul;
      Printf.sprintf "%sWrapper.c" modul;
      Printf.sprintf "%sWrapper.h" modul;
      Printf.sprintf "%sStaticAssertions.c" modul;
    ]

let collect_files
  out_dir
  files_and_modules
=
  let accu = [] in
  let accu = collect_file accu (filename_concat out_dir "EverParse.h") in
  let accu = collect_file accu (filename_concat out_dir "EverParseEndianness.h") in
  List.fold_left (collect_files_from out_dir) accu files_and_modules

(* Call clang-format *)

let call_clang_format
  (clang_format_exe0: string)
  (out_dir: string)
  (files_and_modules: (string * string) list)
=
  let clang_format_exe =
    if clang_format_exe0 <> ""
    then clang_format_exe0
    else Printf.sprintf "clang-format%s" (if Sys.win32 then ".exe" else "")
  in
  let clang_format_args =
    "-i" ::
    "--style=file" ::
    collect_files out_dir files_and_modules
  in
  run_cmd clang_format_exe clang_format_args

(* Summary *)

let postprocess
  (clang_format: bool)
  (clang_format_executable: string)
  (cleanup: bool)
  (out_dir: string)
  (files_and_modules: (string * string) list)
: unit
= (* produce the .checked and .krml files.
     FIXME: modules can be processed in parallel *)
  List.iter (verify_and_extract_module out_dir) files_and_modules;
  (* produce the C files *)
  let everparse_h = filename_concat out_dir "EverParse.h" in
  remove_if_exists everparse_h;
  produce_c_files cleanup out_dir files_and_modules;
  assert (not (Sys.file_exists everparse_h));
  (* copy ancillaries *)
  copy (filename_concat ddd_home ".clang-format") (filename_concat out_dir ".clang-format");
  copy (filename_concat (filename_concat ddd_home "prelude") "EverParse.h") everparse_h;
  copy (filename_concat ddd_home (Printf.sprintf "EverParseEndianness%s.h" (if Sys.win32 then "_Windows_NT" else ""))) (filename_concat out_dir "EverParseEndianness.h");
  (* add copyright *)
  List.iter (add_copyright out_dir) files_and_modules;
  let copyright_txt = filename_concat ddd_home "copyright.txt" in
  add_copyright_header out_dir copyright_txt "EverParse.h";
  (* clang-format the files if asked for *)
  if clang_format
  then call_clang_format clang_format_executable out_dir files_and_modules;
  ()
