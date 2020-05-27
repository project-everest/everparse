let code_of_exit = function
  | Unix.WEXITED i
  | Unix.WSIGNALED i
  | Unix.WSTOPPED i
    -> i

let filename_concat = Filename.concat

let run_cmd_gen reconcat prog args =
  let cmd = String.concat " " (prog :: args) in
  print_endline (Printf.sprintf "Running: %s" cmd);
  let args' = Array.of_list (if reconcat then prog :: args else args) in (* FIXME: WHY WHY WHY do I need to recons the prog in front of the args? *)
  print_endline (Printf.sprintf "Length of args' is: %d" (Array.length args'));
  let pid = Unix.create_process prog args' Unix.stdin Unix.stdout Unix.stderr in
  let (_, res) = Unix.waitpid [] pid in
  let res = code_of_exit res in
  if res <> 0 then exit res

let run_cmd = run_cmd_gen true

(* paths *)
let fstar_home = Sys.getenv "FSTAR_HOME"
let kremlin_home = Sys.getenv "KREMLIN_HOME"
let kremlib = filename_concat kremlin_home "kremlib"
let qd_home = Sys.getenv "QD_HOME"
let lowparse_home = filename_concat (filename_concat qd_home "src") "lowparse"
let ddd_home = filename_concat (filename_concat qd_home "src") "3d"
let ddd_prelude_home = filename_concat (filename_concat (filename_concat qd_home "src") "3d") "prelude"

let regexp_fslash = Str.regexp "/"
let regexp_bslash = Str.regexp "\\"

(* fix all directory separators of a file *)
let fix_seps =
  if Sys.win32
  then Str.global_replace regexp_fslash "\\\\"
  else Str.global_replace regexp_bslash "/"

(* copy a file *)
let copy
  source target
=
  BatFile.with_file_in source (fun cin ->
    BatFile.with_file_out target (fun cout ->
      BatIO.copy cin cout
  ))

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
    then candidate
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
      target
    end
  else
    aux true [(dir, "krml")]

(* command lines *)
let fstar_args0 = [
  "--already_cached"; "Prims,LowStar,FStar,LowParse,C,Prelude,Actions,ResultOps,Spec";
  "--include"; lowparse_home;
  "--include"; kremlib;
  "--include"; ddd_prelude_home;
  "--cmi";
]

let list_snoc q a =
  q @ [a]

let verify_and_extract_module
  out_dir
  (file, modul)
: unit
=
  let fst_file = filename_concat out_dir (Printf.sprintf "%s.fst" modul) in
  let fsti_file = Printf.sprintf "%si" fst_file in
  let fstar_args =
    "--odir" :: out_dir ::
    "--cache_dir" :: out_dir ::
    "--include" :: out_dir ::
    fstar_args0
  in
  let fstar_args_fst = list_snoc fstar_args (fst_file) in
  let fstar_args_fsti = list_snoc fstar_args (fsti_file) in
  run_cmd fstar_exe ("--print_in_place" :: fstar_args_fsti);
  run_cmd fstar_exe ("--print_in_place" :: fstar_args_fst);
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args_fsti);
  run_cmd fstar_exe ("--cache_checked_modules" :: fstar_args_fst);
  let fstar_extract_args =
    "--extract_module" :: modul ::
    "--codegen" :: "Kremlin" ::
      fstar_args_fst
  in
  run_cmd fstar_exe fstar_extract_args

let ends_with
  sg suff
= let len = String.length sg in
  let len_suff = String.length suff in
  len >= len_suff &&
  String.sub sg (len - len_suff) len_suff = suff

let is_krml
  filename
= ends_with filename ".krml"

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

let all_everparse_krmls =
  all_krmls_in_dir ddd_prelude_home

let produce_c_files
  (out_dir: string)
  (files_and_modules: (string * string) list)
: unit
= 
  let krml_files = List.fold_left
    (fun accu (_, modul) -> filename_concat out_dir (Printf.sprintf "%s.krml" modul) :: accu)
    all_everparse_krmls
    files_and_modules
  in
  let krml_args =
    "-tmpdir" :: out_dir ::
    "-skip-compilation" ::
    "-bundle" :: "ResultOps=Prims,C.\\*,FStar.\\*,LowStar.\\*,LowParse.\\*,Prelude,Prelude.\\*,Actions,EverParse3d.\\*[rename=EverParse,rename-prefix]" ::
    "-warn-error" :: "-9@4" ::
    "-fnoreturn-else" ::
    "-fparentheses" ::
    "-fcurly-braces" ::
    "-fmicrosoft" ::
    "-header" :: filename_concat ddd_home "noheader.txt" ::
    "-minimal" :: 
    "-add-include" :: "EverParse:\"EverParseEndianness.h\"" ::
    "-static-header" :: "Prelude.StaticHeader,LowParse.Low.Base,Prelude,Actions,ResultOps" ::
    "-no-prefix" :: "LowParse.Slice" ::
    "-no-prefix" :: "LowParse.Low.BoundedInt" ::
    "-no-prefix" :: "EverParse3d.InputBuffer.Aux" ::
    krml_files
  in
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
  let krml = krml out_dir in
  print_endline (Printf.sprintf "KReMLin found at: %s" krml);
  run_cmd krml [Printf.sprintf "@%s" argfile]

(* Update EVERPARSEVERSION and FILENAME *)

let regexp_EVERPARSEVERSION = Str.regexp "EVERPARSEVERSION"
let regexp_FILENAME = Str.regexp "FILENAME"

let output_line out s =
  output_string out s;
  output_string out "\n"

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

let cat
  (source_file: string)
  (cout: out_channel)
= let cin = open_in source_file in
  let rec aux () =
    match
      begin try
        Some (input_line cin)
      with
        End_of_file -> None
      end
    with
    | None -> ()
    | Some ln -> output_line cout ln; aux ()
  in
  aux ();
  close_in cin

(* for OCaml < 4.06, when renaming a file, we need to remove the new file if it exists *)

let ocaml_version_lt_4_06 =
  match String.split_on_char '.' Sys.ocaml_version with
  | major :: minor :: _ ->
    int_of_string major < 4 || (major = "4" && int_of_string minor < 6)
  | _ -> failwith "Sys.ocaml_version: invalid string"

let rename ol ne =
  if ocaml_version_lt_4_06 && Sys.file_exists ne then Sys.remove ne;
  Sys.rename ol ne

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
  (out_dir: string)
  (files_and_modules: (string * string) list)
: unit
= (* produce the .checked and .krml files.
     FIXME: modules can be processed in parallel *)
  List.iter (verify_and_extract_module out_dir) files_and_modules;
  (* produce the C files *)
  produce_c_files out_dir files_and_modules;
  (* copy ancillaries *)
  copy (filename_concat ddd_home ".clang-format") (filename_concat out_dir ".clang-format");
  copy (filename_concat ddd_home (Printf.sprintf "EverParseEndianness%s.h" (if Sys.win32 then "_Windows_NT" else ""))) (filename_concat out_dir "EverParseEndianness.h");
  (* add copyright *)
  List.iter (add_copyright out_dir) files_and_modules;
  let copyright_txt = filename_concat ddd_home "copyright.txt" in
  add_copyright_header out_dir copyright_txt "EverParse.h";
  (* clang-format the files if asked for *)
  if clang_format
  then call_clang_format clang_format_executable out_dir files_and_modules;
  ()
