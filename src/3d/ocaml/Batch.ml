let code_of_exit = function
  | Unix.WEXITED i
  | Unix.WSIGNALED i
  | Unix.WSTOPPED i
    -> i

let filename_concat = Printf.sprintf "%s/%s" 

let filename_quote s = s

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

(* fix all directory separators of a file *)
let fix_seps =
  if Sys.win32
  then Str.global_replace (Str.regexp "/") "\\\\"
  else Str.global_replace (Str.regexp "\\") "/"

(* copy a file *)
let copy
  source target
=
  let cp =
    if Sys.win32
    then (filename_concat ddd_home "cp.bat")
    else "cp"
  in
  run_cmd cp [ fix_seps source; fix_seps target ]

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
  "--cache_checked_modules";
  "--already_cached"; "FStar,LowStar,C.Spec.Loops,LowParse";
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
    fstar_args0
  in
  run_cmd fstar_exe (list_snoc fstar_args (fsti_file));
  run_cmd fstar_exe (list_snoc fstar_args (fst_file));
  let fstar_extract_args =
    "--extract_module" :: modul ::
    "--codegen" :: "Kremlin" ::
    fstar_args
  in
  run_cmd fstar_exe (list_snoc fstar_extract_args (fst_file))

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

let postprocess
  (out_dir: string)
  (files_and_modules: (string * string) list)
: unit
= (* produce the .checked and .krml files.
     FIXME: modules can be processed in parallel *)
  List.iter (verify_and_extract_module out_dir) files_and_modules;
  (* produce the C files *)
  produce_c_files out_dir files_and_modules;
  (* copy ancillaries *)
  copy (filename_concat ddd_home ".clang-format") out_dir;
  copy (filename_concat ddd_home (Printf.sprintf "EverParseEndianness%s.h" (if Sys.win32 then "_Windows_NT" else ""))) (filename_concat out_dir "EverParseEndianness.h");
  ()
