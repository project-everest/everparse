let dirname = Filename.dirname

(* The filename without its path *)

let basename = Filename.basename

let concat = Filename.concat

(* The filename without its extension *)

let remove_extension = Filename.remove_extension

(* The extension of the filename, including its leading . *)

let extension = Filename.extension

(* The filename where all `\` have been replaced with `/` (because GNU Make uses `/` even on Windows) *)

let regexp_backslash = Re.Posix.compile_pat "\\\\" (* because both OCaml and POSIX regular expressions need to quote backslashes *)

let replace_backslashes (s: string) = Re.replace_string regexp_backslash ~by:"/" s

(* Concatenating a dir path and a filename *)

let filename_concat = Filename.concat

(* Read an environment variable.
   Raise a specific exception if undefined *)

exception Undefined_environment_variable of string

let getenv var =
  try
    Sys.getenv var
  with Not_found ->
    raise (Undefined_environment_variable var)

let getenv_array var =
  try
    String.split_on_char ' ' (String.trim (getenv var))
  with Undefined_environment_variable _ -> []

(* Run program prog with argument args (starting from $1, so prog need
   not be duplicated). *)

let run_cmd prog args =
  let cmd = String.concat " " (prog :: args) in
  print_endline (Printf.sprintf "Running: %s" cmd);
  let args = Array.of_list args in
  (* FIXME: use Process.execute, because we do not need to memorize
     stdin/stdout, alas it is not exposed to the .mli *)
  let out = Process.run prog args in
  List.iter print_endline out.Process.Output.stdout;
  List.iter prerr_endline out.Process.Output.stderr;
  (* FIXME: use Process.Exit.check, alas it is not exposed to the .mli
     Providing exit_status to Process.run would leave no chance to
     print out the command output *)
  match out.Process.Output.exit_status with
  | Process.Exit.Exit 0 -> ()
  | st ->
    prerr_endline (Process.Exit.to_string st);
    exit
      begin match st with
      | Process.Exit.Exit n -> n
      | _ -> 127
      end

(* Copy a file. target must be a filename *)

let copy
  source target
=
  BatFile.with_file_in source (fun cin ->
    BatFile.with_file_out target (fun cout ->
      BatIO.copy cin cout
  ))

(* Remove file, do not fail if it does not exist *)

let remove_if_exists
  file
= if Sys.file_exists file then Sys.remove file

(* Write the contents of s into the out channel, followed by an
   OS-dependent line ending. *)

let output_line out s =
  let out' = BatIO.output_channel out in
  BatIO.write_line out' s

(* Appends the contents of source_file into the cout
   channel. Implicitly converts the line endings to those of the
   running OS (that's why we are not using BatIO.copy.)  *)

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

(* Rename a file, from old name ol to new name ne *)

let rename ol ne =
  (* Sys.rename does not work across devices *)
  copy ol ne;
  Sys.remove ol


let file_exists s = Sys.file_exists s

let file_contents f =
  let ic = open_in_bin f in
  let l = in_channel_length ic in
  let s = really_input_string ic l in
  close_in ic;
  s

let write_witness_to_file w filename =
  BatFile.with_file_out filename (fun out ->
    List.iter
      (fun x ->
        BatIO.write out (char_of_int (Z.to_int x))
      )
      w
  )

let int_of_string x = Z.of_string x
