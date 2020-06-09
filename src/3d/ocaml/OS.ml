(* The filename without its path *)

let basename = Filename.basename

(* The filename without its extension *)

let remove_extension = Filename.remove_extension

(* The extension of the filename, including its leading . *)

let extension = Filename.extension

(* Concatenating a dir path and a filename *)

let filename_concat = Filename.concat

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

