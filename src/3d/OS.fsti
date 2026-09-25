module OS

[@@custard_extern "OS.argv"]
val argv : unit -> FStar.All.ML (list string)

[@@custard_extern "OS.is_windows"]
val is_windows : unit -> FStar.All.ML bool

[@@custard_extern "OS.mkdir"]
val mkdir : string -> FStar.All.ML unit

[@@custard_extern "OS.dirname"]
val dirname : string -> Tot string

(* The filename without its path *)

[@@custard_extern "OS.basename"]
val basename : string -> Tot string

[@@custard_extern "OS.concat"]
val concat : string -> string -> Tot string

[@@custard_extern "OS.concat_if_not_absolute"]
val concat_if_not_absolute: string -> string -> Tot string

[@@custard_extern "OS.everparse_home"]
val everparse_home : string

(* The filename without its extension *)

[@@custard_extern "OS.remove_extension"]
val remove_extension: string -> Tot string

(* The extension of the filename, including its leading . *)

[@@custard_extern "OS.extension"]
val extension: string -> Tot string

(* The filename where all `\` have been replaced with `/` (because GNU Make uses `/` even on Windows) *)

[@@custard_extern "OS.replace_backslashes"]
val replace_backslashes: string -> Tot string

[@@custard_extern "OS.getenv_opt"]
val getenv_opt: string -> FStar.All.ML (option string)

(* Run a command *)
[@@custard_extern "OS.run_cmd"]
val run_cmd: string -> list string -> FStar.All.ML unit

(* Probe a file *)

[@@custard_extern "OS.rename"]
val rename: (src: string) -> (dst: string) -> FStar.All.ML unit

[@@custard_extern "OS.file_exists"]
val file_exists: string -> FStar.All.ML bool

[@@custard_extern "OS.file_contents"]
val file_contents: string -> FStar.All.ML string

[@@custard_extern "OS.overwrite_file"]
val overwrite_file: string -> FStar.All.ML unit

(* Write a witness into a binary file *)

[@@custard_extern "OS.write_witness_to_file"]
val write_witness_to_file: list int -> string -> FStar.All.ML unit

(* Moved here to break dependency cycle *)

[@@custard_extern "OS.int_of_string"]
val int_of_string (x:string) : FStar.All.ML int
