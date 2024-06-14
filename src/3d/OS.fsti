module OS

val dirname : string -> Tot string

(* The filename without its path *)

val basename : string -> Tot string

val concat : string -> string -> Tot string

(* The filename without its extension *)

val remove_extension: string -> Tot string

(* The extension of the filename, including its leading . *)

val extension: string -> Tot string

(* Run a command *)
val run_cmd: string -> list string -> FStar.All.ML unit

(* Probe a file *)

val file_exists: string -> FStar.All.ML bool

val file_contents: string -> FStar.All.ML string

(* Write a witness into a binary file *)

val write_witness_to_file: list int -> string -> FStar.All.ML unit

(* Timestamp, to implement the --z3_timeout option *)

val timestamp : unit -> FStar.All.ML nat

(* Moved here to break dependency cycle *)

val int_of_string (x:string) : FStar.All.ML int
