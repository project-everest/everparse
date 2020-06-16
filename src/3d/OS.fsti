module OS

(* The filename without its path *)

val basename : string -> Tot string

(* The filename without its extension *)

val remove_extension: string -> Tot string

(* The extension of the filename, including its leading . *)

val extension: string -> Tot string
