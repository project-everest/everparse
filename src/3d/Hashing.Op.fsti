module Hashing.Op
open FStar.All

val t: Type0

val hash_bool: t -> bool -> ML unit

val hash_file: t -> string -> ML unit

val hash_file_option: t -> option string -> ML unit

val hash_string: t -> string -> ML unit

val hash_init: unit -> ML t

val hash_finish: t -> ML string
