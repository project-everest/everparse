module Hashing.Op
open FStar.All

(* Realized by Hashing_Op.t in both ocaml/Hashing_Op.ml and
   hashchk/Hashing_Op.fs *)
[@@custard_extern "Hashing_Op.t"]
val t: Type0

[@@custard_extern "Hashing_Op.hash_bool"]
val hash_bool: t -> bool -> ML unit

[@@custard_extern "Hashing_Op.hash_file"]
val hash_file: t -> string -> ML unit

[@@custard_extern "Hashing_Op.hash_file_option"]
val hash_file_option: t -> option string -> ML unit

[@@custard_extern "Hashing_Op.hash_string"]
val hash_string: t -> string -> ML unit

[@@custard_extern "Hashing_Op.hash_init"]
val hash_init: unit -> ML t

[@@custard_extern "Hashing_Op.hash_finish"]
val hash_finish: t -> ML string
