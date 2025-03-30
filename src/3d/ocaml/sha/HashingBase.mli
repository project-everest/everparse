(* NOTE: ideally this file should be in the .. directory,
   but dune cannot handle that. So, this interface file
   MUST be copied as is for any binding to a hashing library. *)

type t

val init : unit -> t

val update : t -> Bytes.t -> unit

val finish : t -> Bytes.t

val get_current_digest : t -> Bytes.t
