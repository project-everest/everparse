module Lisp
open FStar.All

val read_witness_from
  (from: (unit -> ML string))
: ML (string & Seq.seq int)

val read_int_from
  (from: (unit -> ML string))
  (name: string)
: ML (string & int)

val read_any_from
  (from: (unit -> ML string))
: ML string
