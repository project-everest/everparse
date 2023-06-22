module Lisp
open FStar.All

val read_witness_from
  (from: (unit -> ML string))
: ML (string & Seq.seq int)
