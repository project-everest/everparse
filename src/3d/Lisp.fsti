module Lisp
open FStar.All

val read_int_from
  (from: (unit -> ML string))
  (name: string)
: ML (string & int)

val read_bare_int_from
  (from: (unit -> ML string))
: ML int

val read_any_from
  (from: (unit -> ML string))
  (name: string)
: ML string
