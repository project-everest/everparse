module Z3
include Z3.Base
open FStar.All

val with_z3
  (#a: Type)
  (debug: bool)
  (f: (z3 -> ML a))
: ML a
