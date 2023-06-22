module Z3
include Z3.Base
open FStar.All

val with_z3
  (#a: Type)
  (f: (z3 -> ML a))
: ML a
