module Z3
include Z3.Base
open FStar.All

val with_z3
  (#a: Type)
  (debug: bool)
  (f: (z3 -> ML a))
: ML a

val z3_thread : Type0

val with_z3_thread
  (debug: bool)
  (f: (z3 -> ML unit))
: ML z3_thread

val wait_for_z3_thread
  (thread: z3_thread)
: ML unit
