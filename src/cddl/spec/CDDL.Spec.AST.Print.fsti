module CDDL.Spec.AST.Print
include CDDL.Spec.AST.Base

val typ_to_string
  (t: typ)
: Tot string

val group_to_string
  (t: group)
: Tot string

val program_to_string
  (t: program)
: Tot string
