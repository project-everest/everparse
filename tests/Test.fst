module Test

open FStar.HyperStack.ST
open C
open C.String

module TE = QD.Parse_ticketExtension

let main () : St C.exit_code =
  print (!$"QD Parsing test.\n");
  C.EXIT_SUCCESS

