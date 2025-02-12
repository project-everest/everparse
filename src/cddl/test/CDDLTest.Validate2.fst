module CDDLTest.Validate2
open CDDL.Pulse.AST.Bundle
open CDDL.Pulse.AST.Gen
include CDDLTest.Validate

module T = CDDL.Pulse.AST.Tactics

let _ : unit = _ by (FStar.Tactics.print ("parser"); FStar.Tactics.exact (`()))
[@@normalize_for_extraction (nbe :: T.bundle_steps)]
let parse_header_map = b26'.b_parser
