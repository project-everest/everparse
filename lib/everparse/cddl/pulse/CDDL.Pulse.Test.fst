module CDDL.Pulse.Test
include CDDL.Spec.AST.Base
include CDDL.Pulse.AST.Literal

noextract [@@noextract_to "krml"; sem_attr]
let mk_ascii_string
  (s: string)
  (sq: squash (string_is_ascii s))
: Tot ascii_string
= s

noextract [@@noextract_to "krml"]
let steps = CDDL.Pulse.AST.Tactics.steps

[@@ FStar.Tactics.postprocess_with (fun _ ->
  FStar.Tactics.norm steps;
  FStar.Tactics.trefl ())
]
let test : slice_u8_eq_ascii_string_t "bonjour, c'est moi, comment vas-tu ?" =
    (slice_u8_eq_ascii_string (mk_ascii_string "bonjour, c'est moi, comment vas-tu ?" (_ by (FStar.Tactics.norm steps; FStar.Tactics.trivial ()))))
