module SpecTest.Lemmas
(* Client theorems about the actions of the formats of SpecTest.3d, stated
   against the functional specification of actions (EverParse3d.Actions.Spec,
   EverParse3d.Actions.ValueSpec). The validator `validate__X` generated for a
   format `X` is typed by `as_vspec "X" (def'__X ...)`, so these theorems
   describe what the C validators do to their output parameters.

   The theorems are stated and proven in SpecTest.Lemmas.fst, which is a
   `friend` of SpecTest: the generated interface SpecTest.fsti keeps `def'__X`
   abstract, so the value type of `X` is only known to friends. This interface
   is empty, as F* only allows `friend` in modules with an interface. *)
