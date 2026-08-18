module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma7

#push-options "--z3rlimit 64"

let invariant_init
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em0 out w0 size0 count0 l v0
= impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em0 out w0 size0 count0 l v0 v0 0 (Some 0) true l

#pop-options
