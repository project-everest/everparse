module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma5
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

val impl_serialize_map_zero_or_more_iterator_gen_invariant_min_next
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe)
  (#maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (#key: typ) (#tkey: Type0)
  (sp1: spec key tkey true)
  (#value: typ) (#tvalue: Type0)
  (#inj: bool)
  (sp2: spec value tvalue inj)
  (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (min: nat)
  (v0 v': Map.t tkey (list tvalue))
  (gk: tkey)
  (gv: tvalue)
: Lemma
  (requires
    map_of_list_maps_to_nonempty v' /\
    (exists (v: Map.t tkey (list tvalue)) .
      impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except min v0 v /\
      (exists (eqtest: EqTest.eq_test tkey) . v == map_of_list_cons eqtest gk gv v'))
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except
      (impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min gk gv)
      v0 v'
  )
  [SMTPat (impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except
    (impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min gk gv)
    v0 v')]
