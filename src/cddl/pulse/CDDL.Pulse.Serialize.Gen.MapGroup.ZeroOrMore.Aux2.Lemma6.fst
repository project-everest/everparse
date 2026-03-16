module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma6
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux1
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux

module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

#push-options "--z3rlimit 512"

let invariant_max_next_aux
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
  (max: option nat)
  (v0 v v': Map.t tkey (list tvalue))
  (gk: tkey)
  (gv: tvalue)
  (eqtest: EqTest.eq_test tkey)
: Lemma
  (requires
    map_of_list_maps_to_nonempty v' /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except max v0 v /\
    v == map_of_list_cons eqtest gk gv v'
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except
      (impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max gk gv)
      v0 v'
  )
=
  map_of_list_is_append_cons eqtest gk gv v';
  map_of_list_maps_to_nonempty_singleton gk (eqtest gk) [gv] ();
  map_of_list_is_append_serializable_elim sp1 sp2 except (Map.singleton gk (eqtest gk) [gv]) v' v;
  map_of_list_is_append_serializable_intro sp1 sp2 except (Map.singleton gk (eqtest gk) [gv]) v' v;
  map_of_list_is_append_serializable_singleton sp1 sp2 except gk (eqtest gk) gv;
  if sp1.serializable gk && sp2.serializable gv then
    cbor_map_max_length_singleton maxl (sp1.serializer gk) (sp2.serializer gv)

let impl_serialize_map_zero_or_more_iterator_gen_invariant_max_next
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
  (max: option nat)
  (v0 v': Map.t tkey (list tvalue))
  (gk: tkey)
  (gv: tvalue)
= Classical.forall_intro_2 (fun (v: Map.t tkey (list tvalue)) (eqtest: EqTest.eq_test tkey) ->
    Classical.move_requires (invariant_max_next_aux p sp1 sp2 except max v0 v v' gk gv) eqtest
  )
