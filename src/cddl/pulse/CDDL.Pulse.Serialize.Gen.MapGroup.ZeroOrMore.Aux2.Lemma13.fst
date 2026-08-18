module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma13

module Map = CDDL.Spec.Map
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module EqTest = CDDL.Spec.EqTest

open CDDL.Spec.MapGroup

#push-options "--z3rlimit 128 --fuel 1 --ifuel 1 --z3seed 42"

let invariant_insert_dup
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em out vout size count m v0 v min max vout_old gk gv min_old max_old l
= let keq = FStar.IndefiniteDescription.indefinite_description_ghost
    (EqTest.eq_test tkey)
    (fun keq ->
      impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true l /\
      min == impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min_old gk gv /\
      max == impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max_old gk gv /\
      sp1.serializable gk /\ sp2.serializable gv /\
      except (sp1.serializer gk, sp2.serializer gv) == false /\
      cbor_map_defined (sp1.serializer gk) m
    ) in
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true l;
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max false l;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  // Decompose serializable (map_of_list_cons keq gk gv v)
  map_of_list_is_append_cons keq gk gv v;
  map_of_list_maps_to_nonempty_singleton gk (keq gk) [gv] ();
  map_of_list_is_append_serializable_elim sp1 sp2 except (Map.singleton gk (keq gk) [gv]) v (map_of_list_cons keq gk gv v);
  map_of_list_is_append_serializable_intro sp1 sp2 except (Map.singleton gk (keq gk) [gv]) v (map_of_list_cons keq gk gv v);
  map_of_list_is_append_serializable_singleton sp1 sp2 except gk (keq gk) gv;
  // Chain: serializable v_old ==> ser v_old == union (singleton (ser gk, ser gv)) (ser v)
  // So cbor_map_defined (sp1.serializer gk) (ser v_old) (via singleton SMTPat + union get SMTPat)
  // From old invariant2: disjoint l (ser v0) <==> disjoint m (ser v_old)
  // But sp1.serializer gk is defined in both m (precondition) and ser v_old
  // So NOT disjoint, so NOT valid
  ()

#pop-options
