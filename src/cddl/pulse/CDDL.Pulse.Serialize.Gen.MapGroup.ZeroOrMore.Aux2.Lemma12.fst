module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma12

module Map = CDDL.Spec.Map
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module EqTest = CDDL.Spec.EqTest

open CDDL.Spec.MapGroup

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --z3seed 42"

let invariant_insert_success
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em out vout size count m v0 v min max vout_old gk gv min_old max_old em_old size_old count_old m_old l
= let keq = FStar.IndefiniteDescription.indefinite_description_ghost
    (EqTest.eq_test tkey)
    (fun keq ->
      impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em_old out vout_old size_old count_old m_old v0 (map_of_list_cons keq gk gv v) min_old max_old true l /\
      min == impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min_old gk gv /\
      max == impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max_old gk gv /\
      sp1.serializable gk /\ sp2.serializable gv /\
      except (sp1.serializer gk, sp2.serializer gv) == false /\
      m == cbor_map_union m_old (cbor_map_singleton (sp1.serializer gk) (sp2.serializer gv)) /\
      ~ (cbor_map_defined (sp1.serializer gk) m_old)
    ) in
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em_old out vout_old size_old count_old m_old v0 (map_of_list_cons keq gk gv v) min_old max_old true l;
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max true l;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  // Decomposition: map_of_list_cons keq gk gv v = singleton ∪ v
  map_of_list_is_append_cons keq gk gv v;
  map_of_list_maps_to_nonempty_singleton gk (keq gk) [gv] ();
  map_of_list_is_append_serializable_elim sp1 sp2 except (Map.singleton gk (keq gk) [gv]) v (map_of_list_cons keq gk gv v);
  map_of_list_is_append_serializable_intro sp1 sp2 except (Map.singleton gk (keq gk) [gv]) v (map_of_list_cons keq gk gv v);
  map_of_list_is_append_serializable_singleton sp1 sp2 except gk (keq gk) gv;
  // From the above:
  // serializable v_old ==> serializable (singleton gk [gv]) /\ serializable v /\ disjoint ...
  // serializable (singleton gk [gv]) /\ serializable v /\ (Map.disjoint \/ cbor_map_disjoint) ==> serializable v_old
  // ser v_old == union (cbor_map_singleton vk vv) (ser v) when both serializable
  // m == union m_old (cbor_map_singleton vk vv)
  // So union m_old (ser v_old) == union m_old (union (singleton vk vv) (ser v))
  //    == union (union m_old (singleton vk vv)) (ser v) == union m (ser v)
  // From old invariant2: union l (ser v0) == union m_old (ser v_old)
  // So union l (ser v0) == union m (ser v) ✓
  // Disjoint: ~ defined vk m_old ==> disjoint m_old (singleton vk vv)
  // disjoint l (ser v0) <==> disjoint m_old (ser v_old) (old invariant2)
  //   <==> disjoint m_old (union (singleton vk vv) (ser v))
  //   <==> disjoint m_old (singleton vk vv) /\ disjoint m_old (ser v)
  // disjoint m (ser v) = disjoint (union m_old (singleton vk vv)) (ser v)
  //   <==> disjoint m_old (ser v) /\ disjoint (singleton vk vv) (ser v)
  // Since disjoint m_old (singleton vk vv) holds (from ~ defined),
  // disjoint l (ser v0) <==> disjoint m_old (ser v) /\ disjoint (singleton vk vv) (ser v)
  //   <==> disjoint m (ser v) ✓
  if sp.mg_serializable v0 then begin
    assert (sp.mg_serializable (map_of_list_cons keq gk gv v));
    assert (sp.mg_serializable v);
    cbor_map_union_assoc m_old (cbor_map_singleton (sp1.serializer gk) (sp2.serializer gv)) (sp.mg_serializer v);
    assert (cbor_map_union l (sp.mg_serializer v0) == cbor_map_union m (sp.mg_serializer v));
    assert (cbor_map_disjoint_tot l (sp.mg_serializer v0) <==> cbor_map_disjoint m (sp.mg_serializer v));
    ()
  end;
  // Backward: serializable v ==> serializable v0
  // ~ Map.defined gk v ==> Map.disjoint (singleton gk [gv]) v
  // serializable (singleton gk [gv]) /\ serializable v /\ Map.disjoint ==> serializable v_old (via _intro)
  // serializable v_old ==> serializable v0 (from old invariant2 backward)
  ()

#pop-options
