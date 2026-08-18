module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma10

module Map = CDDL.Spec.Map
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module EqTest = CDDL.Spec.EqTest

open CDDL.Spec.MapGroup

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --z3seed 42"

let invariant_value_ser_fail
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em out vout size count m v0 v min max vout_old gk gv min_old max_old sz1 l
= let keq = FStar.IndefiniteDescription.indefinite_description_ghost
    (EqTest.eq_test tkey)
    (fun keq ->
      impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true l /\
      min == impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min_old gk gv /\
      max == impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max_old gk gv /\
      sp1.serializable gk /\ sz1 > 0 /\ sz1 <= Seq.length vout - SZ.v size /\
      (Some? (maxl (sp1.serializer gk)) ==> sz1 <= Some?.v (maxl (sp1.serializer gk))) /\
      ~ (sp2.serializable gv /\ Some? (maxl (sp2.serializer gv)) /\ Some?.v (maxl (sp2.serializer gv)) <= Seq.length vout - SZ.v size - sz1)
    ) in
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true l;
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max false l;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  if sp.mg_serializable v0 then begin
    if cbor_map_disjoint_tot l (sp.mg_serializer v0) then begin
      assert (cbor_map_disjoint_tot m (sp.mg_serializer (map_of_list_cons keq gk gv v)) == true);
      cbor_map_max_length_union maxl l (sp.mg_serializer v0);
      cbor_map_max_length_union maxl m (sp.mg_serializer (map_of_list_cons keq gk gv v));
      // max_length chain:
      // max_sz_old = maxl_gk + maxl_gv + max_sz (from invariant_maxes + update_max)
      // max_length(m) + max_sz_old <= len vout (from valid + equal maps)
      // size <= max_length(m) (from max_length_prop)
      // sz1 <= maxl_gk (from new precondition)
      // So maxl_gv <= len vout - size - maxl_gk <= len vout - size - sz1
      // Contradicts ~ (...maxl_gv <= len vout - size - sz1)
      ()
    end
  end

#pop-options
