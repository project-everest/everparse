module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma9

module Map = CDDL.Spec.Map
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module EqTest = CDDL.Spec.EqTest

open CDDL.Spec.MapGroup

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --z3seed 42"

let invariant_key_ser_fail
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em out vout size count m v0 v min max vout_old gk gv min_old max_old l
= let keq = FStar.IndefiniteDescription.indefinite_description_ghost
    (EqTest.eq_test tkey)
    (fun keq ->
      impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true l /\
      min == impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min_old gk gv /\
      max == impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max_old gk gv /\
      ~ (sp1.serializable gk /\ Some? (maxl (sp1.serializer gk)) /\ Some?.v (maxl (sp1.serializer gk)) <= Seq.length vout - SZ.v size)
    ) in
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true l;
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max false l;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  // Proof of ~ valid:
  // If serializable v0 and disjoint l (ser v0), derive contradiction
  // via max_length chain showing sp1.serializable gk /\ Some? maxl(ser gk) /\ maxl(ser gk) <= len vout - size
  if sp.mg_serializable v0 then begin
    if cbor_map_disjoint_tot l (sp.mg_serializer v0) then begin
      // From old invariant2: disjoint m (ser v_old) and union equality
      assert (cbor_map_disjoint_tot m (sp.mg_serializer (map_of_list_cons keq gk gv v)) == true);
      // max_length decompositions (SMTPat should trigger, but call explicitly for safety)
      cbor_map_max_length_union maxl l (sp.mg_serializer v0);
      cbor_map_max_length_union maxl m (sp.mg_serializer (map_of_list_cons keq gk gv v));
      // From valid: Some? max_length(union l (ser v0)) and <= len vout
      // Decomposition: max_length(l) + max_sz0 = max_length(m) + max_sz_old
      // From new invariant_max: max_sz0 = max + max_sz
      // From old invariant_max: max_sz0 = max_old + max_sz_old
      // From update_max: max = max_old + maxl_gk + maxl_gv (when Some? max)
      // Combining: max_sz_old = maxl_gk + maxl_gv + max_sz
      // max_length(m) + max_sz_old <= len vout
      // size <= max_length(m) (from max_length_prop)
      // So size + maxl_gk <= len vout, i.e., maxl_gk <= len vout - size
      // Contradicts ~ (sp1.serializable gk /\ Some? maxl(ser gk) /\ maxl(ser gk) <= len vout - size)
      ()
    end
  end

#pop-options
