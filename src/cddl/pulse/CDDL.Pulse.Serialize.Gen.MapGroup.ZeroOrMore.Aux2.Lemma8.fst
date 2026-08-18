module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma8

module Map = CDDL.Spec.Map
module Set = CDDL.Spec.Set
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64

open CDDL.Spec.MapGroup

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --z3seed 42"

private
let map_nonempty_length
  (#tkey #tvalue: Type)
  (#key: typ)
  (sp1: spec key tkey true)
  (v: Map.t tkey (list tvalue))
: Lemma
  (requires
    v =!= Map.empty tkey (list tvalue) /\
    (forall (x: tkey) . Map.defined x v ==> sp1.serializable x)
  )
  (ensures Map.length v >= 1)
= if Map.length v = 0 then begin
    let s = Map.key_set sp1 v in
    let l = Set.set_as_list s in
    assert (List.Tot.length l == 0);
    assert (Map.equal v (Map.empty tkey (list tvalue)))
  end

let invariant_count_overflow
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em out vout size count m v0 v min max l
= impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max true l;
  impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max false l;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  if sp.mg_serializable v0 then begin
    assert (sp.mg_serializable v);
    assert (cbor_map_union l (sp.mg_serializer v0) == cbor_map_union m (sp.mg_serializer v));
    map_nonempty_length sp1 v;
    map_group_zero_or_more_match_item_serializer_eq sp1 sp2 except v;
    map_group_zero_or_more_match_item_serializer'_length sp1 sp2 except v;
    assert (cbor_map_length (sp.mg_serializer v) >= 1);
    if cbor_map_disjoint_tot l (sp.mg_serializer v0) then begin
      assert (cbor_map_disjoint_tot m (sp.mg_serializer v) == true);
      cbor_map_length_disjoint_union l (sp.mg_serializer v0);
      cbor_map_length_disjoint_union m (sp.mg_serializer v);
      assert (~ (FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer v0)) 64))
    end
  end

#pop-options
