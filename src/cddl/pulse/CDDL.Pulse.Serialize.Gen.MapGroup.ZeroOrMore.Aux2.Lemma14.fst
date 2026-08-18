module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma14

module Map = CDDL.Spec.Map
module Set = CDDL.Spec.Set
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64

open CDDL.Spec.MapGroup

#push-options "--z3rlimit 512 --fuel 1 --ifuel 1 --z3seed 42"

private
let serializer_empty_is_empty
  (#tkey #tvalue: Type)
  (#key #value: typ)
  (sp1: spec key tkey true)
  (#inj: bool)
  (sp2: spec value tvalue inj)
  (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable (Map.empty tkey (list tvalue))
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializer (Map.empty tkey (list tvalue)) == cbor_map_empty
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let v : (x: Map.t tkey (list tvalue) { sp.mg_serializable x }) = Map.empty tkey (list tvalue) in
  let f = map_group_zero_or_more_match_item_serializer_op sp1 sp2 except v in
  let s = Map.key_set sp1 v in
  let l = Set.set_as_list s in
  assert (List.Tot.length l == 0);
  Set.fold_eq f cbor_map_empty s l;
  map_group_zero_or_more_match_item_serializer_eq sp1 sp2 except v

let invariant_to_post
  #pe #minl #maxl p key tkey sp1 value tvalue inj sp2 except em out vout size count m v0 v min max res l count_init size_init w_init
= impl_serialize_map_zero_or_more_iterator_gen_invariant_reveal p sp1 sp2 except em out vout size count m v0 v min max res l;
  if res
  then begin
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    assert (v == Map.empty _ _);
    assert (sp.mg_serializable v);
    assert (sp.mg_serializable v0);
    serializer_empty_is_empty sp1 sp2 except;
    assert (sp.mg_serializer v == cbor_map_empty);
    assert (cbor_map_union l (sp.mg_serializer v0) == m);
    assert (cbor_map_disjoint_tot l (sp.mg_serializer v0) == true);
    cbor_parse_map_prefix_full p (U64.v count) vout m (SZ.v size);
    cbor_map_length_disjoint_union l (sp.mg_serializer v0);
    ()
  end
  else ()

#pop-options
