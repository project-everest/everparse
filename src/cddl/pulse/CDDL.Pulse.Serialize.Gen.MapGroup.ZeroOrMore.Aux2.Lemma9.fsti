module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma9
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

val invariant_key_ser_fail
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe)
  (#maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (key: typ) (tkey: Type0)
  (sp1: spec key tkey true)
  (value: typ) (tvalue: Type0)
  (inj: bool)
  (sp2: spec value tvalue inj)
  (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (em: bool)
  (out: S.slice U8.t)
  (vout: Seq.seq U8.t)
  (size: SZ.t)
  (count: U64.t)
  (m: cbor_map)
  (v0 v: Map.t tkey (list tvalue))
  (min: nat)
  (max: option nat)
: Lemma
  (requires
    (exists (em_old: bool) (vout_old: Seq.seq U8.t) (size_old: SZ.t) (count_old: U64.t) (m_old: cbor_map) (v_old_iter: Map.t tkey (list tvalue)) (min_old: nat) (max_old: option nat) .
      impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em_old out vout_old size_old count_old m_old v0 v_old_iter min_old max_old true) /\
    em == false /\
    U64.v count <> pow2 64 - 1 /\
    Seq.length vout == SZ.v (S.len out) /\
    SZ.v size <= Seq.length vout /\
    map_of_list_maps_to_nonempty v /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except min v0 v /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except max v0 v /\
    (exists (v_old: Map.t tkey (list tvalue)) (gk: tkey) (gv: tvalue) (key_eq: EqTest.eq_test tkey) .
      v_old == map_of_list_cons key_eq gk gv v /\
      ~ (sp1.serializable gk /\ Some? (maxl (sp1.serializer gk)) /\ Some?.v (maxl (sp1.serializer gk)) <= Seq.length vout - SZ.v size))
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max false
  )
