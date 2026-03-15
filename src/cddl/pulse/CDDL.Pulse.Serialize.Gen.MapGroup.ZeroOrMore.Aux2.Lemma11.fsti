module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma11
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Map = CDDL.Spec.Map
module EqTest = CDDL.Spec.EqTest

val invariant_excluded
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
  (vout_old: Seq.seq U8.t)
  (gk: tkey)
  (gv: tvalue)
  (min_old: nat)
  (max_old: option nat)
: Lemma
  (requires
    em == false /\
    U64.v count <> pow2 64 - 1 /\
    Seq.length vout == SZ.v (S.len out) /\
    SZ.v size <= Seq.length vout /\
    map_of_list_maps_to_nonempty v /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except min v0 v /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except max v0 v /\
    (exists (keq: EqTest.eq_test tkey) .
      impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout_old size count m v0 (map_of_list_cons keq gk gv v) min_old max_old true /\
      min == impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min_old gk gv /\
      max == impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max_old gk gv /\
      sp1.serializable gk /\ sp2.serializable gv /\
      except (sp1.serializer gk, sp2.serializer gv) == true)
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max false
  )
