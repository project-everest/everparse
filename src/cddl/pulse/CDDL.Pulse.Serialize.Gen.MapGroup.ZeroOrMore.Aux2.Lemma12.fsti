module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma12
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Map = CDDL.Spec.Map

val invariant_insert_success
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
    impl_serialize_map_zero_or_more_iterator_gen_invariant0 p em out vout size count m v true /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except min v0 v /\
    impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except max v0 v
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max true
  )
