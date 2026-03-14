module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma7
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Map = CDDL.Spec.Map

val invariant_init
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
  (em0: bool)
  (out: S.slice U8.t)
  (w0: Seq.seq U8.t)
  (size0: SZ.t)
  (count0: U64.t)
  (l: cbor_map)
  (v0: Map.t tkey (list tvalue))
: Lemma
  (requires
    Seq.length w0 == SZ.v (S.len out) /\
    SZ.v size0 <= Seq.length w0 /\
    cbor_parse_map_prefix_prop' p (U64.v count0) w0 (Seq.slice w0 0 (SZ.v size0)) /\
    (em0 == true <==> v0 == Map.empty _ _)
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em0 out w0 size0 count0 l v0 v0 0 (Some 0) true
  )
