module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma2
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Map = CDDL.Spec.Map

#push-options "--z3rlimit 32"

let impl_serialize_map_zero_or_more_iterator_gen_invariant0_insert
  (#pe: cbor_parser)
  (#minl: cbor_min_length pe)
  (#maxl: cbor_max_length pe)
  (#tkey: Type)
  (#tvalue: Type)
  (p: cbor_map_parser minl maxl)
  (em': bool)
  (out: S.slice U8.t)
  (vout': Seq.seq U8.t)
  (size2': SZ.t)
  (count count': U64.t)
  (m: cbor_map)
  (vk vv: cbor)
  (v': Map.t tkey (list tvalue))
: Lemma
  (requires
    Seq.length vout' == SZ.v (S.len out) /\
    SZ.v size2' <= Seq.length vout' /\
    cbor_serialize_map_insert_post p m vk vv true (Seq.slice vout' 0 (SZ.v size2')) /\
    cbor_map_length m == U64.v count /\
    U64.v count' == U64.v count + 1 /\
    (em' == true <==> v' == Map.empty _ _)
  )
  (ensures
    impl_serialize_map_zero_or_more_iterator_gen_invariant0 p em' out vout' size2' count' (cbor_map_union m (cbor_map_singleton vk vv)) v' true
  )
= cbor_map_length_singleton vk vv;
  cbor_map_length_disjoint_union m (cbor_map_singleton vk vv)
