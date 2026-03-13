module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Proof0
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Cbor = CBOR.Spec.API.Format
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

module SM = Pulse.Lib.SeqMatch

val impl_serialize_map_zero_or_more_iterator_gen_invariant_implies_invariant0
  (#pe: cbor_parser)
  (#minl: (cbor_min_length pe))
  (#maxl: (cbor_max_length pe))
  (#tkey: Type)
  (#tvalue: Type)
  (p: (cbor_map_parser minl maxl))
  (em: bool)
  (out: S.slice U8.t)
  (vout: Seq.seq U8.t)
  (size: SZ.t)
  (count: U64.t)
  (m: cbor_map)
  (v: Map.t tkey (list tvalue))
  (res: bool)
: Lemma
  (requires impl_serialize_map_zero_or_more_iterator_gen_invariant p em out vout size count m v res)
  (ensures impl_serialize_map_zero_or_more_iterator_gen_invariant0 p em out vout size count m v res)
  [SMTPat (impl_serialize_map_zero_or_more_iterator_gen_invariant p em out vout size count m v res)]
