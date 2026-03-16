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

val impl_serialize_map_zero_or_more_iterator_gen_invariant_implies_invariant1
  (#pe: cbor_parser)
  (#minl: (cbor_min_length pe))
  (#maxl: (cbor_max_length pe))
  (p: (cbor_map_parser minl maxl))
  (#key: typ) (#tkey: Type0)
  (sp1: (spec key tkey true))
  (#value: typ) (#tvalue: Type0)
  (#inj: bool)
  (sp2: (spec value tvalue inj))
  (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (em: bool)
  (out: S.slice U8.t)
  (vout: Seq.seq U8.t)
  (size: SZ.t)
  (count: U64.t)
  (m: cbor_map)
  (v0: Map.t tkey (list tvalue))
  (v: Map.t tkey (list tvalue))
  (min: nat)
  (max: option nat)
  (res: bool)
  (l: cbor_map)
: Lemma
  (requires impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max res l)
  (ensures impl_serialize_map_zero_or_more_iterator_gen_invariant1 p sp1 sp2 except em out vout size count m v0 v min max res)
  [SMTPat (impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max res l)]
