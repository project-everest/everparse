module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma3
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module U8 = FStar.UInt8
module SZ = FStar.SizeT

let impl_serialize_parse_some
  (#pe: cbor_parser)
  (minl: cbor_min_length pe)
  (maxl: cbor_max_length pe)
  (#t: typ) (#tgt: Type0) (#inj: bool)
  (s: spec t tgt inj)
  (v: tgt)
  (w: Seq.seq U8.t)
  (size: SZ.t)
: Lemma
  (requires
    SZ.v size > 0 /\
    impl_serialize_post minl maxl s v w size
  )
  (ensures
    Some? (pe (Seq.slice w 0 (SZ.v size)))
  )
= ()
