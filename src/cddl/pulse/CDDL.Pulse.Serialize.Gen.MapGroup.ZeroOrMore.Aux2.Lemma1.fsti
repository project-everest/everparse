module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma1
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT

val cbor_serialize_map_insert_pre_intro
  (pe: bare_cbor_parser)
  (p: bare_cbor_map_parser)
  (m: cbor_map)
  (size0 size1 size1' size2 size2': SZ.t)
  (vk vv: cbor)
  (w_ w0 w_key w_value w_suffix: Seq.seq U8.t)
: Lemma
  (requires
    SZ.v size0 <= Seq.length w0 /\
    SZ.v size1' == SZ.v size0 + SZ.v size1 /\
    SZ.v size2' == SZ.v size1' + SZ.v size2 /\
    Seq.length w_key == SZ.v size1 /\
    Seq.length w_value == SZ.v size2 /\
    Seq.length w_ == SZ.v size2' /\
    w_ == Seq.slice
      (Seq.append (Seq.slice w0 0 (SZ.v size0))
        (Seq.append w_key (Seq.append w_value w_suffix)))
      0 (SZ.v size2') /\
    p (cbor_map_length m) (Seq.slice w0 0 (SZ.v size0)) == Some (m, SZ.v size0) /\
    pe w_key == Some (vk, SZ.v size1) /\
    pe w_value == Some (vv, SZ.v size2)
  )
  (ensures cbor_serialize_map_insert_pre p pe m size0 vk size1' vv w_)
