module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux1

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

inline_for_extraction noextract [@@noextract_to "krml";
  FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trefl ())
]
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

let impl_serialize_map_zero_or_more_iterator_gen_invariant0
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
: prop
=
      Seq.length vout == SZ.v (S.len out) /\
      SZ.v size <= Seq.length vout /\
      (
        res == true ==> (
          cbor_map_length m == U64.v count /\
          p (U64.v count) (Seq.slice vout 0 (SZ.v size)) == Some (m, SZ.v size) /\
          (em == true <==> v == Map.empty _ _)
        )
      )

let impl_serialize_map_zero_or_more_iterator_gen_invariant
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
: prop
= impl_serialize_map_zero_or_more_iterator_gen_invariant0 p em out vout size count m v res
