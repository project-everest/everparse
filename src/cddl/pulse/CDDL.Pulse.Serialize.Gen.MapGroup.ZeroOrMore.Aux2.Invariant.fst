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

let impl_serialize_map_zero_or_more_iterator_gen_invariant_min
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
  (n: nat)
  (v0: Map.t tkey (list tvalue))
  (v: Map.t tkey (list tvalue))
: Tot prop
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  sp.mg_serializable v0 ==> (
    sp.mg_serializable v /\ (
      let min_sz0 = cbor_map_min_length minl (sp.mg_serializer v0) in
      let min_sz = cbor_map_min_length minl (sp.mg_serializer v) in
      min_sz0 == n + min_sz
    )
  )

let impl_serialize_map_zero_or_more_iterator_gen_update_min
  (#pe: cbor_parser)
  (minl: (cbor_min_length pe))
  (#key: typ) (#tkey: Type0)
  (sp1: (spec key tkey true))
  (#value: typ) (#tvalue: Type0)
  (#inj: bool)
  (sp2: (spec value tvalue inj))
  (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (n: nat)
  (k: tkey)
  (v: tvalue)
: Tot nat
= if sp1.serializable k && sp2.serializable v
  then n + minl (sp1.serializer k) + minl (sp2.serializer v)
  else 0 (* dummy *)

let impl_serialize_map_zero_or_more_iterator_gen_invariant_max
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
  (n: option nat)
  (v0: Map.t tkey (list tvalue))
  (v: Map.t tkey (list tvalue))
: Tot prop
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  sp.mg_serializable v0 ==> (
    sp.mg_serializable v /\ (
      let max_sz0 = cbor_map_max_length maxl (sp.mg_serializer v0) in
      let max_sz = cbor_map_max_length maxl (sp.mg_serializer v) in
      (Some? max_sz0 ==> (
        Some? n /\
        Some? max_sz /\
        Some?.v max_sz0 == Some?.v n + Some?.v max_sz
      ))
    )
  )

let impl_serialize_map_zero_or_more_iterator_gen_update_max
  (#pe: cbor_parser)
  (maxl: (cbor_max_length pe))
  (#key: typ) (#tkey: Type0)
  (sp1: (spec key tkey true))
  (#value: typ) (#tvalue: Type0)
  (#inj: bool)
  (sp2: (spec value tvalue inj))
  (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (n: option nat)
  (k: tkey)
  (v: tvalue)
: Tot (option nat)
= match n with
  | None -> None
  | Some n' ->
    if sp1.serializable k && sp2.serializable v
    then match maxl (sp1.serializer k) with
    | None -> None
    | Some n1 ->
      match maxl (sp2.serializer v) with
      | None -> None
      | Some n2 -> Some (n' + n1 + n2)
    else None (* dummy *)

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

let impl_serialize_map_zero_or_more_iterator_gen_invariant1
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
: prop
= impl_serialize_map_zero_or_more_iterator_gen_invariant0 p em out vout size count m v res /\
  impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except min v0 v /\
  impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except max v0 v 

let impl_serialize_map_zero_or_more_iterator_gen_invariant
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
: prop
= impl_serialize_map_zero_or_more_iterator_gen_invariant1 p sp1 sp2 except em out vout size count m v0 v min max res
