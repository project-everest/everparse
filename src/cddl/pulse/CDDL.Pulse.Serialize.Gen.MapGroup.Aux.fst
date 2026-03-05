module CDDL.Pulse.Serialize.Gen.MapGroup.Aux
include CDDL.Pulse.Serialize.Gen.MapGroup.Base

open Pulse.Lib.Pervasives
open CBOR.Spec.API.Type
open CBOR.Pulse.API.Base
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

let cbor_map_union_assoc_pat (m1 m2 m3: cbor_map) : Lemma
  (ensures (cbor_map_union (cbor_map_union m1 m2) m3 == cbor_map_union m1 (cbor_map_union m2 m3)))
  [SMTPatOr [
    [SMTPat (cbor_map_union (cbor_map_union m1 m2) m3)];
    [SMTPat (cbor_map_union m1 (cbor_map_union m2 m3))]
  ]]
= cbor_map_union_assoc m1 m2 m3

let cbor_map_length_disjoint_union_pat (m1 m2: cbor_map) : Lemma
  (ensures (
    cbor_map_disjoint m1 m2 ==>
    cbor_map_length (cbor_map_union m1 m2) == cbor_map_length m1 + cbor_map_length m2
  ))
  [SMTPat (cbor_map_union m1 m2)]
= Classical.move_requires (cbor_map_length_disjoint_union m1) m2

let cbor_map_max_length_union_pat
  (maxl: cbor -> option nat)
  (m1 m2: cbor_map)
: Lemma
  (ensures (cbor_map_disjoint m1 m2 ==> cbor_map_max_length maxl (cbor_map_union m1 m2) == begin match cbor_map_max_length maxl m1, cbor_map_max_length maxl m2 with
  | Some fm1, Some fm2 -> Some (fm1 + fm2)
  | _ -> None
  end))
  [SMTPat (cbor_map_max_length maxl (cbor_map_union m1 m2))]
= Classical.move_requires (cbor_map_max_length_union maxl m1) m2

let cbor_map_min_length_union_pat
  (minl: cbor -> nat)
  (m1 m2: cbor_map)
: Lemma
  (ensures (cbor_map_disjoint m1 m2 ==> cbor_map_min_length minl (cbor_map_union m1 m2) == cbor_map_min_length minl m1 + cbor_map_min_length minl m2))
  [SMTPat (cbor_map_min_length minl (cbor_map_union m1 m2))]
= Classical.move_requires (cbor_map_min_length_union minl m1) m2

inline_for_extraction
let pow2_64_m1 : U64.t = U64.uint_to_t (pow2 64 - 1)

let pow2_64_m1_eq : squash (U64.v pow2_64_m1 == pow2 64 - 1) = _ by (
  FStar.Tactics.norm [delta; zeta; iota; primops];
  FStar.Tactics.trefl ()
)

// When insert fails, key is already defined, so disjoint is false, so valid is false.
let cbor_map_disjoint_defined_false
  (l: cbor_map) (key: cbor) (value: cbor)
: Lemma
  (requires cbor_map_defined key l)
  (ensures cbor_map_disjoint_tot l (cbor_map_singleton key value) == false)
= ()

(* Helper lemmas to instantiate universal quantifiers in cbor_map_parser refinements *)

let cbor_map_min_length_instantiate
  (p: bare_cbor_map_parser)
  (minl: cbor -> nat)
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (requires cbor_map_min_length_prop p minl)
  (ensures cbor_map_min_length_prop' p minl n s)
  [SMTPat (cbor_map_min_length_prop p minl); SMTPat (p n s)]
= ()

let cbor_map_max_length_instantiate
  (p: bare_cbor_map_parser)
  (maxl: cbor -> option nat)
  (n: nat)
  (s: Seq.seq U8.t)
: Lemma
  (requires cbor_map_max_length_prop p maxl)
  (ensures cbor_map_max_length_prop' p maxl n s)
  [SMTPat (cbor_map_max_length_prop p maxl); SMTPat (p n s)]
= ()

let cbor_parse_map_prefix_full
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (n: nat) (w: Seq.seq U8.t) (l: cbor_map) (sz: nat)
: Lemma
  (requires (sz <= Seq.length w /\ p n (Seq.slice w 0 sz) == Some (l, sz)))
  (ensures (p n w == Some (l, sz)))
= Seq.lemma_eq_elim (Seq.slice (Seq.slice w 0 sz) 0 sz) (Seq.slice w 0 sz);
  assert (cbor_parse_map_prefix_prop' p n (Seq.slice w 0 sz) w)

let cbor_parse_map_prefix_slice
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (n: nat) (w: Seq.seq U8.t) (l: cbor_map) (sz: nat)
: Lemma
  (requires (sz <= Seq.length w /\ p n w == Some (l, sz)))
  (ensures (p n (Seq.slice w 0 sz) == Some (l, sz)))
= let y = Seq.slice w 0 sz in
  Seq.lemma_eq_elim (Seq.slice w 0 sz) (Seq.slice y 0 sz);
  assert (cbor_parse_map_prefix_prop' p n w y)
