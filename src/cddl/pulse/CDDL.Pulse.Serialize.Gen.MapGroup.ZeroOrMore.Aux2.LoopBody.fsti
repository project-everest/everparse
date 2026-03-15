module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.LoopBody
#lang-pulse
include CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Invariant
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Proof0
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma1
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma2
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma3
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma4
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma5
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma6
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma7
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma8
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma9
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma10
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma11
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma12
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma13

module GR = Pulse.Lib.GhostReference
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Iterator = CDDL.Pulse.Iterator.Base
module EqTest = CDDL.Spec.EqTest
module Map = CDDL.Spec.Map

inline_for_extraction noextract [@@noextract_to "krml"]
val impl_serialize_map_zero_or_more_loop_body
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ) (#[@@@erasable]tkey: Type0)
    (key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0) (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ) (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0) (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable]except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
    (is_empty: cddl_map_iterator_is_empty_gen_t _ _ iterator r)
    (next: cddl_map_iterator_next_gen_t _ _ iterator r)
    (rel_len: rel_map_iterator_length _ _ iterator r)
    (c0: iterator (Iterator.mk_spec r1) (Iterator.mk_spec r2))
    (#v0: Ghost.erased (Map.t tkey (list tvalue)))
    (out: S.slice U8.t)
    (out_count: R.ref U64.t)
    (out_size: R.ref SZ.t)
    (pres: R.ref bool)
    (pc: R.ref (iterator (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
    (pem: R.ref bool)
    (gm: GR.ref cbor_map)
    (gmin: GR.ref nat)
    (gmax: GR.ref (option nat))
    (c: Ghost.erased (iterator (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
    (v: Ghost.erased (Map.t tkey (list tvalue)))
    (em: Ghost.erased bool)
    (res: Ghost.erased bool)
    (vout: Ghost.erased (Seq.seq U8.t))
    (size: Ghost.erased SZ.t)
    (count: Ghost.erased U64.t)
    (m: Ghost.erased cbor_map)
    (min: Ghost.erased nat)
    (max: Ghost.erased (option nat))
: stt unit
    (
      pts_to out vout **
      pts_to pc c **
      r _ _ c v **
      Trade.trade (r _ _ c v) (r _ _ c0 v0) **
      pts_to pem em **
      pts_to pres res **
      GR.pts_to gm m **
      GR.pts_to gmin min **
      GR.pts_to gmax max **
      pts_to out_size size **
      pts_to out_count count **
      pure (
        impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max res /\
        Ghost.reveal res == true /\ Ghost.reveal em == false
      )
    )
    (fun _ -> exists* c v em res vout size count m min max .
      pts_to out vout **
      pts_to pc c **
      r _ _ c v **
      Trade.trade (r _ _ c v) (r _ _ c0 v0) **
      pts_to pem em **
      pts_to pres res **
      GR.pts_to gm m **
      GR.pts_to gmin min **
      GR.pts_to gmax max **
      pts_to out_size size **
      pts_to out_count count **
      pure (
        impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max res
      )
    )
