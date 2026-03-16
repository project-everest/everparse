module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.LoopBody.ParseBranch
#lang-pulse
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Proof0
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma1
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma2
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma11
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.LoopBody.InsertBranch

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

#push-options "--z3rlimit 256"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_parse_branch
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ) (#[@@@erasable]tkey: Type0)
    ([@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0) (#[@@@erasable]r1: rel ikey tkey)
    (#[@@@erasable]value: Ghost.erased typ) (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    ([@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0) (#[@@@erasable]r2: rel ivalue tvalue)
    ([@@@erasable]except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
    (is_empty: cddl_map_iterator_is_empty_gen_t _ _ iterator r)
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
    (vout_cur: Ghost.erased (Seq.seq U8.t))
    (c_cur: Ghost.erased (iterator (Iterator.mk_spec r1) (Iterator.mk_spec r2)))
    (v_cur: Ghost.erased (Map.t tkey (list tvalue)))
    (min_cur: Ghost.erased nat)
    (max_cur: Ghost.erased (option nat))
    (m_cur: Ghost.erased cbor_map)
    (count_old: Ghost.erased U64.t)
    (count': U64.t)
    (size0: SZ.t)
    (size1: SZ.t)
    (size2: SZ.t)
    (vk: Ghost.erased cbor)
    (vv: Ghost.erased cbor)
    (w0_old: Ghost.erased (Seq.seq U8.t))
    (gk: Ghost.erased tkey)
    (gv: Ghost.erased tvalue)
    (min_old: Ghost.erased nat)
    (max_old: Ghost.erased (option nat))
    (wk: Ghost.erased (Seq.seq U8.t))
    (wv: Ghost.erased (Seq.seq U8.t))
    (w_out2_tail: Ghost.erased (Seq.seq U8.t))
    (ex: bool)
    (l: Ghost.erased cbor_map)
requires
      pts_to out vout_cur **
      pts_to pc c_cur **
      r _ _ c_cur v_cur **
      Trade.trade (r _ _ c_cur v_cur) (r _ _ c0 v0) **
      pts_to pem false **
      pts_to pres true **
      GR.pts_to gm m_cur **
      GR.pts_to gmin min_cur **
      GR.pts_to gmax max_cur **
      pts_to out_size size0 **
      pts_to out_count count_old **
      pure (
        parse_branch_pure_pre p sp1 sp2 except out vout_cur v_cur min_cur max_cur m_cur count_old count' v0 size0 size1 size2 vk vv w0_old gk gv min_old max_old wk wv w_out2_tail ex l
      )
ensures exists* c v em res vout size count m min max .
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
        impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em out vout size count m v0 v min max res l
      )
{
    if (ex) {
      pres := false;
      with vout_ . assert (pts_to out vout_);
      with em_ . assert (pts_to pem em_);
      with size_ . assert (pts_to out_size size_);
      with count_ . assert (pts_to out_count count_);
      with m_ . assert (GR.pts_to gm m_);
      with min_ . assert (GR.pts_to gmin min_);
      with max_ . assert (GR.pts_to gmax max_);
      with c_ v_ . assert (r _ _ c_ v_);
      invariant_excluded p key tkey sp1 value tvalue inj sp2 except em_ out vout_ size_ count_ m_ v0 v_ min_ max_ w0_old gk gv min_old max_old l;
      assert pure (impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em_ out vout_ size_ count_ m_ v0 v_ min_ max_ false l);
    } else {
      with vout_w . assert (pts_to out vout_w);
      with c_w v_w . assert (r _ _ c_w v_w);
      with m_w . assert (GR.pts_to gm m_w);
      with count_w . assert (pts_to out_count count_w);
      impl_serialize_map_zero_or_more_insert_branch
        insert sp1 sp2 except iterator r is_empty c0
        out out_count out_size pres pc pem gm gmin gmax
        vout_w c_w v_w min_cur max_cur m_w count_w
        count' size0 size1 size2 vk vv w0_old gk gv min_old max_old wk wv w_out2_tail l;
    }
}

#pop-options
