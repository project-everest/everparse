module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2
#lang-pulse
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Proof0
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma1
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma7
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma14
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.LoopBody

module GR = Pulse.Lib.GhostReference
module S = Pulse.Lib.Slice

#push-options "--z3rlimit 256"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_iterator_gen
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
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
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
: impl_serialize_map_zero_or_more_iterator_gen_t p minl maxl #key #tkey sp1 #ikey r1 #value #tvalue #inj sp2 except #ivalue r2 iterator r
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let mut pres = true;
  let mut pc = c0;
  let em0 = is_empty _ _ c0;
  let mut pem = em0;
  Trade.refl (r _ _ c0 v0);
  S.pts_to_len out;
  let gm = GR.alloc (Ghost.reveal l);
  with size0 . assert (pts_to out_size size0);
  with w0 . assert (pts_to out w0);
  with count0 . assert (pts_to out_count count0);
  assert pure (cbor_parse_map_prefix_prop' p (U64.v count0) w0 (Seq.slice w0 0 (SZ.v size0)));
  let gmin = GR.alloc (0 <: nat);
  let gmax = GR.alloc (Some 0 <: option nat);
  invariant_init p key tkey sp1 value tvalue inj sp2 except em0 out w0 size0 count0 l v0;
  assert pure (impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em0 out w0 size0 count0 l v0 v0 0 (Some 0) true);
  while (
    !pres && not !pem
  )
  invariant exists* c v em res vout size count m min max .
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
  {
    with c_ v_ em_ res_ vout_ size_ count_ m_ min_ max_ . _;
    impl_serialize_map_zero_or_more_loop_body
      parse mk_map_entry insert key_eq pa1 pa2 va_ex iterator r is_empty next rel_len
      c0 out out_count out_size pres pc pem gm gmin gmax
      c_ v_ em_ res_ vout_ size_ count_ m_ min_ max_
  };
  with em_final . assert (pts_to pem em_final);
  with m_final . assert (GR.pts_to gm m_final);
  with min_final . assert (GR.pts_to gmin min_final);
  with max_final . assert (GR.pts_to gmax max_final);
  with c_final v_final . assert (r _ _ c_final v_final);
  Trade.elim _ _;
  GR.free gm;
  GR.free gmin;
  GR.free gmax;
  with w' . assert (pts_to out w');
  with count' . assert (pts_to out_count count');
  with size' . assert (pts_to out_size size');
  with res' . assert (pts_to pres res');
  S.pts_to_len out;
  invariant_to_post p key tkey sp1 value tvalue inj sp2 except em_final out w' size' count' m_final v0 v_final min_final max_final res' l count0 size0 w0;
  assert pure (impl_serialize_map_group_post p minl maxl count' size' l (mg_zero_or_more_match_item sp1 sp2 except) v0 w' res');
  !pres
}
