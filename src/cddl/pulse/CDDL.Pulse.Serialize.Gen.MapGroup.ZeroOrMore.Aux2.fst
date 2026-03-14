module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2
#lang-pulse
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Proof0
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma1
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma2
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma3
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma4
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma5
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2.Lemma6

module GR = Pulse.Lib.GhostReference
module S = Pulse.Lib.Slice

#push-options "--z3rlimit 64"

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
  assume pure (
    impl_serialize_map_zero_or_more_iterator_gen_invariant p sp1 sp2 except em0 out w0 size0 count0 l v0 v0 0 (Some 0) true
  );
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
    let count = !out_count;
    if (count = pow2_64_m1) {
      pres := false;
      assume pure False
    } else {
      let count' = U64.add count 1uL;
      S.pts_to_len out;
      with w0 . assert (pts_to out w0);
      with min . assert (GR.pts_to gmin min);
      with max . assert (GR.pts_to gmax max);
      let (ek, ev) = next _ _ pc;
      Trade.trans _ _ (r _ _ c0 v0);
      with gk . assert (dsnd (Iterator.mk_spec r1) (fst (ek, ev)) gk);
      with gv . assert (dsnd (Iterator.mk_spec r2) (snd (ek, ev)) gv);
      GR.op_Colon_Equals gmin (impl_serialize_map_zero_or_more_iterator_gen_update_min minl sp1 sp2 except min gk gv);
      GR.op_Colon_Equals gmax (impl_serialize_map_zero_or_more_iterator_gen_update_max maxl sp1 sp2 except max gk gv);
      with min' . assert (GR.pts_to gmin min');
      with max' . assert (GR.pts_to gmax max');
      with c' v' . assert (r _ _ c' v');
      rel_len c' v';
      assert pure (impl_serialize_map_zero_or_more_iterator_gen_invariant_min p sp1 sp2 except min' v0 v');
      assert pure (impl_serialize_map_zero_or_more_iterator_gen_invariant_max p sp1 sp2 except max' v0 v');
      Trade.rewrite_with_trade
        (dsnd (Iterator.mk_spec r1) (fst (ek, ev)) gk)
        (r1 ek gk);
      let size0 = !out_size;
      let (_, out1) = slice_split out size0;
      let size1 = pa1 ek out1;
      S.pts_to_len out1;
      Trade.elim (r1 ek gk) _;
      if (size1 = 0sz) {
        Pulse.Lib.Slice.join _ _ _;
        Trade.elim_hyp_l _ _ _;
        pres := false;
        assume pure False
      } else {
        with w_out1 . assert (pts_to out1 w_out1);
        impl_serialize_parse_some minl maxl sp1 gk w_out1 size1;
        let (out1', out2) = slice_split out1 size1;
        Trade.rewrite_with_trade
          (dsnd (Iterator.mk_spec r2) (snd (ek, ev)) gv)
          (r2 ev gv);
        let size2 = pa2 ev out2;
        S.pts_to_len out2;
        Trade.elim (r2 ev gv) _;
        Trade.elim_hyp_l _ _ _;
        if (size2 = 0sz) {
          Pulse.Lib.Slice.join _ _ out1;
          Pulse.Lib.Slice.join _ _ _;
          pres := false;
          assume pure False
        } else {
          let ock = parse out1';
          let Some ck_ = ock;
          let (ck, remk) = ck_;
          with wk . assert (cbor_parse_post pe vmatch' out1' 1.0R wk (Some (ck, remk)));
          rewrite (cbor_parse_post pe vmatch' out1' 1.0R wk (Some (ck, remk)))
            as (cbor_parse_post_some pe vmatch' out1' 1.0R wk ck remk);
          unfold (cbor_parse_post_some pe vmatch' out1' 1.0R wk ck remk);
          with vk . assert (vmatch' 1.0R ck vk);
          with w_out2 . assert (pts_to out2 w_out2);
          impl_serialize_parse_some_value minl maxl sp2 gv w_out2 size2;
          let (out2', out2_tail) = slice_split out2 size2;
          with w_out2_tail . assert (pts_to out2_tail w_out2_tail);
          let ocv = parse out2';
          let Some cv_ = ocv;
          let (cv, remv) = cv_;
          with wv . assert (cbor_parse_post pe vmatch' out2' 1.0R wv (Some (cv, remv)));
          rewrite (cbor_parse_post pe vmatch' out2' 1.0R wv (Some (cv, remv)))
            as (cbor_parse_post_some pe vmatch' out2' 1.0R wv cv remv);
          unfold (cbor_parse_post_some pe vmatch' out2' 1.0R wv cv remv);
          with vv . assert (vmatch' 1.0R cv vv);
          let ce = mk_map_entry ck cv;
          let ex = va_ex ce;
          Trade.elim (vmatch2' 1.0R ce _) _;
          Trade.elim (vmatch' 1.0R ck _ ** _) _;
          Trade.elim (vmatch' 1.0R cv _ ** _) _;
          Pulse.Lib.Slice.join _ _ out2;
          Pulse.Lib.Slice.join _ _ out1;
          Pulse.Lib.Slice.join _ _ _;
          S.pts_to_len out;
          if (ex) {
            pres := false;
            assume pure False
          } else {
            let size1' = SZ.add size0 size1;
            let size2' = SZ.add size1' size2;
            let (out_, _) = slice_split out size2';
            with w_ . assert (pts_to out_ w_);
            with m . assert (GR.pts_to gm m);
            cbor_serialize_map_insert_pre_intro pe p m size0 size1 size1' size2 size2' vk vv w_ w0 wk wv w_out2_tail;
            let no_dup = insert out_ m size0 vk size1' vv;
            S.pts_to_len out_;
            Pulse.Lib.Slice.join _ _ _;
            S.pts_to_len out;
            if (no_dup) {
              pem := is_empty _ _ !pc;
              out_size := size2';
              out_count := count';
              GR.op_Colon_Equals gm (cbor_map_union m (cbor_map_singleton vk vv));
              with vout' . assert (pts_to out vout');
              with em' . assert (pts_to pem em');
              with c' v' . assert (r _ _ c' v');
              impl_serialize_map_zero_or_more_iterator_gen_invariant0_insert p em' out vout' size2' count count' m vk vv v';
              assume pure False
            } else {
              pres := false;
              assume pure False
            }
          }
        }
      }
    }
  };
  Trade.elim _ _;
  GR.free gm;
  GR.free gmin;
  GR.free gmax;
  with w' . assert (pts_to out w');
  with count' . assert (pts_to out_count count');
  with size' . assert (pts_to out_size size');
  with res' . assert (pts_to pres res');
  assume pure (impl_serialize_map_group_post p minl maxl count' size' l (mg_zero_or_more_match_item sp1 sp2 except) v0 w' res');
  !pres
}
