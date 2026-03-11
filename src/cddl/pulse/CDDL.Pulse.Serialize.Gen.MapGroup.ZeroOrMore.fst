module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore
open CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux2
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map
module SM = Pulse.Lib.SeqMatch

(* Slice iterator types and functions *)

inline_for_extraction
noeq
type map_slice_iterator_t
  (impl_elt1: Type0) (impl_elt2: Type0)
  ([@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ([@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: Type0
= {
  base: (slice (impl_elt1 & impl_elt2));
  key_eq: Ghost.erased (EqTest.eq_test (dfst spec1));
}

let rel_map_slice_iterator
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: rel (map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun s l -> rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) s.key_eq (dsnd spec1) (dsnd spec2) s.base l)

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_is_empty
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_is_empty_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _)
  (spec2: _)
  (s: _)
  (#l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  unfold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  S.pts_to_len s.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  fold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  Classical.forall_intro (map_of_list_pair_mem_fst s.key_eq l');
  (S.len s.base.s = 0sz)
}

ghost
fn map_slice_iterator_length
  (impl_elt1: Type0) (impl_elt2: Type0)
: rel_map_iterator_length _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (#spec1: _)
  (#spec2: _)
  (i: _)
  (l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  unfold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  S.pts_to_len i.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  fold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  ()
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_next
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_next_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _)
  (spec2: _)
  (pi: _)
  (#gi: _)
  (#m: _)
{
  let i = !pi;
  let r : rel (impl_elt1 & impl_elt2) (dfst spec1 & dfst spec2) = (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2));
  Trade.rewrite_with_trade
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m)
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  with l . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l);
  rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l)
    as (rel_slice_of_list r false i.base l);
  unfold (rel_slice_of_list r false i.base l);
  S.pts_to_len i.base.s;
  with s . assert (pts_to i.base.s #i.base.p s);
  SM.seq_list_match_length r _ _;
  Seq.lemma_split s 1;
  SM.seq_list_match_cons_elim _ _ r;
  with gres gv . assert (r gres gv);
  let res = S.op_Array_Access i.base.s 0sz;
  rewrite each gres as res;
  let (il, ir) = S.split i.base.s 1sz;
  with sl . assert (pts_to il #i.base.p sl);
  with sr . assert (pts_to ir #i.base.p sr);
  let i' : map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2 = {
    base = {
      s = ir;
      p = i.base.p;
    };
    key_eq = i.key_eq;
  };
  rewrite (pts_to ir #(i.base.p) sr) as (pts_to i'.base.s #i'.base.p (Seq.tail s));
  fold (rel_slice_of_list r false i'.base (List.Tot.tl l));
  rewrite (rel_slice_of_list r false i'.base (List.Tot.tl l))
    as (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base (List.Tot.tl l));
  let m' = Ghost.hide (map_of_list_pair i'.key_eq (List.Tot.tl l));
  fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
  Trade.rewrite_with_trade
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m')
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i' m');
  intro
    (Trade.trade
      (
        r res gv ** rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m'
      )
      (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m)
    )
    #(S.is_split i.base.s il ir ** pts_to il #i.base.p sl)
    fn _
  {
    unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
    with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l');
    rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l')
      as (rel_slice_of_list r false i'.base l');
    unfold (rel_slice_of_list r false i'.base l');
    with s' . assert (pts_to i'.base.s #i'.base.p s');
    SM.seq_list_match_cons_intro res (Ghost.reveal gv) s' l' r;
    rewrite (S.is_split i.base.s il ir) as (S.is_split i.base.s il i'.base.s);
    S.join il i'.base.s i.base.s;
    with sj . assert (pts_to i.base.s #i.base.p sj);
    assert (pure (Seq.equal sj (Seq.cons (Seq.index s 0) s')));
    rewrite each (Seq.cons (Seq.index s 0) s') as sj;
    fold (rel_slice_of_list
      (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2))
      false
      i.base
      (Ghost.reveal gv :: l')
    );
    fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  };
  Trade.trans_hyp_r _ _ _ _;
  Trade.trans _ _ (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m);
  Trade.rewrite_with_trade
    (r res gv)
    (dsnd spec1 (fst res) (fst gv) ** dsnd spec2 (snd res) (snd gv));
  Trade.trans_hyp_l _ (r res gv) _ _;
  pi := i';
  res
}

(* Slice sub-implementation *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_slice
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable]except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_slice_of_table key_eq r1 r2)
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let i : map_slice_iterator_t ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) = {
    base = c0;
    key_eq = key_eq;
  };
  Trade.rewrite_with_trade
    (rel_slice_of_table key_eq r1 r2 c0 v0)
    (rel_map_slice_iterator ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) i v0);
  let mut pi = i;
  let res = impl_serialize_map_zero_or_more_iterator_gen
    parse
    mk_map_entry
    insert
    key_eq
    pa1
    pa2
    va_ex
    (map_slice_iterator_t _ _)
    (rel_map_slice_iterator _ _)
    (map_slice_iterator_is_empty _ _)
    (map_slice_iterator_next _ _)
    (map_slice_iterator_length _ _)
    i
    out
    out_count
    out_size
    l;
  Trade.elim _ _;
  res
}

(* Iterator sub-implementation *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#key: Ghost.erased typ)
    (#tkey: Type0)
    (key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#value: Ghost.erased typ)
    (#tvalue: Type0)
    (#inj: Ghost.erased bool)
    (#sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2))
= impl_serialize_map_zero_or_more_iterator_gen
    parse
    mk_map_entry
    insert
    key_eq
    pa1
    pa2
    va_ex
    (map_iterator_t cbor_map_iterator_t _ _ vmatch vmatch2)
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match _ _)
    (cddl_map_iterator_is_empty map_is_empty map_next map_entry_key map_entry_value _ _)
    (cddl_map_iterator_next map_share map_gather map_next map_entry_key map_entry_value map_entry_share map_entry_gather _ _)
    (rel_map_iterator_prop' cbor_map_iterator_match)

(* Final composition: impl_serialize_map_zero_or_more *)

let impl_serialize_map_zero_or_more
  #pe #minl #maxl #p #ty #vmatch #cbor_map_iterator_t #cbor_map_iterator_match #ty2 #vmatch2
  map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather
  #ty' #ty2' #vmatch' #vmatch2'
  parse mk_map_entry insert #key #tkey key_eq #sp1 #ikey #r1 pa1 #value #tvalue #inj #sp2 #ivalue #r2 pa2 #except va_ex
= impl_serialize_map_group_either_left
    (impl_serialize_map_zero_or_more_slice
      parse mk_map_entry insert key_eq pa1 pa2 va_ex)
    (impl_serialize_map_zero_or_more_iterator
      map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather
      parse mk_map_entry insert key_eq pa1 pa2 va_ex)


