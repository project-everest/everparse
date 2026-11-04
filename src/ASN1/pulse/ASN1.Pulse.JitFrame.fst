module ASN1.Pulse.JitFrame

(* The raw bytes of a present component other than ANY are one TLV whose
   identifier is one of those of the component (`L.framed`). The JIT
   writers (ASN1.Pulse.JitWriter) use this to tell that a SEQUENCE is
   invalid as soon as one of its present components is. *)

#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel

module SB = LowParse.Spec.Base
module L = ASN1.Pulse.JitWriter.Lemmas
module PA = ASN1.Pulse.ParseAdb
module WA = ASN1.Pulse.WriteAdb
module FS = FStar.Set

let fr_t (#t: Type0) (r: bprel t) (s: FS.set asn1_id_t) =
  (pm: perm) -> (y: t) -> (x: Ghost.erased SB.bytes) ->
  stt_ghost unit emp_inames (r pm y x) (fun _ -> r pm y x ** pure (L.framed s x))

ghost
fn fr_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires raw_tlv id r pm y x
ensures raw_tlv id r pm y x ** pure (L.framed (FS.singleton id) x)
{
  unfold (raw_tlv id r pm y x);
  with c . assert (r pm y c);
  L.framed_intro id (FS.singleton id) c;
  fold (raw_tlv id r pm y x);
}

ghost
fn fr_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (s: FS.set asn1_id_t) (f: fr_t r1 s)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r2 pm y x
ensures r2 pm y x ** pure (L.framed s x)
{
  rewrite (r2 pm y x) as (r1 pm y x);
  f pm y x;
  rewrite (r1 pm y x) as (r2 pm y x);
}

ghost
fn fr_sub (#t: Type0) (r: bprel t) (s1 s2: FS.set asn1_id_t) (sq: squash (FS.subset s1 s2)) (f: fr_t r s1)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r pm y x
ensures r pm y x ** pure (L.framed s2 x)
{
  f pm y x;
  L.framed_sub s1 s2 x;
}

ghost
fn fr_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (s1 s2 s: FS.set asn1_id_t)
  (sub: squash (FS.subset s1 s /\ FS.subset s2 s)) (f1: fr_t r1 s1) (f2: fr_t r2 s2)
  (pm: perm) (y: either t1 t2) (x: Ghost.erased SB.bytes)
requires raw_either r1 r2 pm y x
ensures raw_either r1 r2 pm y x ** pure (L.framed s x)
{
  match y {
    Inl a -> {
      rewrite (raw_either r1 r2 pm y x) as (r1 pm a x);
      f1 pm a x;
      L.framed_sub s1 s x;
      rewrite (r1 pm a x) as (raw_either r1 r2 pm y x);
    }
    Inr b -> {
      rewrite (raw_either r1 r2 pm y x) as (r2 pm b x);
      f2 pm b x;
      L.framed_sub s2 s x;
      rewrite (r2 pm b x) as (raw_either r1 r2 pm y x);
    }
  }
}

ghost
fn fr_false (t: Type0) (s: FS.set asn1_id_t) (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires raw_false t pm y x
ensures raw_false t pm y x ** pure (L.framed s x)
{
  unfold (raw_false t pm y x);
  unreachable ()
}

ghost
fn fr_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k)
  (pm: perm) (y: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (x: Ghost.erased SB.bytes)
requires raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x
ensures raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x ** pure (L.framed (FS.singleton id) x)
{
  terminal_prefixed_eq id id2 k2 pm y x;
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x) as (raw_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 y) x);
  fr_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 y) x;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 y) x) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm y x);
}

let fr_terminal (id: asn1_id_t) (k: asn1_terminal_k) : fr_t (raw_terminal_rel id k) (FS.singleton id) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> fun pm y x -> fr_prefixed id id2 k2 pm y x
  | _ ->
    terminal_leaf_equiv id k;
    fr_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_leaf k) pm y x)

let fr_content (id: asn1_id_t) (k: asn1_content_k) : fr_t (raw_content_rel id k) (FS.singleton id) =
  match k with
  | ASN1_TERMINAL k' ->
    content_terminal_equiv id k';
    fr_ext (raw_terminal_rel id k') (raw_content_rel id k) () (FS.singleton id) (fr_terminal id k')
  | ASN1_RESTRICTED_TERMINAL k' r ->
    content_restricted_equiv id k' r;
    fr_ext (raw_terminal_rel id k') (raw_content_rel id k) () (FS.singleton id) (fr_terminal id k')
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv id k';
    fr_ext (raw_tlv id (raw_rel k')) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_rel k') pm y x)
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv id gitems;
    fr_ext (raw_tlv id (raw_items_rel false (dsnd gitems))) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_items_rel false (dsnd gitems)) pm y x)
  | ASN1_SET ids items pf ->
    content_set_equiv id ids items pf;
    fr_ext (raw_tlv id (raw_items_rel true items)) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_items_rel true items) pm y x)
  | ASN1_SEQUENCE_OF ne k' ->
    content_seq_of_equiv id ne k';
    fr_ext (raw_tlv id (raw_ml (raw_rel k'))) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_ml (raw_rel k')) pm y x)
  | ASN1_SET_OF ne k' ->
    content_set_of_equiv id ne k';
    fr_ext (raw_tlv id (raw_ml_sorted (raw_rel k'))) (raw_content_rel id k) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_ml_sorted (raw_rel k')) pm y x)
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      content_adb_none_equiv id ipd prefix kid key_k ls pf pf';
      fr_ext (raw_tlv id (raw_items_any_rel prefix (raw_adb_rel kid key_k ls))) (raw_content_rel id k) () (FS.singleton id)
        (fun pm y x -> fr_tlv id (raw_items_any_rel prefix (raw_adb_rel kid key_k ls)) pm y x)
    | Some fb ->
      content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf';
      fr_ext (raw_tlv id (raw_items_any_rel prefix (raw_afb_rel kid key_k ls fb))) (raw_content_rel id k) () (FS.singleton id)
        (fun pm y x -> fr_tlv id (raw_items_any_rel prefix (raw_afb_rel kid key_k ls fb)) pm y x)
    end

let lc_set (lc: list (asn1_id_t & asn1_content_k)) : FS.set asn1_id_t =
  FS.as_set' (List.Tot.map fst lc)

let rec fr_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot (fr_t (raw_lc_rel lc) (lc_set lc)) (decreases lc) =
  match lc with
  | [] ->
    lc_nil_equiv ();
    fr_ext (raw_false unit) (raw_lc_rel []) () (lc_set lc) (fun pm y x -> fr_false unit (lc_set lc) pm y x)
  | [(id', c)] ->
    lc_single_equiv id' c;
    assert_norm (lc_set [(id', c)] == FS.union (FS.singleton id') FS.empty);
    fr_ext (raw_content_rel id' c) (raw_lc_rel lc) () (lc_set lc)
      (fun pm y x -> fr_sub (raw_content_rel id' c) (FS.singleton id') (lc_set lc) () (fr_content id' c) pm y x)
  | (id', c) :: hd2 :: tl2 ->
    lc_cons_equiv id' c hd2 tl2;
    assert_norm (lc_set ((id', c) :: hd2 :: tl2) == FS.union (FS.singleton id') (lc_set (hd2 :: tl2)));
    fr_ext (raw_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2))) (raw_lc_rel lc) () (lc_set lc)
      (fun pm y x -> fr_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2)) (FS.singleton id') (lc_set (hd2 :: tl2)) (lc_set lc) ()
        (fr_content id' c) (fr_lc (hd2 :: tl2)) pm y x)

let fr_k (#s: _) (k: asn1_k s) (u: squash (~ (ASN1_ANY_ILC? k))) : fr_t (raw_rel k) s =
  match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id k';
    fr_ext (raw_content_rel id k') (raw_rel k) () s (fr_content id k')
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf;
    fr_ext (raw_lc_rel lc) (raw_rel k) () s
      (fun pm y x -> fr_sub (raw_lc_rel lc) (lc_set lc) s () (fr_lc lc) pm y x)

(* SEQUENCE components: the raw bytes of a component other than ANY are
   either framed, or empty if it is absent (`SL.dfe`); and, by the
   well-formedness of the tags, those of the components after an absent
   component do not start with any of its identifiers (`SL.avoids`) *)

module SL = ASN1.Pulse.JitWriter.SeqLemmas
module Sq = ASN1.Pulse.Sequence
module In = ASN1.Pulse.Interpreter
module PS = ASN1.Pulse.ParseSequence

[@@In.asn1_pulse_attr]
inline_for_extraction
let any_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : bool =
  match dk with
  | ASN1_PLAIN_ILC k -> ASN1_ANY_ILC? k
  | ASN1_OPTION_ILC k -> ASN1_ANY_ILC? k
  | _ -> false

let fe_t (#t: Type0) (r: bprel t) (hd: gen_decorated_parser_twin) =
  (pm: perm) -> (y: t) -> (x: Ghost.erased SB.bytes) ->
  stt_ghost unit emp_inames (r pm y x) (fun _ -> r pm y x ** pure (SL.dfe hd x))

let av_t (#t: Type0) (r: bprel t) (s: FS.set asn1_id_t) =
  (pm: perm) -> (y: t) -> (x: Ghost.erased SB.bytes) ->
  stt_ghost unit emp_inames (r pm y x) (fun _ -> r pm y x ** pure (SL.avoids s x))

ghost
fn fe_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (hd: gen_decorated_parser_twin) (f: fe_t r1 hd)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r2 pm y x
ensures r2 pm y x ** pure (SL.dfe hd x)
{
  rewrite (r2 pm y x) as (r1 pm y x);
  f pm y x;
  rewrite (r1 pm y x) as (r2 pm y x);
}

ghost
fn fe_framed (#t: Type0) (r: bprel t) (#s: _) (#d: _) (dk: asn1_decorated_k s d) (f: fr_t r s)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r pm y x
ensures r pm y x ** pure (SL.dfe (In.twin_of dk) x)
{
  f pm y x;
  SL.dfe_framed dk x;
}

ghost
fn fe_opt (#t: Type0) (r: bprel t) (#s: _) (#d: _) (dk: asn1_decorated_k s d)
  (sq: squash (ASN1_OPTION_ILC? dk \/ ASN1_DEFAULT_TERMINAL? dk \/ ASN1_DEFAULT_RESTRICTED_TERMINAL? dk)) (f: fr_t r s)
  (pm: perm) (y: option t) (x: Ghost.erased SB.bytes)
requires raw_opt r pm y x
ensures raw_opt r pm y x ** pure (SL.dfe (In.twin_of dk) x)
{
  match y {
    None -> {
      rewrite (raw_opt r pm y x) as (pure (Ghost.reveal x == Seq.empty));
      SL.dfe_empty dk;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt r pm y x);
    }
    Some z -> {
      rewrite (raw_opt r pm y x) as (r pm z x);
      f pm z x;
      SL.dfe_framed dk x;
      rewrite (r pm z x) as (raw_opt r pm y x);
    }
  }
}

ghost
fn fe_opt_nd (d: SB.bytes) (#t: Type0) (r: bprel t) (#s: _) (#d': _) (dk: asn1_decorated_k s d')
  (sq: squash (ASN1_OPTION_ILC? dk \/ ASN1_DEFAULT_TERMINAL? dk \/ ASN1_DEFAULT_RESTRICTED_TERMINAL? dk)) (f: fr_t r s)
  (pm: perm) (y: option t) (x: Ghost.erased SB.bytes)
requires raw_opt_nd d r pm y x
ensures raw_opt_nd d r pm y x ** pure (SL.dfe (In.twin_of dk) x)
{
  match y {
    None -> {
      rewrite (raw_opt_nd d r pm y x) as (pure (Ghost.reveal x == Seq.empty));
      SL.dfe_empty dk;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt_nd d r pm y x);
    }
    Some z -> {
      rewrite (raw_opt_nd d r pm y x) as (raw_opt_nd d r pm (Some z) x);
      unfold (raw_opt_nd d r pm (Some z) x);
      with c . assert (r pm z c);
      f pm z c;
      SL.dfe_empty dk;
      SL.dfe_framed dk c;
      fold (raw_opt_nd d r pm (Some z) x);
      rewrite (raw_opt_nd d r pm (Some z) x) as (raw_opt_nd d r pm y x);
    }
  }
}

let fe_default (#s: _) (#d: _) (dk: asn1_decorated_k s d) (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k)
  (sq: squash ((ASN1_DEFAULT_TERMINAL? dk \/ ASN1_DEFAULT_RESTRICTED_TERMINAL? dk) /\ s == FS.singleton id0))
: fe_t (raw_default_rel id0 k defl) (In.twin_of dk) =
  if In.adb_key_supported k
  then begin
    default_nd_equiv id0 k defl;
    fe_ext (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () (In.twin_of dk)
      (fun pm y x -> fe_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) dk () (fr_terminal id0 k) pm y x)
  end else begin
    default_opt_equiv id0 k defl;
    fe_ext (raw_opt (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () (In.twin_of dk)
      (fun pm y x -> fe_opt (raw_terminal_rel id0 k) dk () (fr_terminal id0 k) pm y x)
  end

let fe_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (any_dec dk == false)) : fe_t (raw_dec_rel dk) (In.twin_of dk) =
  match dk with
  | ASN1_PLAIN_ILC k ->
    dec_plain_equiv k;
    fe_ext (raw_rel k) (raw_dec_rel dk) () (In.twin_of dk) (fun pm y x -> fe_framed (raw_rel k) dk (fr_k k ()) pm y x)
  | ASN1_OPTION_ILC k ->
    dec_option_equiv k;
    fe_ext (raw_opt (raw_rel k)) (raw_dec_rel dk) () (In.twin_of dk) (fun pm y x -> fe_opt (raw_rel k) dk () (fr_k k ()) pm y x)
  | ASN1_DEFAULT_TERMINAL id0 #k defl ->
    dec_default_equiv id0 #k defl;
    fe_ext (raw_default_rel id0 k defl) (raw_dec_rel dk) () (In.twin_of dk) (fe_default dk id0 k defl ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl ->
    dec_default_restricted_equiv id0 #k r defl;
    fe_ext (raw_default_rel id0 k defl) (raw_dec_rel dk) () (In.twin_of dk) (fe_default dk id0 k defl ())

ghost
fn av_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (s: FS.set asn1_id_t) (f: av_t r1 s)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r2 pm y x
ensures r2 pm y x ** pure (SL.avoids s x)
{
  rewrite (r2 pm y x) as (r1 pm y x);
  f pm y x;
  rewrite (r1 pm y x) as (r2 pm y x);
}

ghost
fn av_none (#t: Type0) (r: bprel t) (s: FS.set asn1_id_t) (sq: squash (forall id . ~ (FS.mem id s)))
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r pm y x
ensures r pm y x ** pure (SL.avoids s x)
{
  SL.avoids_none s x;
}

ghost
fn av_nil (s: FS.set asn1_id_t) (pm: perm) (y: unit) (x: Ghost.erased SB.bytes)
requires raw_pure null_enc pm y x
ensures raw_pure null_enc pm y x ** pure (SL.avoids s x)
{
  unfold (raw_pure null_enc pm y x);
  SL.avoids_empty s x;
  fold (raw_pure null_enc pm y x);
}

ghost
fn av_fe (#t: Type0) (r: bprel t) (hd: gen_decorated_parser_twin) (s: FS.set asn1_id_t)
  (sq: squash (FS.disjoint s (Sq.item_set hd))) (f: fe_t r hd)
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r pm y x
ensures r pm y x ** pure (SL.avoids s x)
{
  f pm y x;
  let xx = Ghost.reveal x;
  SL.avoids_dfe s hd xx;
  ()
}

ghost
fn av_cons_plain (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (hd: gen_decorated_parser_twin) (s: FS.set asn1_id_t)
  (sq: squash (FS.disjoint s (Sq.item_set hd) /\ PLAIN? (Sq.item_dec hd))) (f: fe_t r1 hd)
  (pm: perm) (y: t1 & t2) (x: Ghost.erased SB.bytes)
requires raw_cat r1 r2 pm y x
ensures raw_cat r1 r2 pm y x ** pure (SL.avoids s x)
{
  unfold (raw_cat r1 r2 pm y x);
  with w1 w2 . assert (r1 pm (fst y) w1 ** r2 pm (snd y) w2);
  f pm (fst y) w1;
  SL.dfe_plain_ne hd w1;
  SL.avoids_dfe_cat s hd w1 w2;
  fold (raw_cat r1 r2 pm y x);
}

ghost
fn av_cons_opt (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (hd: gen_decorated_parser_twin) (s s': FS.set asn1_id_t)
  (sq: squash (FS.disjoint s (Sq.item_set hd) /\ s' == FS.union s (Sq.item_set hd))) (f: fe_t r1 hd) (a: av_t r2 s')
  (pm: perm) (y: t1 & t2) (x: Ghost.erased SB.bytes)
requires raw_cat r1 r2 pm y x
ensures raw_cat r1 r2 pm y x ** pure (SL.avoids s x)
{
  unfold (raw_cat r1 r2 pm y x);
  with w1 w2 . assert (r1 pm (fst y) w1 ** r2 pm (snd y) w2);
  f pm (fst y) w1;
  a pm (snd y) w2;
  SL.avoids_sub s s' w2;
  SL.avoids_dfe_cat s hd w1 w2;
  fold (raw_cat r1 r2 pm y x);
}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec av_items (#i: id_decs) (ls: asn1_gen_items_l i) (s: FS.set asn1_id_t) (wf: squash (asn1_sequence_k_wf' i s))
: Tot (av_t (raw_items_rel false ls) s) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv false;
    av_ext (raw_pure null_enc) (raw_items_rel false ls) () s (av_nil s)
  | ASN1_GEN_ITEMS_CONS s1 d1 dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv false dk;
    L.item_set_twin dk;
    if any_dec dk
    then av_none (raw_items_rel false ls) s ()
    else av_ext (raw_dec_rel dk) (raw_items_rel false ls) () s (fun pm y x -> av_fe (raw_dec_rel dk) (In.twin_of dk) s () (fe_dec dk ()) pm y x)
  | ASN1_GEN_ITEMS_CONS s1 d1 dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv false dk dk2 tl2;
    join_cat_equiv false (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2));
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if any_dec dk
    then av_none (raw_items_rel false ls) s ()
    else if PLAIN? d1
    then av_ext (raw_cat (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (raw_items_rel false ls) () s
      (fun pm y x -> av_cons_plain (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (In.twin_of dk) s () (fe_dec dk ()) pm y x)
    else av_ext (raw_cat (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (raw_items_rel false ls) () s
      (fun pm y x -> av_cons_opt (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (In.twin_of dk) s (FS.union s s1) () (fe_dec dk ())
        (av_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) (FS.union s s1) ()) pm y x)
#pop-options
