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

ghost
fn fr_view (#t #ty: Type0) (r: bprel t) (view: ty -> t) (s: FS.set asn1_id_t) (f: fr_t r s)
  (pm: perm) (y: ty) (x: Ghost.erased SB.bytes)
requires raw_view r view pm y x
ensures raw_view r view pm y x ** pure (L.framed s x)
{
  unfold (raw_view r view pm y x);
  f pm (view y) x;
  fold (raw_view r view pm y x);
}

let rec fr_crel (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) : Tot (fr_t (raw_crel id d) (FS.singleton id)) (decreases d) =
  match d with
  | CD_TERMINAL k' ->
    content_terminal_equiv id k';
    fr_ext (raw_terminal_rel id k') (raw_crel id d) () (FS.singleton id) (fr_terminal id k')
  | CD_RESTRICTED k' r ->
    content_restricted_equiv id k' r;
    fr_ext (raw_terminal_rel id k') (raw_crel id d) () (FS.singleton id) (fr_terminal id k')
  | CD_PREFIXED d' ->
    content_prefixed_equiv id d';
    fr_ext (raw_tlv id (raw_arel d')) (raw_crel id d) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_arel d') pm y x)
  | CD_SEQUENCE gitems di ->
    content_sequence_equiv id gitems di;
    fr_ext (raw_tlv id (raw_irel false di)) (raw_crel id d) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_irel false di) pm y x)
  | CD_SET ids items pf di ->
    content_set_equiv id ids items pf di;
    fr_ext (raw_tlv id (raw_irel true di)) (raw_crel id d) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_irel true di) pm y x)
  | CD_SEQUENCE_OF ne d' ->
    content_seq_of_equiv id ne d';
    fr_ext (raw_tlv id (raw_ml (raw_arel d'))) (raw_crel id d) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_ml (raw_arel d')) pm y x)
  | CD_SET_OF ne d' ->
    content_set_of_equiv id ne d';
    fr_ext (raw_tlv id (raw_ml_sorted (raw_arel d'))) (raw_crel id d) () (FS.singleton id) (fun pm y x -> fr_tlv id (raw_ml_sorted (raw_arel d')) pm y x)
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    content_adb_none_equiv id ipd prefix kid key_k ls pf pf' dsx dpre;
    fr_ext (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id d) () (FS.singleton id)
      (fun pm y x -> fr_tlv id (raw_iarel dpre (raw_sxrel kid dsx)) pm y x)
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    fr_ext (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id d) () (FS.singleton id)
      (fun pm y x -> fr_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))) pm y x)
  | CD_VIEW d' ty view mk law ->
    content_view_equiv id d' ty view mk law;
    fr_ext (raw_view (raw_crel id d') view) (raw_crel id d) () (FS.singleton id)
      (fun pm y x -> fr_view (raw_crel id d') view (FS.singleton id) (fr_crel id d') pm y x)

let lc_set (lc: list (asn1_id_t & asn1_content_k)) : FS.set asn1_id_t =
  FS.as_set' (List.Tot.map fst lc)

let rec fr_lcrel (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t) : Tot (fr_t (raw_lcrel d) (lc_set lc)) (decreases d) =
  match d with
  | LC_NIL ->
    lc_nil_equiv ();
    fr_ext (raw_false unit) (raw_lcrel d) () (lc_set lc) (fun pm y x -> fr_false unit (lc_set lc) pm y x)
  | LC_SINGLE id' #c cd ->
    lc_single_equiv id' cd;
    assert_norm (lc_set [(id', c)] == FS.union (FS.singleton id') FS.empty);
    fr_ext (raw_crel id' cd) (raw_lcrel d) () (lc_set lc)
      (fun pm y x -> fr_sub (raw_crel id' cd) (FS.singleton id') (lc_set lc) () (fr_crel id' cd) pm y x)
  | LC_CONS id' #c cd #hd2 #tl2 dtl ->
    lc_cons_equiv id' cd dtl;
    assert_norm (lc_set ((id', c) :: hd2 :: tl2) == FS.union (FS.singleton id') (lc_set (hd2 :: tl2)));
    fr_ext (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel d) () (lc_set lc)
      (fun pm y x -> fr_either (raw_crel id' cd) (raw_lcrel dtl) (FS.singleton id') (lc_set (hd2 :: tl2)) (lc_set lc) ()
        (fr_crel id' cd) (fr_lcrel dtl) pm y x)

let rec fr_arel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (~ (ASN1_ANY_ILC? k))) : Tot (fr_t (raw_arel d) s) (decreases d) =
  match d with
  | D_ILC id cd ->
    rel_ilc_equiv id cd;
    fr_ext (raw_crel id cd) (raw_arel d) () s (fr_crel id cd)
  | D_CHOICE lc pf ld ->
    rel_choice_equiv lc pf ld;
    fr_ext (raw_lcrel ld) (raw_arel d) () s
      (fun pm y x -> fr_sub (raw_lcrel ld) (lc_set lc) s () (fr_lcrel ld) pm y x)
  | D_VIEW d' ty view mk law ->
    rel_view_equiv d' ty view mk law;
    fr_ext (raw_view (raw_arel d') view) (raw_arel d) () s
      (fun pm y x -> fr_view (raw_arel d') view s (fr_arel d' ()) pm y x)

let fr_content (id: asn1_id_t) (k: asn1_content_k) : fr_t (raw_content_rel id k) (FS.singleton id) = fr_crel id (legacy_cdesc k)
let fr_lc (lc: list (asn1_id_t & asn1_content_k)) : fr_t (raw_lc_rel lc) (lc_set lc) = fr_lcrel (legacy_lcdesc lc)
let fr_k (#s: _) (k: asn1_k s) (u: squash (~ (ASN1_ANY_ILC? k))) : fr_t (raw_rel k) s = fr_arel (legacy_adesc k) u

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

ghost
fn fe_view (#t #ty: Type0) (r: bprel t) (view: ty -> t) (hd: gen_decorated_parser_twin) (f: fe_t r hd)
  (pm: perm) (y: ty) (x: Ghost.erased SB.bytes)
requires raw_view r view pm y x
ensures raw_view r view pm y x ** pure (SL.dfe hd x)
{
  unfold (raw_view r view pm y x);
  f pm (view y) x;
  fold (raw_view r view pm y x);
}

let rec fe_drel (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (u: squash (any_dec dk == false))
: Tot (fe_t (raw_drel d) (In.twin_of dk)) (decreases d)
= match d with
  | DD_PLAIN d' ->
    dec_plain_equiv d';
    fe_ext (raw_arel d') (raw_drel d) () (In.twin_of dk) (fun pm y x -> fe_framed (raw_arel d') dk (fr_arel d' ()) pm y x)
  | DD_OPTION d' ->
    dec_option_equiv d';
    fe_ext (raw_opt (raw_arel d')) (raw_drel d) () (In.twin_of dk) (fun pm y x -> fe_opt (raw_arel d') dk () (fr_arel d' ()) pm y x)
  | DD_DEFAULT id0 #k defl ->
    dec_default_equiv id0 #k defl;
    fe_ext (raw_default_rel id0 k defl) (raw_drel d) () (In.twin_of dk) (fe_default dk id0 k defl ())
  | DD_DEFAULT_RESTRICTED id0 #k r defl ->
    dec_default_restricted_equiv id0 #k r defl;
    fe_ext (raw_default_rel id0 k defl) (raw_drel d) () (In.twin_of dk) (fe_default dk id0 k defl ())
  | DD_VIEW d' ty view mk law ->
    dec_view_equiv d' ty view mk law;
    fe_ext (raw_view (raw_drel d') view) (raw_drel d) () (In.twin_of dk)
      (fun pm y x -> fe_view (raw_drel d') view (In.twin_of dk) (fe_drel d' ()) pm y x)

let fe_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (any_dec dk == false)) : fe_t (raw_dec_rel dk) (In.twin_of dk) =
  fe_drel (legacy_ddesc dk) u

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
let rec av_irel (#i: id_decs) (#ls: asn1_gen_items_l i) (#t: Type0) (d: idesc ls t) (s: FS.set asn1_id_t) (wf: squash (asn1_sequence_k_wf' i s))
: Tot (av_t (raw_irel false d) s) (decreases d)
= match d with
  | ID_NIL ->
    items_nil_equiv false;
    av_ext (raw_pure null_enc) (raw_irel false d) () s (av_nil s)
  | ID_SINGLE #_ #_ #dk dd ->
    items_single_equiv false dd;
    L.item_set_twin dk;
    if any_dec dk
    then av_none (raw_irel false d) s ()
    else av_ext (raw_drel dd) (raw_irel false d) () s (fun pm y x -> av_fe (raw_drel dd) (In.twin_of dk) s () (fe_drel dd ()) pm y x)
  | ID_CONS #s1 #d1 #dk dd dtl ->
    items_cons_equiv false dd dtl;
    join_cat_equiv false (raw_drel dd) (raw_irel false dtl);
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if any_dec dk
    then av_none (raw_irel false d) s ()
    else if PLAIN? d1
    then av_ext (raw_cat (raw_drel dd) (raw_irel false dtl)) (raw_irel false d) () s
      (fun pm y x -> av_cons_plain (raw_drel dd) (raw_irel false dtl) (In.twin_of dk) s () (fe_drel dd ()) pm y x)
    else av_ext (raw_cat (raw_drel dd) (raw_irel false dtl)) (raw_irel false d) () s
      (fun pm y x -> av_cons_opt (raw_drel dd) (raw_irel false dtl) (In.twin_of dk) s (FS.union s s1) () (fe_drel dd ())
        (av_irel dtl (FS.union s s1) ()) pm y x)
#pop-options

let av_items (#i: id_decs) (ls: asn1_gen_items_l i) (s: FS.set asn1_id_t) (wf: squash (asn1_sequence_k_wf' i s))
: av_t (raw_items_rel false ls) s
= av_irel (legacy_idesc ls) s wf
