module ASN1.Pulse.RawVConv
#lang-pulse

(* From the typed relation of parsers, `ASN1.Pulse.Rel.arel d pm x y`
   (`y: asn1_t k`), to the value-level relation of writers,
   `ASN1.Pulse.RawVRel.raw_varel d pm x (forget k y)`, with a trade back.
   This lets a user hand a parsed (or otherwise typed) value to the writer
   `ASN1.Pulse.RawJitWriter.jit_write_raw_d`, see `write_typed_d` below.
   It mirrors `ASN1.Pulse.RawValueRel.asn1_rel_to_raw` on descriptors. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props
open ASN1.Pulse.RawValueRel
open ASN1.Pulse.RawVRel

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module It = LowParse.PulseParse.Iterator
module ItR = LowParse.PulseParse.Iterator.Rel
module PS = ASN1.Pulse.ParseSequence
module PA = ASN1.Pulse.ParseAdb
module AL = ASN1.Pulse.ParseAdb.Lemmas
module RS = ASN1.Pulse.RelShare
module T = FStar.Tactics
module Trade = Pulse.Lib.Trade

(* The fallback of an ANY DEFINED BY, as in `crel` *)

let tfbr (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
: perm -> (asn1_terminal_impl_t key_k & tfb) -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop
= fun pm (z: asn1_terminal_impl_t key_k & tfb) key (v: asn1_sequence_t_core (dsnd gfb)) ->
    asn1_terminal_rel key_k pm (fst z) key ** irel dfb pm (snd z) v

(* Equations, so that proofs need not unfold the relation of a whole
   descriptor *)

let solve_tequiv () : T.Tac unit =
  T.norm [delta_only [`%pequiv]];
  let _ = T.forall_intros () in
  T.norm [delta_only [`%arel; `%crel; `%sxrel; `%fxrel; `%lcrel; `%drel; `%irel; `%iarel; `%tfbr; `%RS.prel_default; `%prel_pair; `%prel_option; `%AL.ady; `%AL.ady_fb]; zeta; iota];
  T.trefl ()

let trel_ilc_equiv (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t)
: Lemma (pequiv #t #(asn1_content_t k) (crel cd) (arel (D_ILC id cd)))
= assert (pequiv #t #(asn1_content_t k) (crel cd) (arel (D_ILC id cd))) by (solve_tequiv ())

let trel_choice_equiv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (#t: Type0) (ld: lcdesc lc t)
: Lemma (pequiv #t #(make_gen_choice_type (asn1_lc_t lc)) (lcrel ld) (arel (D_CHOICE lc pf ld)))
= assert (pequiv #t #(make_gen_choice_type (asn1_lc_t lc)) (lcrel ld) (arel (D_CHOICE lc pf ld))) by (solve_tequiv ())

let trel_any_equiv (_: unit)
: Lemma (pequiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (arel D_ANY))
= assert (pequiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (arel D_ANY)) by (solve_tequiv ())

let trel_view_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (pequiv #ty #(asn1_t k) (vview (arel d) view) (arel (D_VIEW d ty view mk law)))
= assert (pequiv #ty #(asn1_t k) (vview (arel d) view) (arel (D_VIEW d ty view mk law))) by (T.norm [delta_only [`%vview]]; solve_tequiv ())

let tcontent_terminal_equiv (k: asn1_terminal_k)
: Lemma (pequiv #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) (crel (CD_TERMINAL k)))
= assert (pequiv #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) (crel (CD_TERMINAL k))) by (solve_tequiv ())

let tcontent_restricted_equiv (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (pequiv #(asn1_terminal_impl_t k) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (crel (CD_RESTRICTED k r)))
= assert_norm (pequiv #(asn1_terminal_impl_t k) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (crel (CD_RESTRICTED k r)))

let tcontent_prefixed_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #t #(asn1_t k) (arel d) (crel (CD_PREFIXED d)))
= assert (pequiv #t #(asn1_t k) (arel d) (crel (CD_PREFIXED d))) by (solve_tequiv ())

let tcontent_sequence_equiv (gitems: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd gitems) t)
: Lemma (pequiv #t #(asn1_sequence_t_core (dsnd gitems)) (irel di) (crel (CD_SEQUENCE gitems di)))
= assert (pequiv #t #(asn1_sequence_t_core (dsnd gitems)) (irel di) (crel (CD_SEQUENCE gitems di))) by (solve_tequiv ())

let tcontent_set_equiv (ids: _) (items: asn1_gen_items_l ids) (pf: _) (#t: Type0) (di: idesc items t)
: Lemma (pequiv #t #(asn1_sequence_t_core items) (irel di) (crel (CD_SET ids items pf di)))
= assert (pequiv #t #(asn1_sequence_t_core items) (irel di) (crel (CD_SET ids items pf di))) by (solve_tequiv ())

let tml_rel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : prel (ml t) (list (asn1_t k)) =
  It.mixed_list_match (arel d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k)

let tcontent_seq_of_eq (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (crel (CD_SEQUENCE_OF ne d) pm x y == tml_rel d pm x (RS.seq_of_up ne k y))
= assert (crel (CD_SEQUENCE_OF ne d) pm x y == tml_rel d pm x (RS.seq_of_up ne k y))
    by (T.norm [delta_only [`%crel; `%tml_rel; `%RS.seq_of_up]; iota; zeta]; T.trefl ())

let tcontent_set_of_eq (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (y: asn1_content_t (ASN1_SET_OF ne k))
: Lemma (crel (CD_SET_OF ne d) pm x y == tml_rel d pm x (RS.set_of_up ne k y))
= assert (crel (CD_SET_OF ne d) pm x y == tml_rel d pm x (RS.set_of_up ne k y))
    by (T.norm [delta_only [`%crel; `%tml_rel; `%RS.set_of_up]; iota; zeta]; T.trefl ())

let tcontent_adb_none_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#ts: Type0) (dsx: sxdesc key_k ls ts) (#t: Type0) (dpre: iadesc prefix ts t)
: Lemma (pequiv #t #(asn1_sequence_any_t_core prefix (AL.ady key_k ls)) (iarel dpre #(AL.ady key_k ls) (sxrel dsx)) (crel (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre)))
= assert (pequiv #t #(asn1_sequence_any_t_core prefix (AL.ady key_k ls)) (iarel dpre #(AL.ady key_k ls) (sxrel dsx)) (crel (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre))) by (solve_tequiv ())

let tcontent_adb_some_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts) (#t: Type0) (dpre: iadesc prefix ts t)
: Lemma (pequiv #t #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
    (iarel dpre #(AL.ady_fb key_k ls fb) (fxrel dfx (asn1_sequence_t_core (dsnd fb)) (tfbr key_k #fb dfb)))
    (crel (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre)))
= assert (pequiv #t #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
    (iarel dpre #(AL.ady_fb key_k ls fb) (fxrel dfx (asn1_sequence_t_core (dsnd fb)) (tfbr key_k #fb dfb)))
    (crel (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre))) by (solve_tequiv ())

let tcontent_view_equiv (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (pequiv #ty #(asn1_content_t k) (vview (crel d) view) (crel (CD_VIEW d ty view mk law)))
= assert (pequiv #ty #(asn1_content_t k) (vview (crel d) view) (crel (CD_VIEW d ty view mk law))) by (T.norm [delta_only [`%vview]]; solve_tequiv ())

let tdec_plain_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #t #(asn1_t k) (arel d) (drel (DD_PLAIN d)))
= assert (pequiv #t #(asn1_t k) (arel d) (drel (DD_PLAIN d))) by (solve_tequiv ())

let tdec_option_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (pequiv #(option t) #(option (asn1_t k)) (prel_option (arel d)) (drel (DD_OPTION d)))
= assert (pequiv #(option t) #(option (asn1_t k)) (prel_option (arel d)) (drel (DD_OPTION d))) by (solve_tequiv ())

let tdec_default_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (pequiv #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (RS.prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (drel (DD_DEFAULT id0 #k defv)))
= assert_norm (pequiv #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (RS.prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (drel (DD_DEFAULT id0 #k defv)))

let tdec_default_restricted_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (pequiv #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (drel (DD_DEFAULT_RESTRICTED id0 #k r defv)))
= assert_norm (pequiv #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (drel (DD_DEFAULT_RESTRICTED id0 #k r defv)))

let tdec_view_equiv (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (pequiv #ty #(asn1_decorated_t_core dk) (vview (drel d) view) (drel (DD_VIEW d ty view mk law)))
= assert (pequiv #ty #(asn1_decorated_t_core dk) (vview (drel d) view) (drel (DD_VIEW d ty view mk law))) by (T.norm [delta_only [`%vview]]; solve_tequiv ())

let titems_nil_equiv (_: unit)
: Lemma (pequiv #unit #unit (prel_emp unit unit) (irel ID_NIL))
= assert (pequiv #unit #unit (prel_emp unit unit) (irel ID_NIL)) by (T.norm [delta_only [`%prel_emp]]; solve_tequiv ())

let titems_single_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t)
: Lemma (pequiv #t #(asn1_decorated_t_core dk) (drel dd) (irel (ID_SINGLE dd)))
= assert (pequiv #t #(asn1_decorated_t_core dk) (drel dd) (irel (ID_SINGLE dd))) by (solve_tequiv ())

let titems_cons_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#t2: Type0)
  (dtl: idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) t2)
: Lemma (pequiv #(t1 & t2) #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (prel_pair (drel dd) (irel dtl)) (irel (ID_CONS dd dtl)))
= assert (pequiv #(t1 & t2) #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (prel_pair (drel dd) (irel dtl)) (irel (ID_CONS dd dtl))) by (solve_tequiv ())

let titems_any_nil_equiv (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #sfxi #sfxs sfxr (iarel (IA_NIL #sfxi) sfxr))
= assert (pequiv #sfxi #sfxs sfxr (iarel (IA_NIL #sfxi) sfxr)) by (solve_tequiv ())

let titems_any_single_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #(t & sfxi) #(asn1_decorated_t_core dk & sfxs) (prel_pair (drel dd) sfxr) (iarel (IA_SINGLE dd #sfxi) sfxr))
= assert (pequiv #(t & sfxi) #(asn1_decorated_t_core dk & sfxs) (prel_pair (drel dd) sfxr) (iarel (IA_SINGLE dd #sfxi) sfxr)) by (solve_tequiv ())

let titems_any_cons_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#sfxi: Type0) (#t2: Type0)
  (dtl: iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi t2) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (pequiv #(t1 & t2) #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs) (prel_pair (drel dd) (iarel dtl sfxr)) (iarel (IA_CONS dd dtl) sfxr))
= assert (pequiv #(t1 & t2) #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs) (prel_pair (drel dd) (iarel dtl sfxr)) (iarel (IA_CONS dd dtl) sfxr)) by (solve_tequiv ())

(* CHOICE alternatives *)

let tlc_nil_eq (pm: perm) (x: unit) (y: make_gen_choice_type (asn1_lc_t []))
: Lemma (lcrel LC_NIL pm x y == pure False)
= assert_norm (lcrel LC_NIL pm x y == pure False)

let tlc_single_eq (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t) (pm: perm) (x: t)
  (v: make_gen_choice_type (asn1_lc_t [(id', c)]))
: Lemma (lcrel (LC_SINGLE id' cd) pm x v == (if dfst v = id' then crel cd pm x (RS.lc_head_val id' c [] v ()) else pure False))
= assert_norm (lcrel (LC_SINGLE id' cd) pm x v == (let (| id, v |) = v in if id = id' then crel cd pm x v else pure False))

let tlc_cons_inl_aux (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (id: asn1_id_t) (w: idlookup_t id (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (lcrel (LC_CONS id' cd dtl) pm (Inl #t1 #t2 a) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then crel cd pm a (RS.lc_head_val id' c (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ()) else pure False))
= assert (lcrel (LC_CONS id' cd dtl) pm (Inl #t1 #t2 a) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then crel cd pm a (RS.lc_head_val id' c (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ()) else pure False))
  by (T.norm [delta_only [`%lcrel; `%RS.lc_head_val]; zeta; iota]; T.trefl ())

let tlc_cons_inl_eq (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (lcrel (LC_CONS id' cd dtl) pm (Inl #t1 #t2 a) v ==
    (if dfst v = id' then crel cd pm a (RS.lc_head_val id' c (hd2 :: tl2) v ()) else pure False))
= let (| id, w |) = v in
  tlc_cons_inl_aux id' cd dtl pm a id w

let tlc_cons_inr_aux (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (id: asn1_id_t) (w: idlookup_t id (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (lcrel (LC_CONS id' cd dtl) pm (Inr #t1 #t2 b) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then pure False else lcrel dtl pm b (RS.lc_tail_val (id', c) (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ())))
= assert (lcrel (LC_CONS id' cd dtl) pm (Inr #t1 #t2 b) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ==
    (if id = id' then pure False else lcrel dtl pm b (RS.lc_tail_val (id', c) (hd2 :: tl2) ((| id, w |) <: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) ())))
  by (T.norm [delta_only [`%lcrel; `%RS.lc_tail_val]; zeta; iota]; T.trefl ())

let tlc_cons_inr_eq (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (lcrel (LC_CONS id' cd dtl) pm (Inr #t1 #t2 b) v ==
    (if dfst v = id' then pure False else lcrel dtl pm b (RS.lc_tail_val (id', c) (hd2 :: tl2) v ())))
= let (| id, w |) = v in
  tlc_cons_inr_aux id' cd dtl pm b id w

(* ANY DEFINED BY, without a fallback *)

let tadb_nil_eq (#key_k: asn1_terminal_k) (pm: perm) (x: unit) (y: AL.ady key_k [])
: Lemma (sxrel (SX_NIL key_k) pm x y == pure False)
= assert_norm (sxrel (SX_NIL key_k) pm x y == pure False)

let tadb_single_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (pm: perm)
  (r: t) (key: asn1_terminal_t key_k) (w: idlookup_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) [(kx, y)]))
: Lemma (sxrel (SX_SINGLE key_k kx y di) pm r ((| key, w |) <: AL.ady key_k [(kx, y)]) ==
    (if key = key_of_lit key_k kx then irel di pm r (AL.ady_head_val kx y [] ((| key, w |) <: AL.ady key_k [(kx, y)]) ()) else pure False))
= assert (sxrel (SX_SINGLE key_k kx y di) pm r ((| key, w |) <: AL.ady key_k [(kx, y)]) ==
    (if key = key_of_lit key_k kx then irel di pm r (AL.ady_head_val kx y [] ((| key, w |) <: AL.ady key_k [(kx, y)]) ()) else pure False))
  by (T.norm [delta_only [`%sxrel; `%AL.ady_head_val; `%AL.ady]; zeta; iota]; T.trefl ())

let tadb_single_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (pm: perm)
  (r: t) (v: AL.ady key_k [(kx, y)])
: Lemma (sxrel (SX_SINGLE key_k kx y di) pm r v ==
    (if dfst v = key_of_lit key_k kx then irel di pm r (AL.ady_head_val kx y [] v ()) else pure False))
= let (| key, w |) = v in
  tadb_single_aux kx y di pm r key w

let tadb_cons_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (key: asn1_terminal_t key_k) (w: idlookup_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((kx, y) :: hd2 :: tl2)))
: Lemma (sxrel (SX_CONS key_k kx y di dtl) pm (Inl #t1 #t2 a) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = key_of_lit key_k kx then irel di pm a (AL.ady_head_val kx y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ()) else pure False))
= assert (sxrel (SX_CONS key_k kx y di dtl) pm (Inl #t1 #t2 a) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = key_of_lit key_k kx then irel di pm a (AL.ady_head_val kx y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ()) else pure False))
  by (T.norm [delta_only [`%sxrel; `%AL.ady_head_val; `%AL.ady]; zeta; iota]; T.trefl ())

let tadb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (sxrel (SX_CONS key_k kx y di dtl) pm (Inl #t1 #t2 a) v ==
    (if dfst v = key_of_lit key_k kx then irel di pm a (AL.ady_head_val kx y (hd2 :: tl2) v ()) else pure False))
= let (| key, w |) = v in
  tadb_cons_inl_aux kx y di dtl pm a key w

let tadb_cons_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (key: asn1_terminal_t key_k) (w: idlookup_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((kx, y) :: hd2 :: tl2)))
: Lemma (sxrel (SX_CONS key_k kx y di dtl) pm (Inr #t1 #t2 b) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = key_of_lit key_k kx then pure False else sxrel dtl pm b (AL.ady_tail_val kx y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ())))
= assert (sxrel (SX_CONS key_k kx y di dtl) pm (Inr #t1 #t2 b) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ==
    (if key = key_of_lit key_k kx then pure False else sxrel dtl pm b (AL.ady_tail_val kx y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((kx, y) :: hd2 :: tl2)) ())))
  by (T.norm [delta_only [`%sxrel; `%AL.ady_tail_val; `%AL.ady]; zeta; iota]; T.trefl ())

let tadb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (sxrel (SX_CONS key_k kx y di dtl) pm (Inr #t1 #t2 b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else sxrel dtl pm b (AL.ady_tail_val kx y (hd2 :: tl2) v ())))
= let (| key, w |) = v in
  tadb_cons_inr_aux kx y di dtl pm b key w

(* ANY DEFINED BY, with a fallback *)

let tafb_nil_aux (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb) (pm: perm) (z: asn1_terminal_impl_t key_k & tfb)
  (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) []) (asn1_sequence_t_core (dsnd gfb)))
: Lemma (fxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb) pm z ((| key, w |) <: AL.ady_fb key_k [] gfb) ==
    prel_pair (asn1_terminal_rel key_k) (irel dfb) pm z (key, AL.ady_fb_nil_val gfb ((| key, w |) <: AL.ady_fb key_k [] gfb)))
= assert (fxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb) pm z ((| key, w |) <: AL.ady_fb key_k [] gfb) ==
    prel_pair (asn1_terminal_rel key_k) (irel dfb) pm z (key, AL.ady_fb_nil_val gfb ((| key, w |) <: AL.ady_fb key_k [] gfb)))
  by (T.norm [delta_only [`%fxrel; `%tfbr; `%RS.prel_default; `%prel_pair; `%AL.ady_fb_nil_val; `%AL.ady_fb]; zeta; iota]; T.trefl ())

let tafb_nil_eq (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb) (pm: perm) (z: asn1_terminal_impl_t key_k & tfb)
  (v: AL.ady_fb key_k [] gfb)
: Lemma (fxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb) pm z v ==
    prel_pair (asn1_terminal_rel key_k) (irel dfb) pm z (dfst v, AL.ady_fb_nil_val gfb v))
= let (| key, w |) = v in
  tafb_nil_aux key_k dfb pm z key w

let tafb_single_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) [(kx, y)]) (asn1_sequence_t_core (dsnd gfb)))
: Lemma (fxrel (FX_SINGLE key_k kx y di #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inl #t1 #fbt a) ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ==
    (if key = key_of_lit key_k kx then irel di pm a (AL.ady_fb_head_val kx y [] gfb ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ()) else pure False))
= assert (fxrel (FX_SINGLE key_k kx y di #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inl #t1 #fbt a) ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ==
    (if key = key_of_lit key_k kx then irel di pm a (AL.ady_fb_head_val kx y [] gfb ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ()) else pure False))
  by (T.norm [delta_only [`%fxrel; `%AL.ady_fb_head_val; `%AL.ady_fb]; zeta; iota]; T.trefl ())

let tafb_single_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (v: AL.ady_fb key_k [(kx, y)] gfb)
: Lemma (fxrel (FX_SINGLE key_k kx y di #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inl #t1 #fbt a) v ==
    (if dfst v = key_of_lit key_k kx then irel di pm a (AL.ady_fb_head_val kx y [] gfb v ()) else pure False))
= let (| key, w |) = v in
  tafb_single_inl_aux kx y di gfb fbr pm a key w

let tafb_single_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (b: fbt) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) [(kx, y)]) (asn1_sequence_t_core (dsnd gfb)))
: Lemma (fxrel (FX_SINGLE key_k kx y di #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inr #t1 #fbt b) ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ==
    (if key = key_of_lit key_k kx then pure False else fxrel (FX_NIL key_k #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm b (AL.ady_fb_tail_val kx y [] gfb ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ())))
= assert (fxrel (FX_SINGLE key_k kx y di #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inr #t1 #fbt b) ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ==
    (if key = key_of_lit key_k kx then pure False else fxrel (FX_NIL key_k #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm b (AL.ady_fb_tail_val kx y [] gfb ((| key, w |) <: AL.ady_fb key_k [(kx, y)] gfb) ())))
  by (T.norm [delta_only [`%fxrel; `%AL.ady_fb_tail_val; `%AL.ady_fb]; zeta; iota]; T.trefl ())

let tafb_single_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#fbt: Type0) (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (b: fbt) (v: AL.ady_fb key_k [(kx, y)] gfb)
: Lemma (fxrel (FX_SINGLE key_k kx y di #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inr #t1 #fbt b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else fxrel (FX_NIL key_k #fbt) (asn1_sequence_t_core (dsnd gfb)) fbr pm b (AL.ady_fb_tail_val kx y [] gfb v ())))
= let (| key, w |) = v in
  tafb_single_inr_aux kx y di gfb fbr pm b key w

let tafb_cons_inl_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((kx, y) :: hd2 :: tl2)) (asn1_sequence_t_core (dsnd gfb)))
: Lemma (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inl #t1 #t2 a) ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = key_of_lit key_k kx then irel di pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) gfb ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ()) else pure False))
= assert (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inl #t1 #t2 a) ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = key_of_lit key_k kx then irel di pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) gfb ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ()) else pure False))
  by (T.norm [delta_only [`%fxrel; `%AL.ady_fb_head_val; `%AL.ady_fb]; zeta; iota]; T.trefl ())

let tafb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (a: t1) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb)
: Lemma (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inl #t1 #t2 a) v ==
    (if dfst v = key_of_lit key_k kx then irel di pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) gfb v ()) else pure False))
= let (| key, w |) = v in
  tafb_cons_inl_aux kx y di dtl gfb fbr pm a key w

let tafb_cons_inr_aux (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (b: t2) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((kx, y) :: hd2 :: tl2)) (asn1_sequence_t_core (dsnd gfb)))
: Lemma (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inr #t1 #t2 b) ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = key_of_lit key_k kx then pure False else fxrel dtl (asn1_sequence_t_core (dsnd gfb)) fbr pm b (AL.ady_fb_tail_val kx y (hd2 :: tl2) gfb ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ())))
= assert (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inr #t1 #t2 b) ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ==
    (if key = key_of_lit key_k kx then pure False else fxrel dtl (asn1_sequence_t_core (dsnd gfb)) fbr pm b (AL.ady_fb_tail_val kx y (hd2 :: tl2) gfb ((| key, w |) <: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb) ())))
  by (T.norm [delta_only [`%fxrel; `%AL.ady_fb_tail_val; `%AL.ady_fb]; zeta; iota]; T.trefl ())

let tafb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2)
  (gfb: asn1_gen_items_lk) (fbr: perm -> fbt -> asn1_terminal_t key_k -> asn1_sequence_t_core (dsnd gfb) -> slprop) (pm: perm)
  (b: t2) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) gfb)
: Lemma (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) fbr pm (Inr #t1 #t2 b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else fxrel dtl (asn1_sequence_t_core (dsnd gfb)) fbr pm b (AL.ady_fb_tail_val kx y (hd2 :: tl2) gfb v ())))
= let (| key, w |) = v in
  tafb_cons_inr_aux kx y di dtl gfb fbr pm b key w

(* Generic conversion combinators *)

ghost
fn conv_false (b: bool) (#t #u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2)
  (eq1: (pm: perm) -> (x: t) -> (y: u1) -> Lemma (r1 pm x y == pure False))
  (eq2: (pm: perm) -> (x: t) -> (y: u2) -> Lemma (r2 pm x y == pure False))
: conv_t b r1 r2 f
= (pm: perm) (x: t) (y: u1)
{
  eq1 pm x y;
  eq2 pm x (f y);
  rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (pure False);
  unreachable ()
}

ghost
fn conv_via (b: bool) (#t #a1 #a2: Type0) (ra1: prel t a1) (ra2: prel t a2) (g: a1 -> a2) (c: conv_t b ra1 ra2 g)
  (#u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2) (m1: u1 -> GTot a1) (m2: u2 -> GTot a2)
  (eq1: (pm: perm) -> (x: t) -> (y: u1) -> Lemma (r1 pm x y == ra1 pm x (m1 y)))
  (eq2: (pm: perm) -> (x: t) -> (y: u2) -> Lemma (r2 pm x y == ra2 pm x (m2 y)))
  (eqf: (y: u1) -> Lemma (m2 (f y) == g (m1 y)))
: conv_t b r1 r2 f
= (pm: perm) (x: t) (y: u1)
{
  eq1 pm x y;
  eq2 pm x (f y);
  eqf y;
  rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (cv b (ra1 pm x (m1 y)) (ra2 pm x (g (m1 y))));
  c pm x (m1 y);
  rewrite (cv b (ra2 pm x (g (m1 y))) (ra1 pm x (m1 y))) as (cv b (r2 pm x (f y)) (r1 pm x y))
}

ghost
fn conv_cond (b: bool) (#t #a1 #a2: Type0) (ra1: prel t a1) (ra2: prel t a2) (g: a1 -> a2) (c: conv_t b ra1 ra2 g)
  (#u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2)
  (p1: u1 -> GTot bool) (h1: (y: u1) -> squash (p1 y == true) -> GTot a1)
  (p2: u2 -> GTot bool) (h2: (y: u2) -> squash (p2 y == true) -> GTot a2)
  (eq1: (pm: perm) -> (x: t) -> (y: u1) -> Lemma (r1 pm x y == (if p1 y then ra1 pm x (h1 y ()) else pure False)))
  (eq2: (pm: perm) -> (x: t) -> (y: u2) -> Lemma (r2 pm x y == (if p2 y then ra2 pm x (h2 y ()) else pure False)))
  (eqp: (y: u1) -> Lemma (p2 (f y) == p1 y))
  (eqh: (y: u1) -> Lemma (requires (p1 y == true /\ p2 (f y) == true)) (ensures (h2 (f y) () == g (h1 y ()))))
: conv_t b r1 r2 f
= (pm: perm) (x: t) (y: u1)
{
  eq1 pm x y;
  eq2 pm x (f y);
  eqp y;
  let bb : bool = p1 y;
  if bb {
    eqh y;
    rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (cv b (ra1 pm x (h1 y ())) (ra2 pm x (g (h1 y ()))));
    c pm x (h1 y ());
    rewrite (cv b (ra2 pm x (g (h1 y ()))) (ra1 pm x (h1 y ()))) as (cv b (r2 pm x (f y)) (r1 pm x y))
  } else {
    rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (pure False);
    unreachable ()
  }
}

ghost
fn conv_either (b: bool) (#th #tt #ah1 #ah2 #at1 #at2: Type0)
  (rh1: prel th ah1) (rh2: prel th ah2) (gh: ah1 -> ah2) (ch: conv_t b rh1 rh2 gh)
  (rt1: prel tt at1) (rt2: prel tt at2) (gt: at1 -> at2) (ct: conv_t b rt1 rt2 gt)
  (#u1 #u2: Type0) (r1: prel (either th tt) u1) (r2: prel (either th tt) u2) (f: u1 -> u2)
  (p1: u1 -> GTot bool) (h1: (y: u1) -> squash (p1 y == true) -> GTot ah1) (tl1: (y: u1) -> squash (p1 y == false) -> GTot at1)
  (p2: u2 -> GTot bool) (h2: (y: u2) -> squash (p2 y == true) -> GTot ah2) (tl2: (y: u2) -> squash (p2 y == false) -> GTot at2)
  (eql1: (pm: perm) -> (x: th) -> (y: u1) -> Lemma (r1 pm (Inl x) y == (if p1 y then rh1 pm x (h1 y ()) else pure False)))
  (eqr1: (pm: perm) -> (x: tt) -> (y: u1) -> Lemma (r1 pm (Inr x) y == (if p1 y then pure False else rt1 pm x (tl1 y ()))))
  (eql2: (pm: perm) -> (x: th) -> (y: u2) -> Lemma (r2 pm (Inl x) y == (if p2 y then rh2 pm x (h2 y ()) else pure False)))
  (eqr2: (pm: perm) -> (x: tt) -> (y: u2) -> Lemma (r2 pm (Inr x) y == (if p2 y then pure False else rt2 pm x (tl2 y ()))))
  (eqp: (y: u1) -> Lemma (p2 (f y) == p1 y))
  (eqh: (y: u1) -> Lemma (requires (p1 y == true /\ p2 (f y) == true)) (ensures (h2 (f y) () == gh (h1 y ()))))
  (eqt: (y: u1) -> Lemma (requires (p1 y == false /\ p2 (f y) == false)) (ensures (tl2 (f y) () == gt (tl1 y ()))))
: conv_t b r1 r2 f
= (pm: perm) (x: either th tt) (y: u1)
{
  eqp y;
  let bb : bool = p1 y;
  match x {
    Inl xh -> {
      eql1 pm xh y;
      eql2 pm xh (f y);
      if bb {
        eqh y;
        rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (cv b (rh1 pm xh (h1 y ())) (rh2 pm xh (gh (h1 y ()))));
        ch pm xh (h1 y ());
        rewrite (cv b (rh2 pm xh (gh (h1 y ()))) (rh1 pm xh (h1 y ()))) as (cv b (r2 pm x (f y)) (r1 pm x y))
      } else {
        rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (pure False);
        unreachable ()
      }
    }
    Inr xt -> {
      eqr1 pm xt y;
      eqr2 pm xt (f y);
      if bb {
        rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (pure False);
        unreachable ()
      } else {
        eqt y;
        rewrite (cv b (r1 pm x y) (r2 pm x (f y))) as (cv b (rt1 pm xt (tl1 y ())) (rt2 pm xt (gt (tl1 y ()))));
        ct pm xt (tl1 y ());
        rewrite (cv b (rt2 pm xt (gt (tl1 y ()))) (rt1 pm xt (tl1 y ()))) as (cv b (r2 pm x (f y)) (r1 pm x y))
      }
    }
  }
}

ghost
fn conv_view (b: bool) (#t #ty #u1 #u2: Type0) (r1: prel t u1) (r2: prel t u2) (f: u1 -> u2) (c: conv_t b r1 r2 f) (view: ty -> t)
: conv_t b (vview r1 view) (vview r2 view) f
= (pm: perm) (x: ty) (y: u1)
{
  rewrite (cv b (vview r1 view pm x y) (vview r2 view pm x (f y))) as (cv b (r1 pm (view x) y) (r2 pm (view x) (f y)));
  c pm (view x) y;
  rewrite (cv b (r2 pm (view x) (f y)) (r1 pm (view x) y)) as (cv b (vview r2 view pm x (f y)) (vview r1 view pm x y))
}

(* Conversion types, one per kind of descriptor *)

let ca_t (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  conv_t b (arel d) (raw_varel d) (forget k)

let cc_t (b: bool) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t) : Type =
  conv_t b (crel cd) (raw_vcrel cd) (forget_content k)

let cd_t (b: bool) (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t) : Type =
  conv_t b (drel dd) (raw_vdrel dd) (forget_dec dk)

let ci_t (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t) : Type =
  conv_t b (irel di) (raw_virel di) (forget_items items)

let clc_t (b: bool) (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t) : Type =
  conv_t b (lcrel ld) (raw_vlcrel ld) (lc_forget lc)

let csx_t (b: bool) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t) : Type =
  conv_t b #t #(AL.ady key_k ls) #(rady key_k ls) (sxrel dsx) (raw_vsxrel dsx) (forget_adb_sfx key_k ls)

let cfx_t (b: bool) (k0: asn1_content_k) (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t)
  (sq: squash (ls << k0 /\ dsnd gfb << k0)) : Type =
  conv_t b #t #(AL.ady_fb key_k ls gfb) #(rady_fb key_k ls gfb)
    (fxrel dfx (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb))
    (raw_vfxrel dfx (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (afb_forget k0 key_k ls gfb sq)

let cia_t (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs #rsfx: Type0) (sfxr: prel sfxi sfxs) (rsfxr: prel sfxi rsfx) (fs: sfxs -> rsfx) : Type =
  conv_t b (iarel dpre #sfxs sfxr) (raw_viarel dpre #rsfx rsfxr) (items_any_forget items #sfxs #rsfx fs)

(* SEQUENCE OF / SET OF *)

ghost
fn elem_fwd_d (b: bool) (sq: squash (b == true)) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: ca_t b d)
  (x: t) (pm0: perm) (y1: asn1_t k) (y2: asn1_raw_t k { fwd_r k y1 y2 })
requires arel d pm0 x y1
ensures raw_varel d pm0 x y2
{
  rewrite (arel d pm0 x y1) as (cv b (arel d pm0 x y1) (raw_varel d pm0 x (forget k y1)));
  c pm0 x y1;
  rewrite (cv b (raw_varel d pm0 x (forget k y1)) (arel d pm0 x y1)) as (raw_varel d pm0 x y2)
}

ghost
fn elem_bwd_d (b: bool) (sq: squash (b == false)) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: ca_t b d)
  (x: t) (pm0: perm) (y1: asn1_raw_t k) (y2: asn1_t k { bwd_r k y1 y2 })
requires raw_varel d pm0 x y1
ensures arel d pm0 x y2
{
  rewrite (raw_varel d pm0 x y1) as (cv b (arel d pm0 x y2) (raw_varel d pm0 x (forget k y2)));
  c pm0 x y2;
  rewrite (cv b (raw_varel d pm0 x (forget k y2)) (arel d pm0 x y2)) as (arel d pm0 x y2)
}

ghost
fn conv_list_d (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: ca_t b d)
: conv_t b (tml_rel d) (vml_rel d) (forget_list k)
= (pm: perm) (x: ml t) (y: list (asn1_t k))
{
  if b {
    rewrite (cv b (tml_rel d pm x y) (vml_rel d pm x (forget_list k y)))
      as (It.mixed_list_match (arel d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y);
    list_rel_fwd k y;
    parsers_fwd k;
    ItR.mixed_list_match_rel (arel d) (raw_varel d) ml_ops (asn1_as_parser k) (parse_raw k) (fwd_r k) () pm x y (forget_list k y) (elem_fwd_d b () d c);
    rewrite (It.mixed_list_match (raw_varel d) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y))
      as (cv b (vml_rel d pm x (forget_list k y)) (tml_rel d pm x y))
  } else {
    rewrite (cv b (tml_rel d pm x y) (vml_rel d pm x (forget_list k y)))
      as (It.mixed_list_match (raw_varel d) ml_ops #asn1_strong_parser_kind (parse_raw k) pm x (forget_list k y));
    list_rel_bwd k y;
    parsers_bwd k;
    ItR.mixed_list_match_rel (raw_varel d) (arel d) ml_ops (parse_raw k) (asn1_as_parser k) (bwd_r k) () pm x (forget_list k y) y (elem_bwd_d b () d c);
    rewrite (It.mixed_list_match (arel d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x y)
      as (cv b (vml_rel d pm x (forget_list k y)) (tml_rel d pm x y))
  }
}

ghost
fn conv_seq_of_d (b: bool) (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: ca_t b d)
: cc_t b (CD_SEQUENCE_OF ne d)
= (pm: perm) (x: ml t) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
{
  tcontent_seq_of_eq ne d pm x y;
  vcontent_seq_of_equiv ne d;
  forget_seq_of ne k y;
  rewrite (cv b (crel (CD_SEQUENCE_OF ne d) pm x y) (raw_vcrel (CD_SEQUENCE_OF ne d) pm x (forget_content (ASN1_SEQUENCE_OF ne k) y)))
    as (cv b (tml_rel d pm x (RS.seq_of_up ne k y)) (vml_rel d pm x (forget_list k (RS.seq_of_up ne k y))));
  conv_list_d b d c pm x (RS.seq_of_up ne k y);
  rewrite (cv b (vml_rel d pm x (forget_list k (RS.seq_of_up ne k y))) (tml_rel d pm x (RS.seq_of_up ne k y)))
    as (cv b (raw_vcrel (CD_SEQUENCE_OF ne d) pm x (forget_content (ASN1_SEQUENCE_OF ne k) y)) (crel (CD_SEQUENCE_OF ne d) pm x y))
}

ghost
fn conv_set_of_d (b: bool) (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: ca_t b d)
: cc_t b (CD_SET_OF ne d)
= (pm: perm) (x: ml t) (y: asn1_content_t (ASN1_SET_OF ne k))
{
  tcontent_set_of_eq ne d pm x y;
  vcontent_set_of_equiv ne d;
  forget_set_of ne k y;
  rewrite (cv b (crel (CD_SET_OF ne d) pm x y) (raw_vcrel (CD_SET_OF ne d) pm x (forget_content (ASN1_SET_OF ne k) y)))
    as (cv b (tml_rel d pm x (RS.set_of_up ne k y)) (vml_rel d pm x (forget_list k (RS.set_of_up ne k y))));
  conv_list_d b d c pm x (RS.set_of_up ne k y);
  rewrite (cv b (vml_rel d pm x (forget_list k (RS.set_of_up ne k y))) (tml_rel d pm x (RS.set_of_up ne k y)))
    as (cv b (raw_vcrel (CD_SET_OF ne d) pm x (forget_content (ASN1_SET_OF ne k) y)) (crel (CD_SET_OF ne d) pm x y))
}

(* CHOICE alternatives *)

let conv_lc_nil (b: bool) : clc_t b LC_NIL =
  conv_false b (lcrel LC_NIL) (raw_vlcrel LC_NIL) (lc_forget []) tlc_nil_eq vlc_nil_eq

let conv_lc_single (b: bool) (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t) (cc: cc_t b cd)
: clc_t b (LC_SINGLE id' cd)
= conv_cond b (crel cd) (raw_vcrel cd) (forget_content c) cc
    (lcrel (LC_SINGLE id' cd)) (raw_vlcrel (LC_SINGLE id' cd)) (lc_forget [(id', c)])
    (fun v -> dfst v = id') (fun v _ -> RS.lc_head_val id' c [] v ())
    (fun v -> dfst v = id') (fun v _ -> raw_lc_head_val id' c [] v ())
    (tlc_single_eq id' cd) (vlc_single_eq id' cd)
    (fun v -> lc_forget_dfst [(id', c)] v)
    (fun v -> lc_forget_head id' c [] v)

let conv_lc_cons (b: bool) (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (cc: cc_t b cd) (ct: clc_t b dtl)
: clc_t b (LC_CONS id' cd dtl)
= conv_either b (crel cd) (raw_vcrel cd) (forget_content c) cc
    (lcrel dtl) (raw_vlcrel dtl) (lc_forget (hd2 :: tl2)) ct
    (lcrel (LC_CONS id' cd dtl)) (raw_vlcrel (LC_CONS id' cd dtl)) (lc_forget ((id', c) :: hd2 :: tl2))
    (fun v -> dfst v = id') (fun v _ -> RS.lc_head_val id' c (hd2 :: tl2) v ()) (fun v _ -> RS.lc_tail_val (id', c) (hd2 :: tl2) v ())
    (fun v -> dfst v = id') (fun v _ -> raw_lc_head_val id' c (hd2 :: tl2) v ()) (fun v _ -> raw_lc_tail_val (id', c) (hd2 :: tl2) v ())
    (tlc_cons_inl_eq id' cd dtl) (tlc_cons_inr_eq id' cd dtl) (vlc_cons_inl_eq id' cd dtl) (vlc_cons_inr_eq id' cd dtl)
    (fun v -> lc_forget_dfst ((id', c) :: hd2 :: tl2) v)
    (fun v -> lc_forget_head id' c (hd2 :: tl2) v)
    (fun v -> lc_forget_tail (id', c) (hd2 :: tl2) v)

(* ANY DEFINED BY: the key test commutes with forgetting *)

let key_eqp (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (key: asn1_terminal_t key_k)
: Lemma ((forget_terminal key_k key = raw_key_of_lit key_k kx) == (key = key_of_lit key_k kx))
= if key = key_of_lit key_k kx then () else forget_key_ne key_k key kx

let conv_sx_nil (b: bool) (key_k: asn1_terminal_k) : csx_t b (SX_NIL key_k) =
  conv_false b (sxrel (SX_NIL key_k)) (raw_vsxrel (SX_NIL key_k)) (forget_adb_sfx key_k []) (tadb_nil_eq #key_k) (vadb_nil_eq #key_k)

let conv_sx_single (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t)
  (ci: ci_t b di)
: csx_t b (SX_SINGLE key_k kx y di)
= conv_cond b (irel di) (raw_virel di) (forget_items (dsnd y)) ci
    (sxrel (SX_SINGLE key_k kx y di)) (raw_vsxrel (SX_SINGLE key_k kx y di)) (forget_adb_sfx key_k [(kx, y)])
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_head_val kx y [] v ())
    (fun v -> dfst v = raw_key_of_lit key_k kx) (fun v _ -> rady_head_val kx y [] v ())
    (tadb_single_eq kx y di) (vadb_single_eq kx y di)
    (fun v -> adb_forget_dfst key_k [(kx, y)] v; key_eqp kx (dfst v))
    (fun v -> adb_forget_head kx y [] v)

let conv_sx_cons (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (ci: ci_t b di) (ct: csx_t b dtl)
: csx_t b (SX_CONS key_k kx y di dtl)
= conv_either b (irel di) (raw_virel di) (forget_items (dsnd y)) ci
    (sxrel dtl) (raw_vsxrel dtl) (forget_adb_sfx key_k (hd2 :: tl2)) ct
    (sxrel (SX_CONS key_k kx y di dtl)) (raw_vsxrel (SX_CONS key_k kx y di dtl)) (forget_adb_sfx key_k ((kx, y) :: hd2 :: tl2))
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_head_val kx y (hd2 :: tl2) v ()) (fun v _ -> AL.ady_tail_val kx y (hd2 :: tl2) v ())
    (fun v -> dfst v = raw_key_of_lit key_k kx) (fun v _ -> rady_head_val kx y (hd2 :: tl2) v ()) (fun v _ -> rady_tail_val kx y (hd2 :: tl2) v ())
    (tadb_cons_inl_eq kx y di dtl) (tadb_cons_inr_eq kx y di dtl) (vadb_cons_inl_eq kx y di dtl) (vadb_cons_inr_eq kx y di dtl)
    (fun v -> adb_forget_dfst key_k ((kx, y) :: hd2 :: tl2) v; key_eqp kx (dfst v))
    (fun v -> adb_forget_head kx y (hd2 :: tl2) v)
    (fun v -> adb_forget_tail kx y (hd2 :: tl2) v)

(* ANY DEFINED BY, with a fallback *)

let conv_fx_nil (b: bool) (k0: asn1_content_k) (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (sq: squash ([] << k0 /\ dsnd gfb << k0)) (ci: ci_t b dfb)
: cfx_t b k0 dfb (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) sq
= conv_via b (prel_pair (asn1_terminal_rel key_k) (irel dfb)) (prel_pair (asn1_raw_terminal_rel key_k) (raw_virel dfb))
    (pair_map (forget_terminal key_k) (forget_items (dsnd gfb)))
    (conv_pair b (asn1_terminal_rel key_k) (asn1_raw_terminal_rel key_k) (forget_terminal key_k) (irel dfb) (raw_virel dfb) (forget_items (dsnd gfb)) (conv_terminal b key_k) ci)
    (fxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb))
    (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (afb_forget k0 key_k [] gfb sq)
    (fun v -> (dfst v, AL.ady_fb_nil_val gfb v)) (fun v -> (dfst v, rady_fb_nil_val gfb v))
    (tafb_nil_eq key_k dfb) (vafb_nil_eq key_k dfb)
    (fun v -> afb_forget_dfst k0 key_k [] gfb sq v; afb_forget_nil k0 key_k gfb sq v)

let conv_fx_single (b: bool) (k0: asn1_content_k) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (sq: squash ([(kx, y)] << k0 /\ dsnd gfb << k0))
  (ci: ci_t b di) (cf: ci_t b dfb)
: cfx_t b k0 dfb (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) sq
= conv_either b (irel di) (raw_virel di) (forget_items (dsnd y)) ci
    (fxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb))
    (raw_vfxrel (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (afb_forget k0 key_k [] gfb ()) (conv_fx_nil b k0 key_k dfb () cf)
    (fxrel (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb))
    (raw_vfxrel (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (afb_forget k0 key_k [(kx, y)] gfb sq)
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_fb_head_val kx y [] gfb v ()) (fun v _ -> AL.ady_fb_tail_val kx y [] gfb v ())
    (fun v -> dfst v = raw_key_of_lit key_k kx) (fun v _ -> rady_fb_head_val kx y [] gfb v ()) (fun v _ -> rady_fb_tail_val kx y [] gfb v ())
    (tafb_single_inl_eq kx y di gfb (tfbr key_k dfb)) (tafb_single_inr_eq kx y di gfb (tfbr key_k dfb))
    (vafb_single_inl_eq kx y di gfb (raw_vfbr key_k dfb)) (vafb_single_inr_eq kx y di gfb (raw_vfbr key_k dfb))
    (fun v -> afb_forget_dfst k0 key_k [(kx, y)] gfb sq v; key_eqp kx (dfst v))
    (fun v -> afb_forget_head k0 kx y [] gfb sq v)
    (fun v -> afb_forget_tail k0 kx y [] gfb sq v)

let conv_fx_cons (b: bool) (k0: asn1_content_k) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2)
  (sq: squash (((kx, y) :: hd2 :: tl2) << k0 /\ dsnd gfb << k0))
  (ci: ci_t b di) (ct: cfx_t b k0 dfb dtl ())
: cfx_t b k0 dfb (FX_CONS key_k kx y di dtl) sq
= conv_either b (irel di) (raw_virel di) (forget_items (dsnd y)) ci
    (fxrel dtl (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb))
    (raw_vfxrel dtl (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (afb_forget k0 key_k (hd2 :: tl2) gfb ()) ct
    (fxrel (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr key_k dfb))
    (raw_vfxrel (FX_CONS key_k kx y di dtl) (raw_items_t (dsnd gfb)) (raw_vfbr key_k dfb))
    (afb_forget k0 key_k ((kx, y) :: hd2 :: tl2) gfb sq)
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_fb_head_val kx y (hd2 :: tl2) gfb v ()) (fun v _ -> AL.ady_fb_tail_val kx y (hd2 :: tl2) gfb v ())
    (fun v -> dfst v = raw_key_of_lit key_k kx) (fun v _ -> rady_fb_head_val kx y (hd2 :: tl2) gfb v ()) (fun v _ -> rady_fb_tail_val kx y (hd2 :: tl2) gfb v ())
    (tafb_cons_inl_eq kx y di dtl gfb (tfbr key_k dfb)) (tafb_cons_inr_eq kx y di dtl gfb (tfbr key_k dfb))
    (vafb_cons_inl_eq kx y di dtl gfb (raw_vfbr key_k dfb)) (vafb_cons_inr_eq kx y di dtl gfb (raw_vfbr key_k dfb))
    (fun v -> afb_forget_dfst k0 key_k ((kx, y) :: hd2 :: tl2) gfb sq v; key_eqp kx (dfst v))
    (fun v -> afb_forget_head k0 kx y (hd2 :: tl2) gfb sq v)
    (fun v -> afb_forget_tail k0 kx y (hd2 :: tl2) gfb sq v)

let conv_any (b: bool) : conv_t b #(S.slice U8.t) #asn1_value #asn1_value (prel_slice_ser asn1_value_enc) (prel_slice_ser asn1_value_enc) (fun y -> y) =
  conv_eq b (prel_slice_ser asn1_value_enc) (prel_slice_ser asn1_value_enc) (fun y -> y) (fun _ _ _ -> ())

let conv_emp (b: bool) : conv_t b #unit #unit #unit (prel_emp unit unit) (prel_emp unit unit) (fun y -> y) =
  conv_eq b (prel_emp unit unit) (prel_emp unit unit) (fun y -> y) (fun _ _ _ -> ())

(* The whole conversion, by mutual recursion on the descriptor *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec conv_a (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Tot (ca_t b d) (decreases d)
= match d with
  | D_ILC id #k' cd ->
    trel_ilc_equiv id cd;
    vrel_ilc_equiv id cd;
    forget_ilc id k';
    conv_ext b (crel cd) (arel d) (raw_vcrel cd) (raw_varel d) (forget_content k') (forget k) () (conv_c b cd)
  | D_CHOICE lc pf ld ->
    trel_choice_equiv lc pf ld;
    vrel_choice_equiv lc pf ld;
    forget_choice_ilc lc pf;
    conv_ext b (lcrel ld) (arel d) (raw_vlcrel ld) (raw_varel d) (lc_forget lc) (forget k) () (conv_lc b ld)
  | D_ANY ->
    trel_any_equiv ();
    vrel_any_equiv ();
    forget_any ();
    conv_ext b (prel_slice_ser asn1_value_enc) (arel d) (prel_slice_ser asn1_value_enc) (raw_varel d) (fun y -> y) (forget k) () (conv_any b)
  | D_VIEW #_ #k' d' ty view mk law ->
    trel_view_equiv d' ty view mk law;
    vrel_view_equiv d' ty view mk law;
    conv_ext b (vview (arel d') view) (arel d) (vview (raw_varel d') view) (raw_varel d) (forget k') (forget k) () (conv_view b (arel d') (raw_varel d') (forget k') (conv_a b d') view)

and conv_c (b: bool) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t)
: Tot (cc_t b cd) (decreases cd)
= match cd with
  | CD_TERMINAL k' ->
    tcontent_terminal_equiv k';
    vcontent_terminal_equiv k';
    forget_content_terminal k';
    conv_ext b (asn1_terminal_rel k') (crel cd) (asn1_raw_terminal_rel k') (raw_vcrel cd) (forget_terminal k') (forget_content k) () (conv_terminal b k')
  | CD_RESTRICTED k' r ->
    tcontent_restricted_equiv k' r;
    vcontent_restricted_equiv k' r;
    forget_content_restricted k' r;
    conv_ext b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (crel cd) (asn1_raw_terminal_rel k') (raw_vcrel cd) (restricted_forget k' r) (forget_content k) () (conv_restricted b k' r)
  | CD_PREFIXED #_ #k' d' ->
    tcontent_prefixed_equiv d';
    vcontent_prefixed_equiv d';
    forget_content_prefixed k';
    conv_ext b (arel d') (crel cd) (raw_varel d') (raw_vcrel cd) (forget k') (forget_content k) () (conv_a b d')
  | CD_SEQUENCE gitems di ->
    tcontent_sequence_equiv gitems di;
    vcontent_sequence_equiv gitems di;
    forget_content_sequence gitems;
    conv_ext b (irel di) (crel cd) (raw_virel di) (raw_vcrel cd) (forget_items (dsnd gitems)) (forget_content k) () (conv_i b di)
  | CD_SET ids items pf di ->
    tcontent_set_equiv ids items pf di;
    vcontent_set_equiv ids items pf di;
    forget_content_set ids items pf;
    conv_ext b (irel di) (crel cd) (raw_virel di) (raw_vcrel cd) (forget_items items) (forget_content k) () (conv_i b di)
  | CD_SEQUENCE_OF ne d' -> conv_seq_of_d b ne d' (conv_a b d')
  | CD_SET_OF ne d' -> conv_set_of_d b ne d' (conv_a b d')
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    tcontent_adb_none_equiv ipd prefix kid key_k ls pf pf' dsx dpre;
    vcontent_adb_none_equiv ipd prefix kid key_k ls pf pf' dsx dpre;
    forget_content_adb_none ipd prefix kid key_k ls pf pf';
    conv_ext b (iarel dpre #(AL.ady key_k ls) (sxrel dsx)) (crel cd) (raw_viarel dpre #(rady key_k ls) (raw_vsxrel dsx)) (raw_vcrel cd)
      (items_any_forget prefix #(AL.ady key_k ls) #(rady key_k ls) (forget_adb_sfx key_k ls)) (forget_content k) ()
      (conv_ia b dpre (sxrel dsx) (raw_vsxrel dsx) (forget_adb_sfx key_k ls) (conv_sx b dsx))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    fb_precedes k;
    let k0 = PA.adb_k_some ipd prefix kid key_k ls fb pf pf' in
    let sq : squash (ls << k0 /\ dsnd fb << k0) = () in
    tcontent_adb_some_equiv ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    vcontent_adb_some_equiv ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    forget_content_adb_some ipd prefix kid key_k ls fb pf pf' sq;
    conv_ext b
      (iarel dpre #(AL.ady_fb key_k ls fb) (fxrel dfx (asn1_sequence_t_core (dsnd fb)) (tfbr key_k #fb dfb))) (crel cd)
      (raw_viarel dpre #(rady_fb key_k ls fb) (raw_vfxrel dfx (raw_items_t (dsnd fb)) (raw_vfbr key_k #fb dfb))) (raw_vcrel cd)
      (items_any_forget prefix #(AL.ady_fb key_k ls fb) #(rady_fb key_k ls fb) (afb_forget k0 key_k ls fb sq)) (forget_content k) ()
      (conv_ia b dpre
        (fxrel dfx (asn1_sequence_t_core (dsnd fb)) (tfbr key_k #fb dfb))
        (raw_vfxrel dfx (raw_items_t (dsnd fb)) (raw_vfbr key_k #fb dfb))
        (afb_forget k0 key_k ls fb sq)
        (conv_fx b k0 dfb (conv_i b dfb) dfx sq))
  | CD_VIEW #k' d' ty view mk law ->
    tcontent_view_equiv d' ty view mk law;
    vcontent_view_equiv d' ty view mk law;
    conv_ext b (vview (crel d') view) (crel cd) (vview (raw_vcrel d') view) (raw_vcrel cd) (forget_content k') (forget_content k) () (conv_view b (crel d') (raw_vcrel d') (forget_content k') (conv_c b d') view)

and conv_sx (b: bool) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t)
: Tot (csx_t b dsx) (decreases dsx)
= match dsx with
  | SX_NIL _ -> conv_sx_nil b key_k
  | SX_SINGLE _ kx y di -> conv_sx_single b kx y di (conv_i b di)
  | SX_CONS _ kx y di dtl -> conv_sx_cons b kx y di dtl (conv_i b di) (conv_sx b dtl)

and conv_fx (b: bool) (k0: asn1_content_k) (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb) (cf: ci_t b dfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t)
  (sq: squash (ls << k0 /\ dsnd gfb << k0))
: Tot (cfx_t b k0 dfb dfx sq) (decreases dfx)
= match dfx with
  | FX_NIL _ -> conv_fx_nil b k0 key_k dfb sq cf
  | FX_SINGLE _ kx y di -> conv_fx_single b k0 kx y di dfb sq (conv_i b di) cf
  | FX_CONS _ kx y di dtl -> conv_fx_cons b k0 kx y di dfb dtl sq (conv_i b di) (conv_fx b k0 dfb cf dtl ())

and conv_ia (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs #rsfx: Type0) (sfxr: prel sfxi sfxs) (rsfxr: prel sfxi rsfx) (fs: sfxs -> rsfx) (cs: conv_t b sfxr rsfxr fs)
: Tot (cia_t b dpre sfxr rsfxr fs) (decreases dpre)
= match dpre with
  | IA_NIL ->
    titems_any_nil_equiv sfxr;
    vitems_any_nil_equiv rsfxr;
    forget_items_any_nil fs;
    conv_ext b sfxr (iarel dpre sfxr) rsfxr (raw_viarel dpre rsfxr) fs (items_any_forget items fs) () cs
  | IA_SINGLE #_ #_ #dk dd ->
    titems_any_single_equiv dd sfxr;
    vitems_any_single_equiv dd rsfxr;
    forget_items_any_single dk fs;
    conv_ext b (prel_pair (drel dd) sfxr) (iarel dpre sfxr) (prel_pair (raw_vdrel dd) rsfxr) (raw_viarel dpre rsfxr) (pair_map (forget_dec dk) fs) (items_any_forget items fs) () (conv_pair b (drel dd) (raw_vdrel dd) (forget_dec dk) sfxr rsfxr fs (conv_d b dd) cs)
  | IA_CONS #_ #_ #dk dd #_ #_ #dk2 #_ #tl2 dtl ->
    titems_any_cons_equiv dd dtl sfxr;
    vitems_any_cons_equiv dd dtl rsfxr;
    forget_items_any_cons dk dk2 tl2 fs;
    conv_ext b (prel_pair (drel dd) (iarel dtl sfxr)) (iarel dpre sfxr) (prel_pair (raw_vdrel dd) (raw_viarel dtl rsfxr)) (raw_viarel dpre rsfxr)
      (pair_map (forget_dec dk) (items_any_forget _ fs)) (items_any_forget items fs) ()
      (conv_pair b (drel dd) (raw_vdrel dd) (forget_dec dk) (iarel dtl sfxr) (raw_viarel dtl rsfxr) (items_any_forget _ fs)
        (conv_d b dd) (conv_ia b dtl sfxr rsfxr fs cs))

and conv_lc (b: bool) (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t)
: Tot (clc_t b ld) (decreases ld)
= match ld with
  | LC_NIL -> conv_lc_nil b
  | LC_SINGLE id' cd -> conv_lc_single b id' cd (conv_c b cd)
  | LC_CONS id' cd dtl -> conv_lc_cons b id' cd dtl (conv_c b cd) (conv_lc b dtl)

and conv_d (b: bool) (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t)
: Tot (cd_t b dd) (decreases dd)
= match dd with
  | DD_PLAIN #_ #k' d' ->
    tdec_plain_equiv d';
    vdec_plain_equiv d';
    forget_dec_plain k';
    conv_ext b (arel d') (drel dd) (raw_varel d') (raw_vdrel dd) (forget k') (forget_dec dk) () (conv_a b d')
  | DD_OPTION #_ #k' d' ->
    tdec_option_equiv d';
    vdec_option_equiv d';
    forget_dec_option k';
    conv_ext b (prel_option (arel d')) (drel dd) (prel_option (raw_varel d')) (raw_vdrel dd) (omap (forget k')) (forget_dec dk) () (conv_option b (arel d') (raw_varel d') (forget k') (conv_a b d'))
  | DD_DEFAULT id0 #k' defv ->
    tdec_default_equiv id0 defv;
    vdec_default_equiv id0 defv;
    forget_dec_default id0 defv;
    conv_ext b (RS.prel_default (asn1_terminal_rel k') (key_of_lit k' defv)) (drel dd) (prel_option (asn1_raw_terminal_rel k')) (raw_vdrel dd)
      (dmap #(asn1_terminal_t k') #(key_of_lit k' defv) (forget_terminal k')) (forget_dec dk) ()
      (conv_default b (asn1_terminal_rel k') (key_of_lit k' defv) (asn1_raw_terminal_rel k') (forget_terminal k') (conv_terminal b k'))
  | DD_DEFAULT_RESTRICTED id0 #k' r defv ->
    tdec_default_restricted_equiv id0 r defv;
    vdec_default_restricted_equiv id0 r defv;
    forget_dec_default_restricted id0 r defv;
    conv_ext b (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (key_of_lit k' defv)) (drel dd) (prel_option (asn1_raw_terminal_rel k')) (raw_vdrel dd)
      (dmap #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k' r)) #(key_of_lit k' defv) (restricted_forget k' r)) (forget_dec dk) ()
      (conv_default b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (key_of_lit k' defv) (asn1_raw_terminal_rel k') (restricted_forget k' r) (conv_restricted b k' r))
  | DD_VIEW #_ #_ #dk' d' ty view mk law ->
    tdec_view_equiv d' ty view mk law;
    vdec_view_equiv d' ty view mk law;
    conv_ext b (vview (drel d') view) (drel dd) (vview (raw_vdrel d') view) (raw_vdrel dd) (forget_dec dk') (forget_dec dk) () (conv_view b (drel d') (raw_vdrel d') (forget_dec dk') (conv_d b d') view)

and conv_i (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t)
: Tot (ci_t b di) (decreases di)
= match di with
  | ID_NIL ->
    titems_nil_equiv ();
    vitems_nil_equiv ();
    forget_items_nil ();
    conv_ext b (prel_emp unit unit) (irel di) (prel_emp unit unit) (raw_virel di) (fun y -> y) (forget_items items) () (conv_emp b)
  | ID_SINGLE #_ #_ #dk dd ->
    titems_single_equiv dd;
    vitems_single_equiv dd;
    forget_items_single dk;
    conv_ext b (drel dd) (irel di) (raw_vdrel dd) (raw_virel di) (forget_dec dk) (forget_items items) () (conv_d b dd)
  | ID_CONS #_ #_ #dk dd #_ #_ #dk2 #_ #tl2 dtl ->
    titems_cons_equiv dd dtl;
    vitems_cons_equiv dd dtl;
    forget_items_cons dk dk2 tl2;
    conv_ext b (prel_pair (drel dd) (irel dtl)) (irel di) (prel_pair (raw_vdrel dd) (raw_virel dtl)) (raw_virel di)
      (pair_map (forget_dec dk) (forget_items _)) (forget_items items) ()
      (conv_pair b (drel dd) (raw_vdrel dd) (forget_dec dk) (irel dtl) (raw_virel dtl) (forget_items _) (conv_d b dd) (conv_i b dtl))
#pop-options

(* The main result: from the typed relation of parsers to the value-level
   relation of writers, with a trade back *)

ghost
fn arel_to_raw (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (y: asn1_t k)
requires arel d pm x y
ensures raw_varel d pm x (forget k y) ** Trade.trade (raw_varel d pm x (forget k y)) (arel d pm x y)
{
  rewrite (arel d pm x y) as (cv true (arel d pm x y) (raw_varel d pm x (forget k y)));
  conv_a true d pm x y;
  rewrite (cv true (raw_varel d pm x (forget k y)) (arel d pm x y)) as (raw_varel d pm x (forget k y));
  Trade.intro_trade (raw_varel d pm x (forget k y)) (arel d pm x y) emp fn _ {
    rewrite (raw_varel d pm x (forget k y)) as (cv false (arel d pm x y) (raw_varel d pm x (forget k y)));
    conv_a false d pm x y;
    rewrite (cv false (raw_varel d pm x (forget k y)) (arel d pm x y)) as (arel d pm x y)
  }
}
