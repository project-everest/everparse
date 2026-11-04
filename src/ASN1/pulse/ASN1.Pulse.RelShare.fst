module ASN1.Pulse.RelShare
#lang-pulse

(* Generic sharing and gathering combinators for the permission of Pulse
   relations (`share_t`, `gather_t`), as needed by the mixed-list
   iterator used by the raw value relation (ASN1.Pulse.RawRel). *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module PB = LowParse.PulseParse.Base
module It = LowParse.PulseParse.Iterator
module PS = ASN1.Pulse.ParseSequence
module PA = ASN1.Pulse.ParseAdb
module AL = ASN1.Pulse.ParseAdb.Lemmas


(* Generic combinators *)

inline_for_extraction
let share_t (#t: Type0) (#u: Type0) (r: prel t u) : Type = PB.share_t #t #u r
inline_for_extraction
let gather_t (#t: Type0) (#u: Type0) (r: prel t u) : Type = PB.gather_t #t #u r

let prel_equiv (#t: Type0) (#u: Type0) (r1 r2: prel t u) : prop =
  forall pm x y . r1 pm x y == r2 pm x y

ghost
fn share_ext (#t: Type0) (#u: Type0) (r1: prel t u) (r2: prel t u) (sq: squash (prel_equiv r1 r2)) (sh: share_t r1)
: share_t #t #u r2
= (x: t) (#p: perm) (#y: u)
{
  rewrite (r2 p x y) as (r1 p x y);
  sh x #p #y;
  rewrite (r1 (p /. 2.0R) x y ** r1 (p /. 2.0R) x y) as (r2 (p /. 2.0R) x y ** r2 (p /. 2.0R) x y)
}

ghost
fn gather_ext (#t: Type0) (#u: Type0) (r1: prel t u) (r2: prel t u) (sq: squash (prel_equiv r1 r2)) (g: gather_t r1)
: gather_t #t #u r2
= (x: t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  rewrite (r2 p x y ** r2 p' x y') as (r1 p x y ** r1 p' x y');
  g x #p #y #p' #y';
  rewrite (r1 (p +. p') x y) as (r2 (p +. p') x y)
}

ghost
fn share_slice_ser (#u: Type0) (enc: u -> GTot SB.bytes)
: share_t #(S.slice U8.t) #u (prel_slice_ser enc)
= (x: S.slice U8.t) (#p: perm) (#y: u)
{
  unfold (prel_slice_ser enc p x y);
  S.share x;
  fold (prel_slice_ser enc (p /. 2.0R) x y);
  fold (prel_slice_ser enc (p /. 2.0R) x y)
}

let enc_injective (#u: Type0) (enc: u -> GTot SB.bytes) : prop =
  forall (y1 y2: u) . enc y1 == enc y2 ==> y1 == y2

ghost
fn gather_slice_ser (#u: Type0) (enc: u -> GTot SB.bytes) (inj: squash (enc_injective enc))
: gather_t #(S.slice U8.t) #u (prel_slice_ser enc)
= (x: S.slice U8.t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  unfold (prel_slice_ser enc p x y);
  unfold (prel_slice_ser enc p' x y');
  S.gather x;
  fold (prel_slice_ser enc (p +. p') x y)
}

let prel_default (#t: Type0) (#u: eqtype) (r: prel t u) (defv: u) (pm: perm) (x: option t) (y: default_tv defv) : slprop =
  match x, y with
  | None, Default -> emp
  | Some a, Nondefault b -> r pm a b
  | _ -> pure False

(* Contents *)

let content_terminal_equiv (k: asn1_terminal_k)
: Lemma (prel_equiv #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) (asn1_content_rel (ASN1_TERMINAL k)))
= assert_norm (prel_equiv #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) (asn1_content_rel (ASN1_TERMINAL k)))

let restricted_t_eq (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r) == parse_filter_refine (restriction_pred r))
= assert_norm (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r) == parse_filter_refine (restriction_pred r))

let restricted_up (k: asn1_terminal_k) (r: asn1_restriction k) (y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) : Tot (asn1_terminal_t k) =
  restricted_t_eq k r;
  let y' : parse_filter_refine (restriction_pred r) = coerce_eq () y in
  y'

let content_restricted_eq (k: asn1_terminal_k) (r: asn1_restriction k) (pm: perm) (x: asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) (y: asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
: Lemma (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x y == asn1_terminal_rel k pm x (restricted_up k r y))
= assert_norm (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x y == asn1_terminal_rel k pm x y)

let content_prefixed_equiv (#s: _) (k: asn1_k s)
: Lemma (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_content_rel (ASN1_PREFIXED k)))
= assert_norm (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_content_rel (ASN1_PREFIXED k)))

let content_sequence_equiv (gitems: asn1_gen_items_lk)
: Lemma (prel_equiv #(asn1_items_impl_t (dsnd gitems)) #(asn1_sequence_t_core (dsnd gitems)) (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)))
= assert_norm (prel_equiv #(asn1_items_impl_t (dsnd gitems)) #(asn1_sequence_t_core (dsnd gitems)) (asn1_items_rel (dsnd gitems)) (asn1_content_rel (ASN1_SEQUENCE gitems)))

let content_set_equiv (ids: _) (items: asn1_gen_items_l ids) (pf: _)
: Lemma (prel_equiv #(asn1_items_impl_t items) #(asn1_sequence_t_core items) (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)))
= assert_norm (prel_equiv #(asn1_items_impl_t items) #(asn1_sequence_t_core items) (asn1_items_rel items) (asn1_content_rel (ASN1_SET ids items pf)))

let seq_of_up (ne: bool) (#s: _) (k: asn1_k s) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k)) : Tot (list (asn1_t k)) =
  assert_norm (asn1_content_t (ASN1_SEQUENCE_OF ne k) == sized_list ne (asn1_t k));
  let y' : sized_list ne (asn1_t k) = coerce_eq () y in
  y'

let set_of_up (ne: bool) (#s: _) (k: asn1_k s) (y: asn1_content_t (ASN1_SET_OF ne k)) : Tot (list (asn1_t k)) =
  assert_norm (asn1_content_t (ASN1_SET_OF ne k) == sized_list ne (asn1_t k));
  let y' : sized_list ne (asn1_t k) = coerce_eq () y in
  y'

let seq_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (y: asn1_content_t (ASN1_SEQUENCE_OF ne k))
: Lemma (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (seq_of_up ne k y))
= asn1_content_rel_seq_of_eq ne k pm x y

let set_of_eq (ne: bool) (#s: _) (k: asn1_k s) (pm: perm) (x: asn1_content_impl_t (ASN1_SET_OF ne k)) (y: asn1_content_t (ASN1_SET_OF ne k))
: Lemma (asn1_content_rel (ASN1_SET_OF ne k) pm x y == It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x (set_of_up ne k y))
= asn1_content_rel_set_of_eq ne k pm x y

(* Tags *)

let rel_ilc_equiv (id: asn1_id_t) (k: asn1_content_k)
: Lemma (prel_equiv #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) (asn1_rel (ASN1_ILC id k)))
= assert_norm (prel_equiv #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) (asn1_rel (ASN1_ILC id k)))

let rel_any_equiv (_: unit)
: Lemma (prel_equiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC))
= assert_norm (prel_equiv #(S.slice U8.t) #asn1_value (prel_slice_ser asn1_value_enc) (asn1_rel ASN1_ANY_ILC))

let rel_choice_equiv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
: Lemma (prel_equiv #(asn1_lc_impl_t lc) #(make_gen_choice_type (asn1_lc_t lc)) (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)))
= assert_norm (prel_equiv #(asn1_lc_impl_t lc) #(make_gen_choice_type (asn1_lc_t lc)) (asn1_lc_rel lc) (asn1_rel (ASN1_CHOICE_ILC lc pf)))

(* Decorated items *)

let dec_plain_equiv (#s: _) (k: asn1_k s)
: Lemma (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)))
= assert_norm (prel_equiv #(asn1_impl_t k) #(asn1_t k) (asn1_rel k) (asn1_decorated_rel (ASN1_PLAIN_ILC k)))

let dec_option_equiv (#s: _) (k: asn1_k s)
: Lemma (prel_equiv #(option (asn1_impl_t k)) #(option (asn1_t k)) (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)))
= assert_norm (prel_equiv #(option (asn1_impl_t k)) #(option (asn1_t k)) (prel_option (asn1_rel k)) (asn1_decorated_rel (ASN1_OPTION_ILC k)))

let dec_default_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)))
= assert_norm (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv (key_of_lit k defv)) (prel_default (asn1_terminal_rel k) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)))

let dec_default_restricted_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) (prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)))
= assert_norm (prel_equiv #(option (asn1_terminal_impl_t k)) #(default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) (prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (key_of_lit k defv)) (asn1_decorated_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)))

(* Items *)

let items_nil_equiv (_: unit)
: Lemma (prel_equiv #unit #unit (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL))
= assert_norm (prel_equiv #unit #unit (prel_emp unit unit) (asn1_items_rel ASN1_GEN_ITEMS_NIL))

let items_single_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (prel_equiv #(asn1_decorated_impl_t dk) #(asn1_decorated_t_core dk) (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)))
= assert_norm (prel_equiv #(asn1_decorated_impl_t dk) #(asn1_decorated_t_core dk) (asn1_decorated_rel dk) (asn1_items_rel (PS.single dk)))

let items_cons_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Lemma (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
    (asn1_items_rel (PS.cons2 dk dk2 tl2)))
= assert_norm (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    #(asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
    (prel_pair (asn1_decorated_rel dk) (asn1_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
    (asn1_items_rel (PS.cons2 dk dk2 tl2)))

(* CHOICE alternatives *)

let lc_head_val (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: tl))) (sq: squash (dfst v == id'))
: Tot (asn1_content_t c)
= dsnd v

let lc_tail_val (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (v: make_gen_choice_type (asn1_lc_t (hd :: tl))) (sq: squash (dfst v <> fst hd))
: Tot (make_gen_choice_type (asn1_lc_t tl))
= (| dfst v, dsnd v |)

let lc_single_eq (id': asn1_id_t) (c: asn1_content_k) (pm: perm) (x: asn1_lc_impl_t [(id', c)])
  (v: make_gen_choice_type (asn1_lc_t [(id', c)]))
: Lemma (asn1_lc_rel [(id', c)] pm x v == (if dfst v = id' then asn1_content_rel c pm x (lc_head_val id' c [] v ()) else pure False))
= assert_norm (asn1_lc_rel [(id', c)] pm x v == (let (| id, v |) = v in if id = id' then asn1_content_rel c pm x v else pure False))

let lc_inl (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k)) (a: asn1_content_impl_t c)
: Tot (asn1_lc_impl_t ((id', c) :: hd2 :: tl2))
= Inl #_ #(asn1_lc_impl_t (hd2 :: tl2)) a

let lc_inr (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k)) (b: asn1_lc_impl_t (hd2 :: tl2))
: Tot (asn1_lc_impl_t ((id', c) :: hd2 :: tl2))
= Inr #(asn1_content_impl_t c) b

let lc_cons_inl_eq (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (a: asn1_content_impl_t c) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inl id' c hd2 tl2 a) v ==
    (if dfst v = id' then asn1_content_rel c pm a (lc_head_val id' c (hd2 :: tl2) v ()) else pure False))
= let (| id, w |) = v in
  assert_norm (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inl id' c hd2 tl2 a) (| id, w |) ==
    (if id = id' then asn1_content_rel c pm a w else pure False))

let lc_cons_inr_eq (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (b: asn1_lc_impl_t (hd2 :: tl2)) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inr id' c hd2 tl2 b) v ==
    (if dfst v = id' then pure False else asn1_lc_rel (hd2 :: tl2) pm b (lc_tail_val (id', c) (hd2 :: tl2) v ())))
= let (| id, w |) = v in
  assert_norm (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm (lc_inr id' c hd2 tl2 b) (| id, w |) ==
    (if id = id' then pure False else asn1_lc_rel (hd2 :: tl2) pm b (| id, w |)));
  if id = id' then () else begin
    let t : make_gen_choice_type (asn1_lc_t (hd2 :: tl2)) = lc_tail_val (id', c) (hd2 :: tl2) v () in
    assert_norm (lc_tail_val (id', c) (hd2 :: tl2) v () == (| dfst v, dsnd v |));
    assert (t == (| id, w |))
  end

(* ANY DEFINED BY *)

let items_any_nil_equiv (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (prel_equiv #sfxi #sfxs sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr))
= assert_norm (prel_equiv #sfxi #sfxs sfxr (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr))

let items_any_single_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (prel_equiv #(asn1_decorated_impl_t dk & sfxi) #(asn1_decorated_t_core dk & sfxs) (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr))
= assert_norm (prel_equiv #(asn1_decorated_impl_t dk & sfxi) #(asn1_decorated_t_core dk & sfxs) (prel_pair (asn1_decorated_rel dk) sfxr) (asn1_items_any_rel (PS.single dk) sfxr))

let items_any_cons_equiv (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (#sfxi: Type0) (#sfxs: Type0) (sfxr: prel sfxi sfxs)
: Lemma (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
    #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
    (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
    (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr))
= assert_norm (prel_equiv
    #(asn1_decorated_impl_t dk & asn1_items_any_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi)
    #(asn1_decorated_t_core dk & asn1_sequence_any_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxs)
    (prel_pair (asn1_decorated_rel dk) (asn1_items_any_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxr))
    (asn1_items_any_rel (PS.cons2 dk dk2 tl2) sfxr))

let adb_none_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (prel_equiv
    #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None))
    #(asn1_sequence_any_t_core prefix (AL.ady key_k ls))
    (asn1_items_any_rel prefix (asn1_adb_rel key_k ls))
    (asn1_content_rel (PA.adb_k_none ipd prefix kid key_k ls pf pf')))
= Classical.forall_intro_3 (PA.adb_rel_none_eq ipd prefix kid key_k ls pf pf')

let adb_some_equiv (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma (prel_equiv
    #(asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb))))
    #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
    (asn1_items_any_rel prefix (PA.afb_rel key_k ls fb))
    (asn1_content_rel (PA.adb_k_some ipd prefix kid key_k ls fb pf pf')))
= Classical.forall_intro_3 (PA.adb_rel_some_eq ipd prefix kid key_k ls fb pf pf')

(* Without a fallback *)

let adb_single_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (r: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k [(kx, y)])
: Lemma (asn1_adb_rel key_k [(kx, y)] pm r v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm r (AL.ady_head_val kx y [] v ()) else pure False))
= assert_norm (asn1_adb_rel key_k [(kx, y)] pm r v == (let (| key, w |) = v in if key = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm r w else pure False))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let adb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a) v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm a (AL.ady_head_val kx y (hd2 :: tl2) v ()) else pure False))
= ()

let adb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (v: AL.ady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (asn1_adb_rel key_k ((kx, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else asn1_adb_rel key_k (hd2 :: tl2) pm b (AL.ady_tail_val kx y (hd2 :: tl2) v ())))
= let (| key, w |) = v in
  PA.adb_rel_cons_inr_aux kx y hd2 tl2 pm b key w
(* With a fallback *)

let fbr_eq (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb) (key: asn1_terminal_t key_k) (v: PA.fbs fb)
: Lemma (PA.fbr key_k fb pm z key v == (asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) v))
= ()

let afb_nil_eq (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm) (z: PA.fbt key_k fb) (v: AL.ady_fb key_k [] fb)
: Lemma (PA.afb_rel key_k [] fb pm z v == PA.fbr key_k fb pm z (dfst v) (AL.ady_fb_nil_val fb v))
= PA.afb_rel_nil_eq fb pm (fst z) (snd z) v

let afb_single_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k [(kx, y)] fb)
: Lemma (PA.afb_rel key_k [(kx, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) a) v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y [] fb v ()) else pure False))
= let (| key, w |) = v in
  PA.afb_rel_single_inl_aux kx y fb pm a key w

let afb_single_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (b: PA.fbt key_k fb) (v: AL.ady_fb key_k [(kx, y)] fb)
: Lemma (PA.afb_rel key_k [(kx, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(PA.fbt key_k fb) b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else PA.fbr key_k fb pm b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val kx y [] fb v ()))))
= let (| key, w |) = v in
  PA.afb_rel_single_inr_aux kx y fb pm b key w

let afb_cons_inl_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) a) v ==
    (if dfst v = key_of_lit key_k kx then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val kx y (hd2 :: tl2) fb v ()) else pure False))
= let (| key, w |) = v in
  PA.afb_rel_cons_inl_aux kx y hd2 tl2 fb pm a key w

let afb_cons_inr_eq (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) (v: AL.ady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (PA.afb_rel key_k ((kx, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) b) v ==
    (if dfst v = key_of_lit key_k kx then pure False else PA.afb_rel key_k (hd2 :: tl2) fb pm b (AL.ady_fb_tail_val kx y (hd2 :: tl2) fb v ())))
= let (| key, w |) = v in
  PA.afb_rel_cons_inr_aux kx y hd2 tl2 fb pm b key w
