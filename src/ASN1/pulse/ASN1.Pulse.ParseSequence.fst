module ASN1.Pulse.ParseSequence
#lang-pulse

(* Zero-copy parsing of SEQUENCE { ... }: the items are visited in order;
   an OPTIONAL or DEFAULT item is present iff the identifier at the head of
   the remaining input belongs to it, in which case its extent is given by
   its identifier and length header, and its value is parsed in place. *)

open Pulse.Lib.Pervasives
open LowParse.PulseParse.VReader
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.ILC
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse

module S = Pulse.Lib.Slice
module SU = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module In = ASN1.Pulse.Interpreter
module Sq = ASN1.Pulse.Sequence
module L = ASN1.Pulse.ParseSequence.Lemmas

(* Bridging the value types of the twins with those of the schema *)

#push-options "--fuel 1 --ifuel 1"
let twin_d_eq (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (Mkgendcparser?.d (In.twin_of dk) == (| s, d, dk |) /\ Sq.item_set (In.twin_of dk) == s)
= match dk with
  | ASN1_PLAIN_ILC _ -> ()
  | ASN1_OPTION_ILC _ -> ()
  | ASN1_DEFAULT_TERMINAL _ _ -> ()
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ _ _ -> ()

let twin_d (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: squash (asn1_decorated_t_core dk == asn1_decorated_t (Mkgendcparser?.d (In.twin_of dk)))
= twin_d_eq dk

let rec twins_d (#i: _) (ls: asn1_gen_items_l i)
: Lemma (ensures List.Tot.map Mkgendcparser?.d (In.twins_of ls) == l_as_list ls) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> twin_d_eq dk; twins_d tl
#pop-options

let seq_t_eq (#i: _) (ls: asn1_gen_items_l i)
: squash (asn1_sequence_t_core ls == asn1_sequence_t (List.Tot.map Mkgendcparser?.d (In.twins_of ls)))
= twins_d ls; asn1_sequence_t_core_equiv ls

let item_parsed_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (w: SB.bytes) (v: asn1_decorated_t_core dk) : prop =
  L.item_parsed (In.twin_of dk) w (coerce_eq (twin_d dk) v)

let absent_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (v: asn1_decorated_t_core dk) : prop =
  L.absent (In.twin_of dk) (coerce_eq (twin_d dk) v)

let seq_parsed_core (#i: _) (ls: asn1_gen_items_l i) (w: SB.bytes) (v: asn1_sequence_t_core ls) : prop =
  L.seq_parsed (In.twins_of ls) w (coerce_eq (seq_t_eq ls) v)

(* The SEQUENCE content parser *)

let seq_content (gitems: asn1_gen_items_lk) (w: SB.bytes) (v: asn1_content_t (ASN1_SEQUENCE gitems))
: Lemma
  (requires parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE gitems)) w v)
  (ensures seq_parsed_core (dsnd gitems) w v)
= seq_t_eq (dsnd gitems)

(* Sequences of two or more items *)

let cons2 (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Tot (asn1_gen_items_l ((s, d) :: (s2, d2) :: ids2))
= ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)

let vfst (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (v: asn1_sequence_t_core (cons2 dk dk2 tl2))
: Tot (asn1_decorated_t_core dk)
= fst #(asn1_decorated_t_core dk) #(asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) v

let vsnd (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (v: asn1_sequence_t_core (cons2 dk dk2 tl2))
: Tot (asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
= snd #(asn1_decorated_t_core dk) #(asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) v

let cons_post_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (w: SB.bytes) (v: asn1_sequence_t_core (cons2 dk dk2 tl2)) : prop
= let v1 = vfst dk dk2 tl2 v in
  let v2 = vsnd dk dk2 tl2 v in
  let tl = ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2 in
  if Seq.length w = 0
  then absent_core dk v1 /\ seq_parsed_core tl w v2
  else match SB.parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, _) ->
    if Set.mem id s
    then (match L.tlv_size w with
      | None -> False
      | Some n -> n <= Seq.length w /\ item_parsed_core dk (Seq.slice w 0 n) v1 /\ seq_parsed_core tl (Seq.slice w n (Seq.length w)) v2)
    else absent_core dk v1 /\ seq_parsed_core tl w v2

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let seq_cons_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (w: SB.bytes) (v: asn1_sequence_t_core (cons2 dk dk2 tl2))
: Lemma
  (requires seq_parsed_core (cons2 dk dk2 tl2) w v)
  (ensures cons_post_core dk dk2 tl2 w v)
= let tl = ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2 in
  let _ = seq_t_eq (cons2 dk dk2 tl2) in
  let _ = seq_t_eq tl in
  let _ = twin_d dk in
  twin_d_eq dk;
  L.dec_shaped dk;
  let v1 = coerce_eq (twin_d dk) (vfst dk dk2 tl2 v) in
  let v2 = coerce_eq (seq_t_eq tl) (vsnd dk dk2 tl2 v) in
  L.seq_cons (In.twin_of dk) (In.twin_of dk2) (In.twins_of tl2) w v1 v2
#pop-options

(* Single item *)

let single (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot (asn1_gen_items_l [(s, d)]) =
  ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let seq_single_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (w: SB.bytes) (v: asn1_sequence_t_core (single dk))
: Lemma
  (requires seq_parsed_core (single dk) w v)
  (ensures (if Seq.length w = 0 then absent_core dk v else item_parsed_core dk w v))
= let _ = seq_t_eq (single dk) in
  let _ = twin_d dk in
  L.seq_single (In.twin_of dk) w (coerce_eq (twin_d dk) v)
#pop-options

(* No items *)

#push-options "--fuel 2 --ifuel 2"
let seq_nil_core (w: SB.bytes) (v: asn1_sequence_t_core ASN1_GEN_ITEMS_NIL)
: Lemma
  (requires seq_parsed_core ASN1_GEN_ITEMS_NIL w v)
  (ensures Seq.length w == 0)
= ()
#pop-options

(* Unfolding the relation *)

let items_rel_single_eq (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (pm: perm) (x: t) (y: asn1_sequence_t_core (single dk))
: Lemma (irel (ID_SINGLE dd) pm x y == drel dd pm x y)
= assert_norm (irel (ID_SINGLE dd) pm x y == drel dd pm x y)

let items_rel_cons_eq (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2) (#t2: Type0) (dtl: idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) t2)
  (pm: perm) (x1: t1) (x2: t2) (y: asn1_sequence_t_core (cons2 dk dk2 tl2))
: Lemma (irel (ID_CONS dd dtl) pm (x1, x2) y ==
    drel dd pm x1 (vfst dk dk2 tl2 y) ** irel dtl pm x2 (vsnd dk dk2 tl2 y))
= assert_norm (irel (ID_CONS dd dtl) pm (x1, x2) y ==
    drel dd pm x1 (vfst dk dk2 tl2 y) ** irel dtl pm x2 (vsnd dk dk2 tl2 y))

(* Item parsers *)

ghost
fn rel_rewrite (#p: slprop) (q: slprop) (#r: slprop)
  requires p ** Trade.trade p r ** pure (p == q)
  ensures q ** Trade.trade q r
{
  rewrite p as q;
  rewrite (Trade.trade p r) as (Trade.trade q r);
}

inline_for_extraction
let dpresent (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) : Type =
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#w: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (asn1_decorated_t_core dk)) ->
  stt t
    (S.pts_to input #pm w ** pure (item_parsed_core dk w v))
    (fun res -> drel dd pm res v ** Trade.trade (drel dd pm res v) (S.pts_to input #pm w))

let dres (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (input: S.slice U8.t) (pm: perm) (w: Ghost.erased SB.bytes) (v: Ghost.erased (asn1_decorated_t_core dk)) : Type =
  stt t
    (S.pts_to input #pm w ** pure (item_parsed_core dk w v))
    (fun res -> drel dd pm res v ** Trade.trade (drel dd pm res v) (S.pts_to input #pm w))

inline_for_extraction
let dabsent (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) : Type =
  (pm: perm) ->
  (v: Ghost.erased (asn1_decorated_t_core dk)) ->
  stt t
    (pure (absent_core dk v))
    (fun res -> drel dd pm res v ** pure (drel dd pm res v == emp))

(* PLAIN *)

let dec_plain_lemma (#s: _) (k: asn1_k s) (w: SB.bytes) (v: asn1_t k)
: Lemma
  (requires item_parsed_core (ASN1_PLAIN_ILC k) w v)
  (ensures parsed #asn1_strong_parser_kind (asn1_as_parser k) w v)
= L.dec_plain k w v

let dec_rel_plain_eq (#s: _) (#k: asn1_k s) (#t: Type0) (da: adesc k t) (pm: perm) (x: t) (y: asn1_t k)
: Lemma (drel (DD_PLAIN da) pm x y == arel da pm x y)
= assert_norm (drel (DD_PLAIN da) pm x y == arel da pm x y)

inline_for_extraction
fn dec_plain_present
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (da: Ghost.erased (adesc k t))
  (pk: aparser #t #(asn1_t k) (arel da) #asn1_strong_parser_kind (asn1_as_parser k))
: dpresent (DD_PLAIN (Ghost.reveal da))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  dec_plain_lemma k w v;
  let r = pk input #pm #w #v;
  dec_rel_plain_eq da pm r v;
  rel_rewrite (drel (DD_PLAIN (Ghost.reveal da)) pm r v);
  r
}

let absent_plain (#s: _) (k: asn1_k s) (v: asn1_t k)
: Lemma (requires absent_core (ASN1_PLAIN_ILC k) v) (ensures False)
= ()

inline_for_extraction
fn dec_plain_absent
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (da: Ghost.erased (adesc k t))
: dabsent (DD_PLAIN (Ghost.reveal da))
= (pm: _) (v: _)
{
  absent_plain k v;
  unreachable ()
}

(* OPTIONAL *)

#push-options "--z3rlimit 64"

let dec_option_lemma (#s: _) (k: asn1_k s) (w: SB.bytes) (v: option (asn1_t k))
: Lemma
  (requires item_parsed_core (ASN1_OPTION_ILC k) w v)
  (ensures Some? v /\ parsed #asn1_strong_parser_kind (asn1_as_parser k) w (Some?.v v))
= L.dec_option k w v

let dec_rel_option_some (#s: _) (#k: asn1_k s) (#t: Type0) (da: adesc k t) (pm: perm) (a: t) (y: option (asn1_t k))
: Lemma (requires Some? y) (ensures drel (DD_OPTION da) pm (Some a) y == arel da pm a (Some?.v y))
= let Some b = y in
  assert_norm (drel (DD_OPTION da) pm (Some a) (Some b) == arel da pm a b)

let some_v (#t: Type) (v: option t { Some? v }) : Tot t = Some?.v v

inline_for_extraction
fn dec_option_present
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (da: Ghost.erased (adesc k t))
  (pk: aparser #t #(asn1_t k) (arel da) #asn1_strong_parser_kind (asn1_as_parser k))
: dpresent (DD_OPTION (Ghost.reveal da))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  dec_option_lemma k w v;
  let gv : Ghost.erased (option (asn1_t k)) = v;
  assert (pure (Some? (Ghost.reveal gv)));
  let r = pk input #pm #w #(some_v (Ghost.reveal gv));
  let res : option t = Some r;
  dec_rel_option_some da pm r v;
  rel_rewrite (drel (DD_OPTION (Ghost.reveal da)) pm res v);
  res
}

let dec_rel_option_none (#s: _) (#k: asn1_k s) (#t: Type0) (da: adesc k t) (pm: perm) (y: option (asn1_t k))
: Lemma (requires absent_core (ASN1_OPTION_ILC k) y) (ensures drel (DD_OPTION da) pm None y == emp)
= assert_norm (drel (DD_OPTION da) pm None None == emp)

inline_for_extraction
fn dec_option_absent
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (da: Ghost.erased (adesc k t))
: dabsent (DD_OPTION (Ghost.reveal da))
= (pm: _) (v: _)
{
  let res : option t = None;
  dec_rel_option_none da pm v;
  rewrite emp as (drel (DD_OPTION (Ghost.reveal da)) pm res v);
  res
}

(* DEFAULT *)

let dec_default_lemma (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k) (w: SB.bytes) (v: default_tv (key_of_lit k defv))
: Lemma
  (requires item_parsed_core (ASN1_DEFAULT_TERMINAL id0 #k defv) w v)
  (ensures Nondefault? v /\ parsed #asn1_strong_parser_kind (parse_asn1_ILC id0 #(ASN1_TERMINAL k) (asn1_terminal_as_parser k)) w (Nondefault?.v' v))
= L.dec_default id0 defv w v

let nondefault_v (#t: eqtype) (#defv: t) (v: default_tv defv { Nondefault? v }) : Tot t = Nondefault?.v' v

let dec_rel_default_some (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k) (pm: perm) (a: asn1_terminal_impl_t k) (y: default_tv (key_of_lit k defv))
: Lemma (requires Nondefault? y) (ensures drel (DD_DEFAULT id0 #k defv) pm (Some a) y == asn1_terminal_rel k pm a (nondefault_v y))
= let Nondefault b = y in
  assert_norm (drel (DD_DEFAULT id0 #k defv) pm (Some a) (Nondefault b) == asn1_terminal_rel k pm a b)

inline_for_extraction
fn dec_default_present
  (id0: Ghost.erased asn1_id_t) (#k: Ghost.erased asn1_terminal_k) (defv: Ghost.erased (asn1_key_lit k))
  (pt: aparser #(asn1_terminal_impl_t k) #(asn1_terminal_t k) (asn1_terminal_rel k) #asn1_weak_parser_kind (asn1_terminal_as_parser k))
: dpresent (DD_DEFAULT (Ghost.reveal id0) #(Ghost.reveal k) defv)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  dec_default_lemma id0 #k defv w v;
  let gv : Ghost.erased (default_tv #(asn1_terminal_t k) (key_of_lit k defv)) = v;
  let r = parse_ilc id0 #(ASN1_TERMINAL k) #_ #_ #(asn1_terminal_as_parser k) pt input #pm #w #(nondefault_v (Ghost.reveal gv));
  let res : option (asn1_terminal_impl_t k) = Some r;
  dec_rel_default_some id0 #k defv pm r v;
  rel_rewrite (drel (DD_DEFAULT (Ghost.reveal id0) #(Ghost.reveal k) defv) pm res v);
  res
}

let dec_rel_default_none (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k) (pm: perm) (y: default_tv (key_of_lit k defv))
: Lemma (requires absent_core (ASN1_DEFAULT_TERMINAL id0 #k defv) y) (ensures drel (DD_DEFAULT id0 #k defv) pm None y == emp)
= assert_norm (drel (DD_DEFAULT id0 #k defv) pm None (Default #_ #(key_of_lit k defv)) == emp)

inline_for_extraction
fn dec_default_absent
  (id0: Ghost.erased asn1_id_t) (#k: Ghost.erased asn1_terminal_k) (defv: Ghost.erased (asn1_key_lit k))
: dabsent (DD_DEFAULT (Ghost.reveal id0) #(Ghost.reveal k) defv)
= (pm: _) (v: _)
{
  let res : option (asn1_terminal_impl_t k) = None;
  dec_rel_default_none id0 #k defv pm v;
  rewrite emp as (drel (DD_DEFAULT (Ghost.reveal id0) #(Ghost.reveal k) defv) pm res v);
  res
}

(* DEFAULT, restricted *)

let dec_default_restricted_lemma (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) }) (w: SB.bytes) (v: default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv))
: Lemma
  (requires item_parsed_core (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv) w v)
  (ensures Nondefault? v /\ parsed #asn1_strong_parser_kind (parse_asn1_ILC id0 #(ASN1_RESTRICTED_TERMINAL k r) (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))) w (Nondefault?.v' v))
= L.dec_default_restricted id0 r defv w v

let nondefault_r (#k: asn1_terminal_k) (r: asn1_restriction k) (#defv: parse_filter_refine (restriction_pred r)) (v: default_tv defv { Nondefault? v })
: Tot (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
= Nondefault?.v' v

let dec_rel_default_restricted_some (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) }) (pm: perm) (a: asn1_terminal_impl_t k) (y: default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv))
: Lemma (requires Nondefault? y) (ensures drel (DD_DEFAULT_RESTRICTED id0 #k r defv) pm (Some a) y == asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm a (nondefault_r r y))
= let Nondefault b = y in
  assert_norm (drel (DD_DEFAULT_RESTRICTED id0 #k r defv) pm (Some a) (Nondefault b) == asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm a b)

inline_for_extraction
fn dec_default_restricted_present
  (id0: Ghost.erased asn1_id_t) (#k: Ghost.erased asn1_terminal_k) (r: Ghost.erased (asn1_restriction k)) (defv: Ghost.erased (d: asn1_key_lit k { restriction_pred r (key_of_lit k d) }))
  (pc: aparser #(asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)))
: dpresent (DD_DEFAULT_RESTRICTED (Ghost.reveal id0) #(Ghost.reveal k) r defv)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  dec_default_restricted_lemma id0 #k r defv w v;
  let gv : Ghost.erased (default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv)) = v;
  let x = parse_ilc id0 #(ASN1_RESTRICTED_TERMINAL k r) #_ #_ #(asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) pc input #pm #w #(nondefault_r r (Ghost.reveal gv));
  let res : option (asn1_terminal_impl_t k) = Some x;
  dec_rel_default_restricted_some id0 #k r defv pm x v;
  rel_rewrite (drel (DD_DEFAULT_RESTRICTED (Ghost.reveal id0) #(Ghost.reveal k) r defv) pm res v);
  res
}

let dec_rel_default_restricted_none (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) }) (pm: perm) (y: default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv))
: Lemma (requires absent_core (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv) y) (ensures drel (DD_DEFAULT_RESTRICTED id0 #k r defv) pm None y == emp)
= assert_norm (drel (DD_DEFAULT_RESTRICTED id0 #k r defv) pm None (Default #(parse_filter_refine (restriction_pred r)) #(key_of_lit k defv)) == emp)

inline_for_extraction
fn dec_default_restricted_absent
  (id0: Ghost.erased asn1_id_t) (#k: Ghost.erased asn1_terminal_k) (r: Ghost.erased (asn1_restriction k)) (defv: Ghost.erased (d: asn1_key_lit k { restriction_pred r (key_of_lit k d) }))
: dabsent (DD_DEFAULT_RESTRICTED (Ghost.reveal id0) #(Ghost.reveal k) r defv)
= (pm: _) (v: _)
{
  let res : option (asn1_terminal_impl_t k) = None;
  dec_rel_default_restricted_none id0 #k r defv pm v;
  rewrite emp as (drel (DD_DEFAULT_RESTRICTED (Ghost.reveal id0) #(Ghost.reveal k) r defv) pm res v);
  res
}

#pop-options

(* VIEW *)

let dec_rel_view_eq (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
  (pm: perm) (x: ty) (y: asn1_decorated_t_core dk)
: Lemma (drel (DD_VIEW dd ty view mk law) pm x y == drel dd pm (view x) y)
= assert_norm (drel (DD_VIEW dd ty view mk law) pm x y == drel dd pm (view x) y)

inline_for_extraction
fn dec_view_present
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (ty: Type0) (view: Ghost.erased (ty -> t)) (mk: t -> ty) (law: squash (view_law (Ghost.reveal view) mk))
  (p: dpresent dd)
: dpresent (DD_VIEW (Ghost.reveal dd) ty (Ghost.reveal view) mk law)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let x = p input #pm #w #v;
  let res = mk x;
  dec_rel_view_eq dd ty view mk law pm res v;
  rewrite (drel dd pm x v) as (drel (DD_VIEW (Ghost.reveal dd) ty (Ghost.reveal view) mk law) pm res v);
  rewrite (Trade.trade (drel dd pm x v) (S.pts_to input #pm w))
    as (Trade.trade (drel (DD_VIEW (Ghost.reveal dd) ty (Ghost.reveal view) mk law) pm res v) (S.pts_to input #pm w));
  res
}

inline_for_extraction
fn dec_view_absent
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (ty: Type0) (view: Ghost.erased (ty -> t)) (mk: t -> ty) (law: squash (view_law (Ghost.reveal view) mk))
  (a: dabsent dd)
: dabsent (DD_VIEW (Ghost.reveal dd) ty (Ghost.reveal view) mk law)
= (pm: _) (v: _)
{
  let x = a pm v;
  let res = mk x;
  dec_rel_view_eq dd ty view mk law pm res v;
  rewrite (drel dd pm x v) as (drel (DD_VIEW (Ghost.reveal dd) ty (Ghost.reveal view) mk law) pm res v);
  res
}

(* Sequence parsers *)

inline_for_extraction
let sparser (#i: _) (#ls: asn1_gen_items_l i) (#t: Type0) (di: idesc ls t) : Type =
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#w: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (asn1_sequence_t_core ls)) ->
  stt t
    (S.pts_to input #pm w ** pure (seq_parsed_core ls w v))
    (fun res -> irel di pm res v ** Trade.trade (irel di pm res v) (S.pts_to input #pm w))

let sres (#i: _) (#ls: asn1_gen_items_l i) (#t: Type0) (di: idesc ls t) (input: S.slice U8.t) (pm: perm) (w: Ghost.erased SB.bytes) (v: Ghost.erased (asn1_sequence_t_core ls)) : Type =
  stt t
    (S.pts_to input #pm w ** pure (seq_parsed_core ls w v))
    (fun res -> irel di pm res v ** Trade.trade (irel di pm res v) (S.pts_to input #pm w))

ghost
fn trade_emp_intro (p r: slprop)
  requires r ** pure (p == emp)
  ensures Trade.trade p r
{
  intro (Trade.trade p r) #r fn _ {
    rewrite p as emp;
  };
}

ghost
fn trade_emp_l (p q r: slprop)
  requires Trade.trade q r ** pure (p == emp)
  ensures Trade.trade (p ** q) r
{
  intro (Trade.trade (p ** q) r) #(Trade.trade q r) fn _ {
    rewrite p as emp;
    Trade.elim q r;
  };
}

let items_rel_nil_eq (pm: perm) (x: unit) (y: asn1_sequence_t_core ASN1_GEN_ITEMS_NIL)
: Lemma (irel ID_NIL pm x y == emp)
= assert_norm (irel ID_NIL pm x y == emp)

inline_for_extraction
fn seq_nil (_: unit)
: sparser ID_NIL
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seq_nil_core w v;
  let res : unit = ();
  items_rel_nil_eq pm res v;
  trade_emp_intro (irel ID_NIL pm res v) (S.pts_to input #pm w);
  rewrite emp as (irel ID_NIL pm res v);
  res
}

inline_for_extraction
fn seq_single
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (pres: dpresent dd) (abs: dabsent dd)
: sparser (ID_SINGLE (Ghost.reveal dd))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seq_single_core dk w v;
  S.pts_to_len input;
  if (SZ.eq (S.len input) 0sz) {
    let r = abs pm v;
    trade_emp_intro (drel dd pm r v) (S.pts_to input #pm w);
    items_rel_single_eq dd pm r v;
    rel_rewrite (irel (ID_SINGLE (Ghost.reveal dd)) pm r v);
    r
  } else {
    let r = pres input #pm #w #v;
    items_rel_single_eq dd pm r v;
    rel_rewrite (irel (ID_SINGLE (Ghost.reveal dd)) pm r v);
    r
  }
}

let tail_of (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Tot (asn1_gen_items_l ((s2, d2) :: ids2))
= ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2

let id_cons (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2) (#t2: Type0) (dtl: idesc (tail_of dk dk2 tl2) t2)
: Tot (idesc (cons2 dk dk2 tl2) (t1 & t2))
= ID_CONS dd dtl

#push-options "--z3rlimit 64"

inline_for_extraction
fn seq_cons_absent
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (abs: dabsent dd)
  (ptail: sparser dtl)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core (cons2 dk dk2 tl2)))
  requires S.pts_to input #pm w ** pure (absent_core dk (vfst dk dk2 tl2 v) /\ seq_parsed_core (tail_of dk dk2 tl2) w (vsnd dk dk2 tl2 v))
  returns res: (t1 & t2)
  ensures irel (id_cons dd dk2 tl2 dtl) pm res v ** Trade.trade (irel (id_cons dd dk2 tl2 dtl) pm res v) (S.pts_to input #pm w)
{
  let r1 = abs pm (vfst dk dk2 tl2 v);
  let r2 = ptail input #pm #w #(vsnd dk dk2 tl2 v);
  trade_emp_l (drel dd pm r1 (vfst dk dk2 tl2 v)) (irel dtl pm r2 (vsnd dk dk2 tl2 v)) (S.pts_to input #pm w);
  let res : (t1 & t2) = (r1, r2);
  items_rel_cons_eq dd dk2 tl2 dtl pm r1 r2 v;
  rewrite (drel dd pm r1 (vfst dk dk2 tl2 v) ** irel dtl pm r2 (vsnd dk dk2 tl2 v))
    as (irel (id_cons dd dk2 tl2 dtl) pm res v);
  rewrite (Trade.trade (drel dd pm r1 (vfst dk dk2 tl2 v) ** irel dtl pm r2 (vsnd dk dk2 tl2 v)) (S.pts_to input #pm w))
    as (Trade.trade (irel (id_cons dd dk2 tl2 dtl) pm res v) (S.pts_to input #pm w));
  res
}

inline_for_extraction
fn seq_cons_present
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (pres: dpresent dd)
  (ptail: sparser dtl)
  (n: SZ.t)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core (cons2 dk dk2 tl2)))
  requires S.pts_to input #pm w ** pure (SZ.v n <= Seq.length w /\ item_parsed_core dk (Seq.slice w 0 (SZ.v n)) (vfst dk dk2 tl2 v) /\ seq_parsed_core (tail_of dk dk2 tl2) (Seq.slice w (SZ.v n) (Seq.length w)) (vsnd dk dk2 tl2 v))
  returns res: (t1 & t2)
  ensures irel (id_cons dd dk2 tl2 dtl) pm res v ** Trade.trade (irel (id_cons dd dk2 tl2 dtl) pm res v) (S.pts_to input #pm w)
{
  let in1, in2 = SU.split_trade input n;
  let r1 = pres in1 #pm #(Seq.slice w 0 (SZ.v n)) #(vfst dk dk2 tl2 v);
  let r2 = ptail in2 #pm #(Seq.slice w (SZ.v n) (Seq.length w)) #(vsnd dk dk2 tl2 v);
  Trade.prod
    (drel dd pm r1 (vfst dk dk2 tl2 v)) (S.pts_to in1 #pm (Seq.slice w 0 (SZ.v n)))
    (irel dtl pm r2 (vsnd dk dk2 tl2 v)) (S.pts_to in2 #pm (Seq.slice w (SZ.v n) (Seq.length w)));
  Trade.trans
    (drel dd pm r1 (vfst dk dk2 tl2 v) ** irel dtl pm r2 (vsnd dk dk2 tl2 v))
    (S.pts_to in1 #pm (Seq.slice w 0 (SZ.v n)) ** S.pts_to in2 #pm (Seq.slice w (SZ.v n) (Seq.length w)))
    (S.pts_to input #pm w);
  let res : (t1 & t2) = (r1, r2);
  items_rel_cons_eq dd dk2 tl2 dtl pm r1 r2 v;
  rewrite (drel dd pm r1 (vfst dk dk2 tl2 v) ** irel dtl pm r2 (vsnd dk dk2 tl2 v))
    as (irel (id_cons dd dk2 tl2 dtl) pm res v);
  rewrite (Trade.trade (drel dd pm r1 (vfst dk dk2 tl2 v) ** irel dtl pm r2 (vsnd dk dk2 tl2 v)) (S.pts_to input #pm w))
    as (Trade.trade (irel (id_cons dd dk2 tl2 dtl) pm res v) (S.pts_to input #pm w));
  res
}

let tlv_size_eq (w: SB.bytes) (c1: nat) (c2: nat) (len: U32.t)
: Lemma
  (requires (
    c1 <= Seq.length w /\
    (match SB.parse parse_asn1_identifier_U32 w with Some (_, c1') -> c1' == c1 | None -> False) /\
    (match SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w c1 (Seq.length w)) with Some (len', c2') -> (len' <: U32.t) == len /\ c2' == c2 | None -> False)))
  (ensures L.tlv_size w == Some (c1 + c2 + U32.v len))
= ILC.length_eq (Seq.slice w c1 (Seq.length w))

inline_for_extraction
fn seq_cons
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (has_id: (id: asn1_id_t) -> Tot (b: bool { b == Set.mem id s }))
  (pres: dpresent dd) (abs: dabsent dd)
  (ptail: sparser dtl)
: sparser (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seq_cons_core dk dk2 tl2 w v;
  S.pts_to_len input;
  if (SZ.eq (S.len input) 0sz) {
    seq_cons_absent dd dk2 tl2 dtl abs ptail input #pm #w #v
  } else {
    let mut poff = 0sz;
    let oid = I.vread_identifier input poff;
    match oid {
      Some id -> {
        if (has_id id) {
          let c1 = !poff;
          let ol = ILC.vread_length input poff;
          match ol {
            Some len -> {
              let off2 = !poff;
              tlv_size_eq w (SZ.v c1) (SZ.v off2 - SZ.v c1) len;
              SZ.fits_lte (SZ.v off2 + U32.v len) (Seq.length w);
              let n = SZ.add off2 (SZ.uint32_to_sizet len);
              seq_cons_present dd dk2 tl2 dtl pres ptail n input #pm #w #v
            }
            None -> {
              unreachable ()
            }
          }
        } else {
          seq_cons_absent dd dk2 tl2 dtl abs ptail input #pm #w #v
        }
      }
      None -> {
        unreachable ()
      }
    }
  }
}

#pop-options

(* The SEQUENCE content parser *)

inline_for_extraction
fn seq_parser
  (gitems: Ghost.erased asn1_gen_items_lk) (#t: Type0) (di: Ghost.erased (idesc (dsnd (Ghost.reveal gitems)) t))
  (f: sparser di)
: aparser #t #(asn1_sequence_t_core (dsnd (Ghost.reveal gitems))) (irel di) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE gitems))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seq_content gitems w v;
  f input #pm #w #v
}
