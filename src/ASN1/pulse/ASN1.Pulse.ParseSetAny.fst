module ASN1.Pulse.ParseSetAny
#lang-pulse

(* Zero-copy parsing of SET { ... } with components declared in any order.

   The elements of the SET are read in their encoding order: the extent of
   each element is given by its identifier and length header, and the
   element is dispatched, by its identifier, to the parser of its component,
   whose result is stored in the slot of that component. Once all elements
   have been read, the remaining empty slots are filled with the values of
   absent components (None for OPTIONAL, the default value for DEFAULT.)

   The input is assumed to be valid (the validator checks the canonical
   order of the elements, and that each mandatory component appears exactly
   once), so every element belongs to a component whose slot is empty, and
   every empty slot at the end belongs to an OPTIONAL or DEFAULT component. *)

open Pulse.Lib.Pervasives
open LowParse.PulseParse.VReader
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.ILC
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.ParseSequence
open ASN1.Pulse.Interpreter
open ASN1.Pulse.ParseSetAny.Lemmas

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
module SC = ASN1.Pulse.SetComp
module L = ASN1.Pulse.ParseSequence.Lemmas

(* The slots filled so far, indexed by the descriptor of the items *)

let slot_rel (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (pm: perm) (o: option t) (y: asn1_decorated_t_core dk) : slprop =
  match o with
  | None -> emp
  | Some x -> drel dd pm x y

(* strict: keeps Custard's template-index scan from unfolding [dtuple] on a
   symbolic descriptor, which blows up exponentially *)
[@@asn1_pulse_attr; strict_on_arguments [3]]
let rec dtuple (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) : Tot Type0 (decreases di) =
  match di with
  | ID_NIL -> unit
  | ID_SINGLE #_ #_ #_ #t1 _ -> option t1 & unit
  | ID_CONS #_ #_ #_ #t1 _ dtl -> option t1 & dtuple dtl

[@@asn1_pulse_attr]
let rec dnone (#[@@@FStar.Attributes.monomorphize] ids: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l ids) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] di: idesc ls t) : Tot (dtuple di) (decreases di) =
  match di as di returns dtuple di with
  | ID_NIL -> ()
  | ID_SINGLE #_ #_ #_ #t1 _ -> (None #t1, ())
  | ID_CONS #_ #_ #_ #t1 _ dtl -> (None #t1, dnone dtl)

let opres (#t: Type0) (o: option t) : Tot (option unit) =
  match o with
  | None -> None
  | Some _ -> Some ()

(* The presence of a value in each slot *)

let rec pres_of (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) : Tot (dtuple di -> opt_tuple ls) (decreases di) =
  match di as di returns (dtuple di -> opt_tuple ls) with
  | ID_NIL -> (fun _ -> [])
  | ID_SINGLE _ -> (fun st -> [opres (fst st)])
  | ID_CONS _ dtl -> (fun st -> opres (fst st) :: pres_of dtl (snd st))

let rec partial_rel (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) (pm: perm) : Tot (dtuple di -> asn1_sequence_t_core ls -> slprop) (decreases di) =
  match di as di returns (dtuple di -> asn1_sequence_t_core ls -> slprop) with
  | ID_NIL -> (fun _ _ -> emp)
  | ID_SINGLE #_ #_ #dk dd -> (fun st v -> let v' : asn1_decorated_t_core dk = v in slot_rel dd pm (fst st) v')
  | ID_CONS #_ #_ #dk dd #s2 #d2 #dk2 #ids2 #tl2 dtl -> (fun st v ->
    let v' : asn1_decorated_t_core dk & asn1_sequence_t_core (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) = v in
    slot_rel dd pm (fst st) (fst v') ** partial_rel dtl pm (snd st) (snd v'))

(* Slot accessors with erased descriptors, for use in computational code *)

[@@asn1_pulse_attr]
inline_for_extraction
let sone_get (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (st: dtuple (ID_SINGLE (Ghost.reveal dd)))
: Tot (option t)
= fst #(option t) #unit st

[@@asn1_pulse_attr]
inline_for_extraction
let sone_mk (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (o: option t)
: Tot (dtuple (ID_SINGLE (Ghost.reveal dd)))
= (o, ())

[@@asn1_pulse_attr]
inline_for_extraction
let scons_get
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (st: dtuple (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)))
: Tot (option t1)
= fst #(option t1) #(dtuple (Ghost.reveal dtl)) st

[@@asn1_pulse_attr]
inline_for_extraction
let scons_rest
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (st: dtuple (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)))
: Tot (dtuple (Ghost.reveal dtl))
= snd #(option t1) #(dtuple (Ghost.reveal dtl)) st

[@@asn1_pulse_attr]
inline_for_extraction
let scons_mk
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (o: option t1) (r: dtuple (Ghost.reveal dtl))
: Tot (dtuple (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)))
= (o, r)

(* Unfolding *)

let partial_rel_nil_eq (pm: perm) (st: dtuple ID_NIL) (v: asn1_sequence_t_core ASN1_GEN_ITEMS_NIL)
: Lemma (partial_rel ID_NIL pm st v == emp /\ pres_of ID_NIL st == [])
= assert_norm (partial_rel ID_NIL pm st v == emp);
  assert_norm (pres_of ID_NIL st == [])

let partial_rel_single_eq (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (pm: perm) (st: dtuple (ID_SINGLE (Ghost.reveal dd))) (v: asn1_sequence_t_core (single (Ghost.reveal dk)))
: Lemma (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v == slot_rel (Ghost.reveal dd) pm (sone_get dd st) v /\
    pres_of (ID_SINGLE (Ghost.reveal dd)) st == scons (Ghost.reveal dk) ASN1_GEN_ITEMS_NIL (opres (sone_get dd st)) [] /\
    vhd (Ghost.reveal dk) ASN1_GEN_ITEMS_NIL v == v)
= assert_norm (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v == slot_rel (Ghost.reveal dd) pm (sone_get dd st) v);
  assert_norm (pres_of (ID_SINGLE (Ghost.reveal dd)) st == scons (Ghost.reveal dk) ASN1_GEN_ITEMS_NIL (opres (sone_get dd st)) [])

let vhd_cons2 (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (v: asn1_sequence_t_core (cons2 dk dk2 tl2))
: Lemma (vhd dk (tail_of dk dk2 tl2) v == vfst dk dk2 tl2 v /\ vtl dk (tail_of dk dk2 tl2) v == vsnd dk dk2 tl2 v)
= ()

let partial_rel_cons_eq
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (pm: perm) (st: dtuple (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl))) (v: asn1_sequence_t_core (cons2 (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)))
: Lemma (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v ==
      (slot_rel (Ghost.reveal dd) pm (scons_get dd dk2 tl2 dtl st) (vfst (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v) **
       partial_rel (Ghost.reveal dtl) pm (scons_rest dd dk2 tl2 dtl st) (vsnd (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v)) /\
    pres_of (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) st ==
      scons (Ghost.reveal dk) (tail_of (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)) (opres (scons_get dd dk2 tl2 dtl st)) (pres_of (Ghost.reveal dtl) (scons_rest dd dk2 tl2 dtl st)) /\
    vhd (Ghost.reveal dk) (tail_of (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)) v == vfst (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v /\
    vtl (Ghost.reveal dk) (tail_of (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)) v == vsnd (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v)
= assert_norm (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v ==
      (slot_rel (Ghost.reveal dd) pm (scons_get dd dk2 tl2 dtl st) (vfst (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v) **
       partial_rel (Ghost.reveal dtl) pm (scons_rest dd dk2 tl2 dtl st) (vsnd (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v)));
  assert_norm (pres_of (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) st ==
      scons (Ghost.reveal dk) (tail_of (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)) (opres (scons_get dd dk2 tl2 dtl st)) (pres_of (Ghost.reveal dtl) (scons_rest dd dk2 tl2 dtl st)));
  vhd_cons2 (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2) v

let rec partial_rel_none (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) (pm: perm) (v: asn1_sequence_t_core ls)
: Lemma (ensures (partial_rel di pm (dnone di) v == emp /\ pres_of di (dnone di) == none_tuple ls)) (decreases di)
= match di with
  | ID_NIL ->
    assert_norm (partial_rel #[] #ASN1_GEN_ITEMS_NIL #unit ID_NIL pm () v == emp);
    assert_norm (pres_of #[] #ASN1_GEN_ITEMS_NIL #unit ID_NIL () == []);
    assert_norm (none_tuple ASN1_GEN_ITEMS_NIL == [])
  | ID_SINGLE #s #d #dk #t1 dd ->
    partial_rel_single_eq #s #d #dk #t1 dd pm (dnone di) v;
    assert_norm (none_tuple (single dk) == [None])
  | ID_CONS #s #d #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #t2 dtl ->
    partial_rel_cons_eq #s #d #dk #t1 dd #s2 #d2 dk2 #ids2 tl2 #t2 dtl pm (dnone di) v;
    partial_rel_none dtl pm (vsnd dk dk2 tl2 v);
    assert_norm (none_tuple (cons2 dk dk2 tl2) == None :: none_tuple (tail_of dk dk2 tl2));
    slprop_equivs ()

(* Dispatching an element to the slot of its component *)

inline_for_extraction
let disp_t (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) : Type =
  (id: asn1_id_t) ->
  (e: S.slice U8.t) ->
  (#pm: perm) ->
  (#we: Ghost.erased SB.bytes) ->
  (st: dtuple di) ->
  (#v: Ghost.erased (asn1_sequence_t_core ls)) ->
  stt (dtuple di)
    (S.pts_to e #pm we ** partial_rel di pm st v ** pure (dpre ls id we (pres_of di st) v))
    (fun st' -> partial_rel di pm st' v ** Trade.trade (partial_rel di pm st' v) (partial_rel di pm st v ** S.pts_to e #pm we) **
      pure (forall (c: nat) . is_some ls (pres_of di st') c == (is_some ls (pres_of di st) c || SC.comp_of_id (In.twins_of ls) id = Some c)))

inline_for_extraction
fn disp_nil (_: unit)
: disp_t ID_NIL
= (id: _) (e: _) (#pm: _) (#we: _) (st: _) (#v: _)
{
  partial_rel_nil_eq pm st v;
  unreachable ()
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn disp_single
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (pres: dpresent dd)
: disp_t (ID_SINGLE (Ghost.reveal dd))
= (id: _) (e: _) (#pm: _) (#we: _) (st: _) (#v: _)
{
  partial_rel_single_eq dd pm st v;
  rewrite (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v) as emp;
  let x = pres e #pm #we #v;
  let st' = sone_mk dd (Some x);
  partial_rel_single_eq dd pm st' v;
  is_some_fill (Ghost.reveal dk) ASN1_GEN_ITEMS_NIL (pres_of (ID_SINGLE (Ghost.reveal dd)) st) id;
  rewrite (drel dd pm x v) as (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st' v);
  intro (Trade.trade (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st' v) (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v ** S.pts_to e #pm we))
    #(Trade.trade (drel dd pm x v) (S.pts_to e #pm we))
    fn _ {
    rewrite (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st' v) as (drel dd pm x v);
    Trade.elim (drel dd pm x v) (S.pts_to e #pm we);
    rewrite emp as (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v);
  };
  st'
}

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
fn disp_cons
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (has_id: (id: asn1_id_t) -> Tot (b: bool { b == Set.mem id s }))
  (pres: dpresent dd)
  (ptail: disp_t (Ghost.reveal dtl))
: disp_t (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl))
= (id: _) (e: _) (#pm: _) (#we: _) (st: _) (#v: _)
{
  partial_rel_cons_eq dd dk2 tl2 dtl pm st v;
  rewrite (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v)
    as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v));
  if (has_id id) {
    rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v)) as emp;
    let x = pres e #pm #we #(vfst dk dk2 tl2 v);
    let st' = scons_mk dd dk2 tl2 dtl (Some x) (scons_rest dd dk2 tl2 dtl st);
    partial_rel_cons_eq dd dk2 tl2 dtl pm st' v;
    is_some_fill (Ghost.reveal dk) (tail_of dk dk2 tl2) (pres_of (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) st) id;
    rewrite (drel dd pm x (vfst dk dk2 tl2 v)) as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v));
    rewrite (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v)) as (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v));
    rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v))
      as (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st' v);
    intro (Trade.trade (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st' v) (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v ** S.pts_to e #pm we))
      #(Trade.trade (drel dd pm x (vfst dk dk2 tl2 v)) (S.pts_to e #pm we))
      fn _ {
      rewrite (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st' v)
        as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v));
      rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v)) as (drel dd pm x (vfst dk dk2 tl2 v));
      Trade.elim (drel dd pm x (vfst dk dk2 tl2 v)) (S.pts_to e #pm we);
      rewrite (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v)) as (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v));
      rewrite emp as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v));
      rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v))
        as (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v);
    };
    st'
  } else {
    let st2 = ptail id e #pm #we (scons_rest dd dk2 tl2 dtl st) #(vsnd dk dk2 tl2 v);
    let st' = scons_mk dd dk2 tl2 dtl (scons_get dd dk2 tl2 dtl st) st2;
    partial_rel_cons_eq dd dk2 tl2 dtl pm st' v;
    is_some_pass (Ghost.reveal dk) (tail_of dk dk2 tl2) (pres_of (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) st) (pres_of (Ghost.reveal dtl) st2) id;
    rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v)) as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v));
    rewrite (partial_rel dtl pm st2 (vsnd dk dk2 tl2 v)) as (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v));
    rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v))
      as (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st' v);
    intro (Trade.trade (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st' v) (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v ** S.pts_to e #pm we))
      #(Trade.trade (partial_rel dtl pm st2 (vsnd dk dk2 tl2 v)) (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v) ** S.pts_to e #pm we))
      fn _ {
      rewrite (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st' v)
        as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v));
      rewrite (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st') (vsnd dk dk2 tl2 v)) as (partial_rel dtl pm st2 (vsnd dk dk2 tl2 v));
      Trade.elim (partial_rel dtl pm st2 (vsnd dk dk2 tl2 v)) (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v) ** S.pts_to e #pm we);
      rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st') (vfst dk dk2 tl2 v)) as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v));
      rewrite (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v))
        as (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v);
    };
    st'
  }
}

#pop-options

(* Filling the empty slots *)

inline_for_extraction
let fin_t (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (di: idesc ls t) : Type =
  (st: dtuple di) ->
  (#pm: perm) ->
  (#v: Ghost.erased (asn1_sequence_t_core ls)) ->
  stt t
    (partial_rel di pm st v ** pure (fin_pre ls (pres_of di st) v))
    (fun res -> irel di pm res v ** Trade.trade (irel di pm res v) (partial_rel di pm st v))

inline_for_extraction
fn fin_nil (_: unit)
: fin_t ID_NIL
= (st: _) (#pm: _) (#v: _)
{
  let res : unit = ();
  items_rel_nil_eq pm res v;
  partial_rel_nil_eq pm st v;
  trade_emp_intro (irel ID_NIL pm res v) (partial_rel ID_NIL pm st v);
  rewrite emp as (irel ID_NIL pm res v);
  res
}

inline_for_extraction
fn fin_slot
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (abs: dabsent dd)
  (o: option t) (#pm: perm) (#y: Ghost.erased (asn1_decorated_t_core dk))
  requires slot_rel dd pm o y ** pure (None? o ==> absent_core dk y)
  returns x: t
  ensures drel dd pm x y ** Trade.trade (drel dd pm x y) (slot_rel dd pm o y)
{
  match o {
    Some x -> {
      rewrite (slot_rel dd pm o y) as (drel dd pm x y);
      Trade.refl' (drel dd pm x y) (slot_rel dd pm o y);
      x
    }
    None -> {
      rewrite (slot_rel dd pm o y) as emp;
      let x = abs pm y;
      Trade.refl' (drel dd pm x y) (slot_rel dd pm o y);
      x
    }
  }
}

#push-options "--fuel 2 --ifuel 1"

inline_for_extraction
fn fin_single
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (abs: dabsent dd)
: fin_t (ID_SINGLE (Ghost.reveal dd))
= (st: _) (#pm: _) (#v: _)
{
  partial_rel_single_eq dd pm st v;
  rewrite (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v)
    as (slot_rel dd pm (sone_get dd st) v);
  let x = fin_slot dd abs (sone_get dd st) #pm #v;
  items_rel_single_eq dd pm x v;
  rewrite (drel dd pm x v) as (irel (ID_SINGLE (Ghost.reveal dd)) pm x v);
  rewrite (Trade.trade (drel dd pm x v) (slot_rel dd pm (sone_get dd st) v))
    as (Trade.trade (irel (ID_SINGLE (Ghost.reveal dd)) pm x v) (partial_rel (ID_SINGLE (Ghost.reveal dd)) pm st v));
  x
}

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
fn fin_cons
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2)) (#t2: Type0) (dtl: Ghost.erased (idesc (tail_of dk dk2 tl2) t2))
  (abs: dabsent dd)
  (ftail: fin_t (Ghost.reveal dtl))
: fin_t (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl))
= (st: _) (#pm: _) (#v: _)
{
  partial_rel_cons_eq dd dk2 tl2 dtl pm st v;
  rewrite (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v)
    as (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v));
  let x1 = fin_slot dd abs (scons_get dd dk2 tl2 dtl st) #pm #(vfst dk dk2 tl2 v);
  let x2 = ftail (scons_rest dd dk2 tl2 dtl st) #pm #(vsnd dk dk2 tl2 v);
  Trade.prod
    (drel dd pm x1 (vfst dk dk2 tl2 v)) (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v))
    (irel dtl pm x2 (vsnd dk dk2 tl2 v)) (partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v));
  let res : (t1 & t2) = (x1, x2);
  items_rel_cons_eq dd dk2 tl2 dtl pm x1 x2 v;
  rewrite (drel dd pm x1 (vfst dk dk2 tl2 v) ** irel dtl pm x2 (vsnd dk dk2 tl2 v))
    as (irel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm res v);
  rewrite (Trade.trade
      (drel dd pm x1 (vfst dk dk2 tl2 v) ** irel dtl pm x2 (vsnd dk dk2 tl2 v))
      (slot_rel dd pm (scons_get dd dk2 tl2 dtl st) (vfst dk dk2 tl2 v) ** partial_rel dtl pm (scons_rest dd dk2 tl2 dtl st) (vsnd dk dk2 tl2 v)))
    as (Trade.trade (irel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm res v) (partial_rel (id_cons (Ghost.reveal dd) (Ghost.reveal dk2) (Ghost.reveal tl2) (Ghost.reveal dtl)) pm st v));
  res
}

#pop-options

(* The SET content parser *)

let loop_inv (#i: _) (#ls: asn1_gen_items_l i) (#t: Type0) (di: idesc ls t) (pm: perm) (input: S.slice U8.t) (w: SB.bytes) (v: asn1_sequence_t_core ls)
  (r: S.slice U8.t) (wr: SB.bytes) (st: dtuple di) (rem: SZ.t) : slprop
= S.pts_to r #pm wr **
  partial_rel di pm st v **
  Trade.trade (partial_rel di pm st v ** S.pts_to r #pm wr) (S.pts_to input #pm w) **
  pure (SZ.v rem == Seq.length wr /\ full ls w v /\ inv ls w wr (pres_of di st))

#push-options "--z3rlimit 64"

inline_for_extraction
fn set_any_step
  (#ids: Ghost.erased id_decs)
  (items: Ghost.erased (asn1_gen_items_l ids))
  (#t: Type0) (di: Ghost.erased (idesc (Ghost.reveal items) t))
  (disp: disp_t (Ghost.reveal di))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core items))
  (r: S.slice U8.t) (#wr: Ghost.erased SB.bytes) (st: dtuple (Ghost.reveal di)) (rem: SZ.t)
  requires loop_inv di pm input w v r wr st rem ** pure (SZ.v rem > 0)
  returns res: ((S.slice U8.t & dtuple (Ghost.reveal di)) & SZ.t)
  ensures exists* wr' . loop_inv di pm input w v (fst (fst res)) wr' (snd (fst res)) (snd res) ** pure (SZ.v (snd res) < SZ.v rem)
{
  unfold (loop_inv di pm input w v r wr st rem);
  S.pts_to_len r;
  step_pre items w wr (pres_of di st) v;
  let mut poff = 0sz;
  let oid = I.vread_identifier r poff;
  match oid {
    Some id -> {
      let c1 = !poff;
      let ol = ILC.vread_length r poff;
      match ol {
        Some len -> {
          let off2 = !poff;
          tlv_size_eq wr (SZ.v c1) (SZ.v off2 - SZ.v c1) len;
          SZ.fits_lte (SZ.v off2 + U32.v len) (Seq.length wr);
          let n = SZ.add off2 (SZ.uint32_to_sizet len);
          let e, r2 = SU.split_trade r n;
          let st' = disp id e #pm #(Seq.slice wr 0 (SZ.v n)) st #v;
          step_post items w wr (pres_of di st) (pres_of di st') v;
          intro (Trade.trade (partial_rel di pm st' v ** S.pts_to r2 #pm (Seq.slice wr (SZ.v n) (Seq.length wr))) (S.pts_to input #pm w))
            #(Trade.trade (partial_rel di pm st' v) (partial_rel di pm st v ** S.pts_to e #pm (Seq.slice wr 0 (SZ.v n))) **
              Trade.trade (S.pts_to e #pm (Seq.slice wr 0 (SZ.v n)) ** S.pts_to r2 #pm (Seq.slice wr (SZ.v n) (Seq.length wr))) (S.pts_to r #pm wr) **
              Trade.trade (partial_rel di pm st v ** S.pts_to r #pm wr) (S.pts_to input #pm w))
            fn _ {
            Trade.elim (partial_rel di pm st' v) (partial_rel di pm st v ** S.pts_to e #pm (Seq.slice wr 0 (SZ.v n)));
            Trade.elim (S.pts_to e #pm (Seq.slice wr 0 (SZ.v n)) ** S.pts_to r2 #pm (Seq.slice wr (SZ.v n) (Seq.length wr))) (S.pts_to r #pm wr);
            Trade.elim (partial_rel di pm st v ** S.pts_to r #pm wr) (S.pts_to input #pm w);
          };
          let rem' = SZ.sub rem n;
          fold (loop_inv di pm input w v r2 (Seq.slice wr (SZ.v n) (Seq.length wr)) st' rem');
          ((r2, st'), rem')
        }
        None -> {
          unreachable ()
        }
      }
    }
    None -> {
      unreachable ()
    }
  }
}

#pop-options

inline_for_extraction
fn set_any_loop
  (#ids: Ghost.erased id_decs)
  (items: Ghost.erased (asn1_gen_items_l ids))
  (#t: Type0) (di: Ghost.erased (idesc (Ghost.reveal items) t))
  (none: (x: dtuple (Ghost.reveal di) { x == dnone (Ghost.reveal di) }))
  (disp: disp_t (Ghost.reveal di))
  (fin: fin_t (Ghost.reveal di))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core items))
  requires S.pts_to input #pm w ** pure (full items w v /\ inv items w w (none_tuple items))
  returns res: t
  ensures irel di pm res v ** Trade.trade (irel di pm res v) (S.pts_to input #pm w)
{
  S.pts_to_len input;
  partial_rel_none di pm v;
  rewrite emp as (partial_rel di pm none v);
  intro (Trade.trade (partial_rel di pm none v ** S.pts_to input #pm w) (S.pts_to input #pm w)) #emp fn _ {
    rewrite (partial_rel di pm none v) as emp;
  };
  fold (loop_inv di pm input w v input w none (S.len input));
  let mut pr = input;
  let mut pst = none;
  let mut prem = S.len input;
  while (
    let rem = !prem;
    SZ.gt rem 0sz
  ) invariant exists* r wr st rem .
    R.pts_to pr r **
    R.pts_to pst st **
    R.pts_to prem rem **
    loop_inv di pm input w v r wr st rem
    decreases (SZ.v (!prem))
  {
    let r = !pr;
    let st = !pst;
    let rem = !prem;
    let res = set_any_step items di disp input #pm #w #v r st rem;
    pr := fst (fst res);
    pst := snd (fst res);
    prem := snd res;
  };
  let st = !pst;
  let r = !pr;
  let rem = !prem;
  with wr . assert (loop_inv di pm input w v r wr st rem);
  unfold (loop_inv di pm input w v r wr st rem);
  final items w wr (pres_of di st) v;
  let res = fin st #pm #v;
  Trade.elim_hyp_r (partial_rel di pm st v) (S.pts_to r #pm wr) (S.pts_to input #pm w);
  Trade.trans (irel di pm res v) (partial_rel di pm st v) (S.pts_to input #pm w);
  res
}

inline_for_extraction
fn set_any_parser
  (#ids: Ghost.erased id_decs)
  (items: Ghost.erased (asn1_gen_items_l ids))
  (pf: squash (asn1_set_k_wf ids))
  (#t: Type0) (di: Ghost.erased (idesc (Ghost.reveal items) t))
  (none: (x: dtuple (Ghost.reveal di) { x == dnone (Ghost.reveal di) }))
  (disp: disp_t (Ghost.reveal di))
  (fin: fin_t (Ghost.reveal di))
: aparser #t #(asn1_sequence_t_core (Ghost.reveal items)) (irel di) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  init items pf w v;
  set_any_loop items di none disp fin input #pm #w #v
}
