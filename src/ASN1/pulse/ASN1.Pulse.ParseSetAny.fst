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

(* The slots filled so far *)

let slot_rel (#s: _) (#d: _) (dk: asn1_decorated_k s d) (pm: perm) (o: option (asn1_decorated_impl_t dk)) (y: asn1_decorated_t_core dk) : slprop =
  match o with
  | None -> emp
  | Some x -> asn1_decorated_rel dk pm x y

let rec partial_rel (#i: _) (ls: asn1_gen_items_l i) (pm: perm) (st: opt_tuple ls) (v: asn1_sequence_t_core ls) : Tot slprop (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> emp
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    slot_rel dk pm (sfst dk tl st) (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st) (vtl dk tl v)

let partial_rel_cons_eq (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i2: _) (tl: asn1_gen_items_l i2)
  (pm: perm) (st: opt_tuple (cons_l dk tl)) (v: asn1_sequence_t_core (cons_l dk tl))
: Lemma (partial_rel (cons_l dk tl) pm st v == (slot_rel dk pm (sfst dk tl st) (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st) (vtl dk tl v)))
= assert_norm (partial_rel (cons_l dk tl) pm st v == (slot_rel dk pm (sfst dk tl st) (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st) (vtl dk tl v)))

let partial_rel_nil_eq (pm: perm) (st: opt_tuple ASN1_GEN_ITEMS_NIL) (v: asn1_sequence_t_core ASN1_GEN_ITEMS_NIL)
: Lemma (partial_rel ASN1_GEN_ITEMS_NIL pm st v == emp)
= assert_norm (partial_rel ASN1_GEN_ITEMS_NIL pm st v == emp)

let rec partial_rel_none (#i: _) (ls: asn1_gen_items_l i) (pm: perm) (v: asn1_sequence_t_core ls)
: Lemma (ensures (partial_rel ls pm (none_tuple ls) v == emp)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> partial_rel_nil_eq pm (none_tuple ls) v
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    partial_rel_cons_eq dk tl pm (none_tuple ls) v;
    partial_rel_none tl pm (vtl dk tl v);
    slprop_equivs ()

(* Slot accessors with erased schema indices, for use in computational code *)

[@@asn1_pulse_attr]
inline_for_extraction
let efst (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#i2: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l i2)) (st: opt_tuple (cons_l (Ghost.reveal dk) (Ghost.reveal tl)))
: Tot (o: option (asn1_decorated_impl_t dk) { o == sfst (Ghost.reveal dk) (Ghost.reveal tl) st })
= fst #(option (asn1_decorated_impl_t dk)) #(opt_tuple (Ghost.reveal tl)) st

[@@asn1_pulse_attr]
inline_for_extraction
let esnd (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#i2: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l i2)) (st: opt_tuple (cons_l (Ghost.reveal dk) (Ghost.reveal tl)))
: Tot (r: opt_tuple (Ghost.reveal tl) { r == ssnd (Ghost.reveal dk) (Ghost.reveal tl) st })
= snd #(option (asn1_decorated_impl_t dk)) #(opt_tuple (Ghost.reveal tl)) st

[@@asn1_pulse_attr]
inline_for_extraction
let econs (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#i2: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l i2)) (o: option (asn1_decorated_impl_t dk)) (r: opt_tuple (Ghost.reveal tl))
: Tot (st: opt_tuple (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) { st == scons (Ghost.reveal dk) (Ghost.reveal tl) o r })
= (o, r)

(* Dispatching an element to the slot of its component *)

let ddres (#i: _) (ls: asn1_gen_items_l i) (id: asn1_id_t) (e: S.slice U8.t) (pm: perm) (we: Ghost.erased SB.bytes) (st: opt_tuple ls) (v: Ghost.erased (asn1_sequence_t_core ls)) : Type =
  stt (opt_tuple ls)
    (S.pts_to e #pm we ** partial_rel ls pm st v ** pure (dpre ls id we st v))
    (fun st' -> partial_rel ls pm st' v ** Trade.trade (partial_rel ls pm st' v) (partial_rel ls pm st v ** S.pts_to e #pm we) **
      pure (forall (c: nat) . is_some ls st' c == (is_some ls st c || SC.comp_of_id (In.twins_of ls) id = Some c)))

inline_for_extraction
let disp_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (id: asn1_id_t) ->
  (e: S.slice U8.t) ->
  (#pm: perm) ->
  (#we: Ghost.erased SB.bytes) ->
  (st: opt_tuple ls) ->
  (#v: Ghost.erased (asn1_sequence_t_core ls)) ->
  stt (opt_tuple ls)
    (S.pts_to e #pm we ** partial_rel ls pm st v ** pure (dpre ls id we st v))
    (fun st' -> partial_rel ls pm st' v ** Trade.trade (partial_rel ls pm st' v) (partial_rel ls pm st v ** S.pts_to e #pm we) **
      pure (forall (c: nat) . is_some ls st' c == (is_some ls st c || SC.comp_of_id (In.twins_of ls) id = Some c)))

inline_for_extraction
fn disp_nil (_: unit)
: disp_t ASN1_GEN_ITEMS_NIL
= (id: _) (e: _) (#pm: _) (#we: _) (st: _) (#v: _)
{
  unreachable ()
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn disp_cons
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#i2: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l i2))
  (has_id: (id: asn1_id_t) -> Tot (b: bool { b == Set.mem id s }))
  (pres: dpresent dk)
  (ptail: disp_t tl)
: disp_t (cons_l (Ghost.reveal dk) (Ghost.reveal tl))
= (id: _) (e: _) (#pm: _) (#we: _) (st: _) (#v: _)
{
  partial_rel_cons_eq dk tl pm st v;
  rewrite (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st v)
    as (slot_rel dk pm (sfst dk tl st) (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st) (vtl dk tl v));
  if (has_id id) {
    rewrite (slot_rel dk pm (sfst dk tl st) (vhd dk tl v)) as emp;
    let x = pres e #pm #we #(vhd dk tl v);
    let st' = econs dk tl (Some x) (esnd dk tl st);
    is_some_fill dk tl st x id;
    rewrite (asn1_decorated_rel dk pm x (vhd dk tl v)) as (slot_rel dk pm (sfst dk tl st') (vhd dk tl v));
    rewrite (partial_rel tl pm (ssnd dk tl st) (vtl dk tl v)) as (partial_rel tl pm (ssnd dk tl st') (vtl dk tl v));
    partial_rel_cons_eq dk tl pm st' v;
    rewrite (slot_rel dk pm (sfst dk tl st') (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st') (vtl dk tl v))
      as (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st' v);
    intro (Trade.trade (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st' v) (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st v ** S.pts_to e #pm we))
      #(Trade.trade (asn1_decorated_rel dk pm x (vhd dk tl v)) (S.pts_to e #pm we))
      fn _ {
      rewrite (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st' v)
        as (slot_rel dk pm (sfst dk tl st') (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st') (vtl dk tl v));
      rewrite (slot_rel dk pm (sfst dk tl st') (vhd dk tl v)) as (asn1_decorated_rel dk pm x (vhd dk tl v));
      Trade.elim (asn1_decorated_rel dk pm x (vhd dk tl v)) (S.pts_to e #pm we);
      rewrite (partial_rel tl pm (ssnd dk tl st') (vtl dk tl v)) as (partial_rel tl pm (ssnd dk tl st) (vtl dk tl v));
      rewrite emp as (slot_rel dk pm (sfst dk tl st) (vhd dk tl v));
      rewrite (slot_rel dk pm (sfst dk tl st) (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st) (vtl dk tl v))
        as (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st v);
    };
    st'
  } else {
    let st2 = ptail id e #pm #we (esnd dk tl st) #(vtl dk tl v);
    let st' = econs dk tl (efst dk tl st) st2;
    is_some_pass dk tl st st2 id;
    rewrite (slot_rel dk pm (sfst dk tl st) (vhd dk tl v)) as (slot_rel dk pm (sfst dk tl st') (vhd dk tl v));
    rewrite (partial_rel tl pm st2 (vtl dk tl v)) as (partial_rel tl pm (ssnd dk tl st') (vtl dk tl v));
    partial_rel_cons_eq dk tl pm st' v;
    rewrite (slot_rel dk pm (sfst dk tl st') (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st') (vtl dk tl v))
      as (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st' v);
    intro (Trade.trade (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st' v) (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st v ** S.pts_to e #pm we))
      #(Trade.trade (partial_rel tl pm st2 (vtl dk tl v)) (partial_rel tl pm (ssnd dk tl st) (vtl dk tl v) ** S.pts_to e #pm we))
      fn _ {
      rewrite (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st' v)
        as (slot_rel dk pm (sfst dk tl st') (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st') (vtl dk tl v));
      rewrite (partial_rel tl pm (ssnd dk tl st') (vtl dk tl v)) as (partial_rel tl pm st2 (vtl dk tl v));
      Trade.elim (partial_rel tl pm st2 (vtl dk tl v)) (partial_rel tl pm (ssnd dk tl st) (vtl dk tl v) ** S.pts_to e #pm we);
      rewrite (slot_rel dk pm (sfst dk tl st') (vhd dk tl v)) as (slot_rel dk pm (sfst dk tl st) (vhd dk tl v));
      rewrite (slot_rel dk pm (sfst dk tl st) (vhd dk tl v) ** partial_rel tl pm (ssnd dk tl st) (vtl dk tl v))
        as (partial_rel (cons_l (Ghost.reveal dk) (Ghost.reveal tl)) pm st v);
    };
    st'
  }
}

#pop-options

(* Filling the empty slots *)

let fres (#i: _) (ls: asn1_gen_items_l i) (st: opt_tuple ls) (pm: perm) (v: Ghost.erased (asn1_sequence_t_core ls)) : Type =
  stt (asn1_items_impl_t ls)
    (partial_rel ls pm st v ** pure (fin_pre ls st v))
    (fun res -> asn1_items_rel ls pm res v ** Trade.trade (asn1_items_rel ls pm res v) (partial_rel ls pm st v))

inline_for_extraction
let fin_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (st: opt_tuple ls) ->
  (#pm: perm) ->
  (#v: Ghost.erased (asn1_sequence_t_core ls)) ->
  stt (asn1_items_impl_t ls)
    (partial_rel ls pm st v ** pure (fin_pre ls st v))
    (fun res -> asn1_items_rel ls pm res v ** Trade.trade (asn1_items_rel ls pm res v) (partial_rel ls pm st v))

inline_for_extraction
fn fin_nil (_: unit)
: fin_t ASN1_GEN_ITEMS_NIL
= (st: _) (#pm: _) (#v: _)
{
  let res : asn1_items_impl_t ASN1_GEN_ITEMS_NIL = ();
  items_rel_nil_eq pm res v;
  trade_emp_intro (asn1_items_rel ASN1_GEN_ITEMS_NIL pm res v) (partial_rel ASN1_GEN_ITEMS_NIL pm st v);
  rewrite emp as (asn1_items_rel ASN1_GEN_ITEMS_NIL pm res v);
  res
}

inline_for_extraction
fn fin_slot
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (abs: dabsent dk)
  (o: option (asn1_decorated_impl_t dk)) (#pm: perm) (#y: Ghost.erased (asn1_decorated_t_core dk))
  requires slot_rel dk pm o y ** pure (None? o ==> absent_core dk y)
  returns x: asn1_decorated_impl_t dk
  ensures asn1_decorated_rel dk pm x y ** Trade.trade (asn1_decorated_rel dk pm x y) (slot_rel dk pm o y)
{
  match o {
    Some x -> {
      rewrite (slot_rel dk pm o y) as (asn1_decorated_rel dk pm x y);
      Trade.refl' (asn1_decorated_rel dk pm x y) (slot_rel dk pm o y);
      x
    }
    None -> {
      rewrite (slot_rel dk pm o y) as emp;
      let x = abs pm y;
      Trade.refl' (asn1_decorated_rel dk pm x y) (slot_rel dk pm o y);
      x
    }
  }
}

let vhd_single (#s: _) (#d: _) (dk: asn1_decorated_k s d) (v: asn1_sequence_t_core (single dk))
: Lemma (vhd dk ASN1_GEN_ITEMS_NIL v == v /\ vtl dk ASN1_GEN_ITEMS_NIL v == ())
= ()

let vhd_cons2 (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (v: asn1_sequence_t_core (cons2 dk dk2 tl2))
: Lemma (vhd dk (tail_of dk dk2 tl2) v == vfst dk dk2 tl2 v /\ vtl dk (tail_of dk dk2 tl2) v == vsnd dk dk2 tl2 v)
= ()

inline_for_extraction
fn fin_single
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (abs: dabsent dk)
: fin_t (single (Ghost.reveal dk))
= (st: _) (#pm: _) (#v: _)
{
  let ls : Ghost.erased (asn1_gen_items_l [(Ghost.reveal s, Ghost.reveal d)]) = cons_l (Ghost.reveal dk) ASN1_GEN_ITEMS_NIL;
  partial_rel_cons_eq dk ASN1_GEN_ITEMS_NIL pm st v;
  partial_rel_nil_eq pm (ssnd dk ASN1_GEN_ITEMS_NIL st) (vtl dk ASN1_GEN_ITEMS_NIL v);
  vhd_single dk v;
  rewrite (partial_rel (single (Ghost.reveal dk)) pm st v)
    as (slot_rel dk pm (sfst dk ASN1_GEN_ITEMS_NIL st) v ** emp);
  let x = fin_slot dk abs (efst dk ASN1_GEN_ITEMS_NIL st) #pm #v;
  items_rel_single_eq dk pm x v;
  rewrite (asn1_decorated_rel dk pm x v) as (asn1_items_rel (single (Ghost.reveal dk)) pm x v);
  intro (Trade.trade (asn1_items_rel (single (Ghost.reveal dk)) pm x v) (partial_rel (single (Ghost.reveal dk)) pm st v))
    #(Trade.trade (asn1_decorated_rel dk pm x v) (slot_rel dk pm (sfst dk ASN1_GEN_ITEMS_NIL st) v))
    fn _ {
    rewrite (asn1_items_rel (single (Ghost.reveal dk)) pm x v) as (asn1_decorated_rel dk pm x v);
    Trade.elim (asn1_decorated_rel dk pm x v) (slot_rel dk pm (sfst dk ASN1_GEN_ITEMS_NIL st) v);
    rewrite (slot_rel dk pm (sfst dk ASN1_GEN_ITEMS_NIL st) v ** emp) as (partial_rel (single (Ghost.reveal dk)) pm st v);
  };
  x
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn fin_cons2
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#s2: Ghost.erased (Set.set asn1_id_t)) (#d2: Ghost.erased asn1_decorator) (dk2: Ghost.erased (asn1_decorated_k s2 d2))
  (#ids2: Ghost.erased id_decs) (tl2: Ghost.erased (asn1_gen_items_l ids2))
  (abs: dabsent dk)
  (ftail: fin_t (tail_of dk dk2 tl2))
: fin_t (cons2 (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2))
= (st: _) (#pm: _) (#v: _)
{
  partial_rel_cons_eq dk (tail_of dk dk2 tl2) pm st v;
  vhd_cons2 dk dk2 tl2 v;
  rewrite (partial_rel (cons2 (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)) pm st v)
    as (slot_rel dk pm (sfst dk (tail_of dk dk2 tl2) st) (vfst dk dk2 tl2 v) ** partial_rel (tail_of dk dk2 tl2) pm (ssnd dk (tail_of dk dk2 tl2) st) (vsnd dk dk2 tl2 v));
  let x1 = fin_slot dk abs (efst dk (tail_of dk dk2 tl2) st) #pm #(vfst dk dk2 tl2 v);
  let x2 = ftail (esnd dk (tail_of dk dk2 tl2) st) #pm #(vsnd dk dk2 tl2 v);
  Trade.prod
    (asn1_decorated_rel dk pm x1 (vfst dk dk2 tl2 v)) (slot_rel dk pm (sfst dk (tail_of dk dk2 tl2) st) (vfst dk dk2 tl2 v))
    (asn1_items_rel (tail_of dk dk2 tl2) pm x2 (vsnd dk dk2 tl2 v)) (partial_rel (tail_of dk dk2 tl2) pm (ssnd dk (tail_of dk dk2 tl2) st) (vsnd dk dk2 tl2 v));
  let res : asn1_items_impl_t (cons2 dk dk2 tl2) = (x1, x2);
  items_rel_cons_eq dk dk2 tl2 pm x1 x2 v;
  rewrite (asn1_decorated_rel dk pm x1 (vfst dk dk2 tl2 v) ** asn1_items_rel (tail_of dk dk2 tl2) pm x2 (vsnd dk dk2 tl2 v))
    as (asn1_items_rel (cons2 dk dk2 tl2) pm res v);
  rewrite (Trade.trade
      (asn1_decorated_rel dk pm x1 (vfst dk dk2 tl2 v) ** asn1_items_rel (tail_of dk dk2 tl2) pm x2 (vsnd dk dk2 tl2 v))
      (slot_rel dk pm (sfst dk (tail_of dk dk2 tl2) st) (vfst dk dk2 tl2 v) ** partial_rel (tail_of dk dk2 tl2) pm (ssnd dk (tail_of dk dk2 tl2) st) (vsnd dk dk2 tl2 v)))
    as (Trade.trade (asn1_items_rel (cons2 dk dk2 tl2) pm res v) (partial_rel (cons2 (Ghost.reveal dk) (Ghost.reveal dk2) (Ghost.reveal tl2)) pm st v));
  res
}

#pop-options

(* The SET content parser *)

let loop_inv (#i: _) (ls: asn1_gen_items_l i) (pm: perm) (input: S.slice U8.t) (w: SB.bytes) (v: asn1_sequence_t_core ls)
  (r: S.slice U8.t) (wr: SB.bytes) (st: opt_tuple ls) (rem: SZ.t) : slprop
= S.pts_to r #pm wr **
  partial_rel ls pm st v **
  Trade.trade (partial_rel ls pm st v ** S.pts_to r #pm wr) (S.pts_to input #pm w) **
  pure (SZ.v rem == Seq.length wr /\ full ls w v /\ inv ls w wr st)

#push-options "--z3rlimit 64"

inline_for_extraction
fn set_any_step
  (#ids: Ghost.erased id_decs)
  (items: Ghost.erased (asn1_gen_items_l ids))
  (disp: disp_t (Ghost.reveal items))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core items))
  (r: S.slice U8.t) (#wr: Ghost.erased SB.bytes) (st: opt_tuple (Ghost.reveal items)) (rem: SZ.t)
  requires loop_inv items pm input w v r wr st rem ** pure (SZ.v rem > 0)
  returns res: ((S.slice U8.t & opt_tuple (Ghost.reveal items)) & SZ.t)
  ensures exists* wr' . loop_inv items pm input w v (fst (fst res)) wr' (snd (fst res)) (snd res) ** pure (SZ.v (snd res) < SZ.v rem)
{
  unfold (loop_inv items pm input w v r wr st rem);
  S.pts_to_len r;
  step_pre items w wr st v;
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
          step_post items w wr st st' v;
          intro (Trade.trade (partial_rel items pm st' v ** S.pts_to r2 #pm (Seq.slice wr (SZ.v n) (Seq.length wr))) (S.pts_to input #pm w))
            #(Trade.trade (partial_rel items pm st' v) (partial_rel items pm st v ** S.pts_to e #pm (Seq.slice wr 0 (SZ.v n))) **
              Trade.trade (S.pts_to e #pm (Seq.slice wr 0 (SZ.v n)) ** S.pts_to r2 #pm (Seq.slice wr (SZ.v n) (Seq.length wr))) (S.pts_to r #pm wr) **
              Trade.trade (partial_rel items pm st v ** S.pts_to r #pm wr) (S.pts_to input #pm w))
            fn _ {
            Trade.elim (partial_rel items pm st' v) (partial_rel items pm st v ** S.pts_to e #pm (Seq.slice wr 0 (SZ.v n)));
            Trade.elim (S.pts_to e #pm (Seq.slice wr 0 (SZ.v n)) ** S.pts_to r2 #pm (Seq.slice wr (SZ.v n) (Seq.length wr))) (S.pts_to r #pm wr);
            Trade.elim (partial_rel items pm st v ** S.pts_to r #pm wr) (S.pts_to input #pm w);
          };
          let rem' = SZ.sub rem n;
          fold (loop_inv items pm input w v r2 (Seq.slice wr (SZ.v n) (Seq.length wr)) st' rem');
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
  (none: (x: opt_tuple (Ghost.reveal items) { x == none_tuple (Ghost.reveal items) }))
  (disp: disp_t (Ghost.reveal items))
  (fin: fin_t (Ghost.reveal items))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core items))
  requires S.pts_to input #pm w ** pure (full items w v /\ inv items w w (none_tuple items))
  returns res: asn1_items_impl_t items
  ensures asn1_items_rel items pm res v ** Trade.trade (asn1_items_rel items pm res v) (S.pts_to input #pm w)
{
  S.pts_to_len input;
  partial_rel_none items pm v;
  rewrite emp as (partial_rel items pm none v);
  intro (Trade.trade (partial_rel items pm none v ** S.pts_to input #pm w) (S.pts_to input #pm w)) #emp fn _ {
    rewrite (partial_rel items pm none v) as emp;
  };
  fold (loop_inv items pm input w v input w none (S.len input));
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
    loop_inv items pm input w v r wr st rem
    decreases (SZ.v (!prem))
  {
    let r = !pr;
    let st = !pst;
    let rem = !prem;
    let res = set_any_step items disp input #pm #w #v r st rem;
    pr := fst (fst res);
    pst := snd (fst res);
    prem := snd res;
  };
  let st = !pst;
  let r = !pr;
  let rem = !prem;
  with wr . assert (loop_inv items pm input w v r wr st rem);
  unfold (loop_inv items pm input w v r wr st rem);
  final items w wr st v;
  let res = fin st #pm #v;
  Trade.elim_hyp_r (partial_rel items pm st v) (S.pts_to r #pm wr) (S.pts_to input #pm w);
  Trade.trans (asn1_items_rel items pm res v) (partial_rel items pm st v) (S.pts_to input #pm w);
  res
}

inline_for_extraction
fn set_any_parser
  (#ids: Ghost.erased id_decs)
  (items: Ghost.erased (asn1_gen_items_l ids))
  (pf: squash (asn1_set_k_wf ids))
  (none: (x: opt_tuple (Ghost.reveal items) { x == none_tuple (Ghost.reveal items) }))
  (disp: disp_t (Ghost.reveal items))
  (fin: fin_t (Ghost.reveal items))
: aparser #(asn1_items_impl_t (Ghost.reveal items)) #(asn1_sequence_t_core (Ghost.reveal items)) (asn1_items_rel (Ghost.reveal items)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  init items pf w v;
  set_any_loop items none disp fin input #pm #w #v
}
