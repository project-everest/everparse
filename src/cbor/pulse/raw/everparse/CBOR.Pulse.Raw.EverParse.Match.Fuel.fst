module CBOR.Pulse.Raw.EverParse.Match.Fuel
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Match

open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open LowParse.Pulse.Base
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Base
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module SM = Pulse.Lib.SeqMatch
open LowParse.PulseParse.Iterator.Type

let rec cbor_raw_match_fuel
  (n: nat)
:
  (pm: perm) ->
  (xl: cbor_raw) ->
  (xh: raw_data_item) ->
  Tot slprop
= if n = 0
  then fun _ _ _ -> pure False
  else cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1))

let cbor_raw_match_fuel_eq_zero
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Lemma
  (cbor_raw_match_fuel 0 pm xl xh == pure False)
= ()

let cbor_raw_match_fuel_eq_succ
  (n: nat)
  (pm: perm)
  (xl: cbor_raw)
  (xh: raw_data_item)
: Lemma
  (requires (n > 0))
  (ensures (
    cbor_raw_match_fuel n pm xl xh ==
    cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm xl xh
  ))
= ()

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn rec cbor_raw_match_fuel_share
  (n: nat)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh
ensures cbor_raw_match_fuel n (pm /. 2.0R) xl xh **
        cbor_raw_match_fuel n (pm /. 2.0R) xl xh
decreases n
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    let n' : nat = n - 1;
    cbor_raw_match_fuel_eq_succ n pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') pm xl (Ghost.reveal xh));
    ghost fn share_rec
      (x1: cbor_raw) (#p0: perm) (#x2: raw_data_item)
    requires cbor_raw_match_fuel n' p0 x1 x2
    ensures cbor_raw_match_fuel n' (p0 /. 2.0R) x1 x2 **
            cbor_raw_match_fuel n' (p0 /. 2.0R) x1 x2
    {
      cbor_raw_match_fuel_share n' x1 #p0 #x2
    };
    cbor_raw_match_aux_share
      (cbor_raw_match_fuel n')
      share_rec
      parse_raw_data_item
      xl;
    cbor_raw_match_fuel_eq_succ n (pm /. 2.0R) xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') (pm /. 2.0R) xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n (pm /. 2.0R) xl (Ghost.reveal xh));
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') (pm /. 2.0R) xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n (pm /. 2.0R) xl (Ghost.reveal xh));
  }
}

ghost
fn rec cbor_raw_match_fuel_gather
  (n: nat)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
  (#pm': perm)
  (#xh': Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh **
         cbor_raw_match_fuel n pm' xl xh'
ensures cbor_raw_match_fuel n (pm +. pm') xl xh **
        pure (xh == xh')
decreases n
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    let n' : nat = n - 1;
    cbor_raw_match_fuel_eq_succ n pm xl (Ghost.reveal xh);
    cbor_raw_match_fuel_eq_succ n pm' xl (Ghost.reveal xh');
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') pm xl (Ghost.reveal xh));
    rewrite (cbor_raw_match_fuel n pm' xl (Ghost.reveal xh'))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') pm' xl (Ghost.reveal xh'));
    ghost fn gather_rec
      (x1: cbor_raw) (#pm0: perm) (#x2: raw_data_item) (#pm0': perm) (x2': raw_data_item { x2' << Ghost.reveal xh' })
    requires cbor_raw_match_fuel n' pm0 x1 x2 ** cbor_raw_match_fuel n' pm0' x1 x2'
    ensures cbor_raw_match_fuel n' (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
    {
      cbor_raw_match_fuel_gather n' x1 #pm0 #x2 #pm0' #x2'
    };
    cbor_raw_match_aux_gather
      (cbor_raw_match_fuel n')
      parse_raw_data_item
      xl
      #pm #xh #pm' #xh'
      gather_rec;
    cbor_raw_match_fuel_eq_succ n (pm +. pm') xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel n') (pm +. pm') xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n (pm +. pm') xl (Ghost.reveal xh));
  }
}

#pop-options

ghost
fn cbor_raw_match_fuel_implies_pos
  (n: nat)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh
ensures cbor_raw_match_fuel n pm xl xh ** pure (n >= 1)
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    ()
  }
}

ghost
fn cbor_raw_match_fuel_share_t
  (n: nat)
: share_t (cbor_raw_match_fuel n)
= (xl: cbor_raw)
  (#pm: perm)
  (#xh: raw_data_item)
{
  cbor_raw_match_fuel_share n xl #pm #(Ghost.hide xh)
}

ghost
fn cbor_raw_match_fuel_gather_t
  (n: nat)
: gather_t (cbor_raw_match_fuel n)
= (xl: cbor_raw)
  (#pm: perm)
  (#xh: raw_data_item)
  (#pm': perm)
  (#xh': raw_data_item)
{
  cbor_raw_match_fuel_gather n xl #pm #(Ghost.hide xh) #pm' #(Ghost.hide xh')
}

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn rec cbor_raw_match_fuel_weaken
  (n: nat)
  (n': nat { n' >= n })
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh
ensures cbor_raw_match_fuel n' pm xl xh
decreases n
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    let m : nat = n - 1;
    let m' : nat = n' - 1;
    cbor_raw_match_fuel_eq_succ n pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel m) pm xl (Ghost.reveal xh));
    ghost fn weaken_rec
      (x1: cbor_raw) (pm0: perm) (x2: raw_data_item { x2 << Ghost.reveal xh })
    requires cbor_raw_match_fuel m pm0 x1 x2
    ensures cbor_raw_match_fuel m' pm0 x1 x2
    {
      cbor_raw_match_fuel_weaken m m' x1 #pm0 #(Ghost.hide x2)
    };
    cbor_raw_match_aux_weaken
      (cbor_raw_match_fuel m)
      (cbor_raw_match_fuel m')
      parse_raw_data_item
      xl
      weaken_rec;
    cbor_raw_match_fuel_eq_succ n' pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel m') pm xl (Ghost.reveal xh))
         as (cbor_raw_match_fuel n' pm xl (Ghost.reveal xh));
  }
}

ghost
fn rec cbor_raw_match_of_fuel
  (n: nat)
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match_fuel n pm xl xh
ensures cbor_raw_match pm xl xh
decreases n
{
  if (n = 0) {
    cbor_raw_match_fuel_eq_zero pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (pure False);
    unreachable ()
  } else {
    let m : nat = n - 1;
    cbor_raw_match_fuel_eq_succ n pm xl (Ghost.reveal xh);
    rewrite (cbor_raw_match_fuel n pm xl (Ghost.reveal xh))
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel m) pm xl (Ghost.reveal xh));
    ghost fn weaken_rec
      (x1: cbor_raw) (pm0: perm) (x2: raw_data_item { x2 << Ghost.reveal xh })
    requires cbor_raw_match_fuel m pm0 x1 x2
    ensures cbor_raw_match pm0 x1 x2
    {
      cbor_raw_match_of_fuel m x1 #pm0 #(Ghost.hide x2)
    };
    cbor_raw_match_aux_weaken
      (cbor_raw_match_fuel m)
      cbor_raw_match
      parse_raw_data_item
      xl
      weaken_rec;
    cbor_raw_match_fold_aux xl #pm #xh;
  }
}

#pop-options

(* ======== From cbor_raw_match to cbor_raw_match_fuel ========

   We want a ghost function that produces some fuel level n such that
   cbor_raw_match_fuel n holds. Strategy: walk the cbor_raw_match
   structure (recursively on xh), recursively converting each
   sub-element to fuel, taking the max of all sub-fuels, then weakening
   everyone to that max via cbor_raw_match_fuel_weaken. Return max + 1
   to cover the current level.

   We need auxiliary walkers for:
   - seq_list_match (the list-matching primitive inside Slice variants)
   - base_mixed_list_match_n and mixed_list_match_n (used in array/map
     content)
   - cbor_map_entry_match (each entry has two cbor_raw_match's)

   These walkers are parameterized by an element-to-fuel closure, which
   is supplied via the top-level recursive call.
*)

let nat_max (a b: nat) : nat = if a > b then a else b

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* Generic walker: seq_list_match c l (vmatch1 pm) -> max fuel m, plus
   seq_list_match c l (vmatch2 m pm). Recursive in l. The output vmatch2
   is indexed by a nat (the fuel level), and we require a weakening
   lemma on it that increases the index. *)
ghost
fn rec seq_list_match_to_fuel
  (#t: Type0)
  (#u: Type0)
  (vmatch1: perm -> t -> u -> slprop)
  (vmatch2: nat -> perm -> t -> u -> slprop)
  (l: list u)
  (vmatch2_weaken: (
    (n1: nat) -> (n2: nat { n1 <= n2 }) ->
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch2 n1 pm0 x y)
      (fun _ -> vmatch2 n2 pm0 x y)
  ))
  (to_fuel_elem: (
    (x: t) -> (pm0: perm) ->
    (y: u { List.Tot.memP y l }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (vmatch1 pm0 x y)
      (fun n -> vmatch2 (Ghost.reveal n) pm0 x y)
  ))
  (c: Seq.seq t)
  (pm: perm)
requires SM.seq_list_match c l (vmatch1 pm)
returns m: Ghost.erased nat
ensures SM.seq_list_match c l (vmatch2 (Ghost.reveal m) pm)
decreases l
{
  if (Nil? l) {
    SM.seq_list_match_nil_elim c l (vmatch1 pm);
    SM.seq_list_match_nil_intro c l (vmatch2 0 pm);
    Ghost.hide 0
  } else {
    SM.list_cons_precedes (List.Tot.hd l) (List.Tot.tl l);
    let _ : squash (List.Tot.tl l << l) = ();
    SM.seq_list_match_cons_elim c l (vmatch1 pm);
    let n_hd = to_fuel_elem (Seq.head c) pm (List.Tot.hd l);
    ghost fn to_fuel_elem_tl
      (x1: t) (pm1: perm)
      (y: u { List.Tot.memP y (List.Tot.tl l) })
    requires vmatch1 pm1 x1 y
    returns n: Ghost.erased nat
    ensures vmatch2 (Ghost.reveal n) pm1 x1 y
    {
      to_fuel_elem x1 pm1 y
    };
    ghost fn vmatch2_weaken_tl
      (n1: nat) (n2: nat { n1 <= n2 })
      (x1: t) (pm1: perm)
      (y: u { List.Tot.memP y (List.Tot.tl l) })
    requires vmatch2 n1 pm1 x1 y
    ensures vmatch2 n2 pm1 x1 y
    {
      vmatch2_weaken n1 n2 x1 pm1 y
    };
    let n_tl = seq_list_match_to_fuel vmatch1 vmatch2 (List.Tot.tl l) vmatch2_weaken_tl to_fuel_elem_tl (Seq.tail c) pm;
    let m : Ghost.erased nat = Ghost.hide (nat_max (Ghost.reveal n_hd) (Ghost.reveal n_tl));
    vmatch2_weaken (Ghost.reveal n_hd) (Ghost.reveal m) (Seq.head c) pm (List.Tot.hd l);
    ghost fn weaken_tl
      (x1: t)
      (y: u { List.Tot.memP y (List.Tot.tl l) })
    requires vmatch2 (Ghost.reveal n_tl) pm x1 y
    ensures vmatch2 (Ghost.reveal m) pm x1 y
    {
      vmatch2_weaken (Ghost.reveal n_tl) (Ghost.reveal m) x1 pm y
    };
    I.seq_list_match_weaken_memP (Seq.tail c) (List.Tot.tl l)
      (vmatch2 (Ghost.reveal n_tl) pm)
      (vmatch2 (Ghost.reveal m) pm)
      weaken_tl;
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) (vmatch2 (Ghost.reveal m) pm);
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd l :: List.Tot.tl l) (vmatch2 (Ghost.reveal m) pm))
         as (SM.seq_list_match c l (vmatch2 (Ghost.reveal m) pm));
    m
  }
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* Walker for base_mixed_list_match_n. Computes max fuel m and converts
   the input vmatch1 to the indexed output vmatch2 at level m. *)
ghost
fn base_mixed_list_match_n_to_fuel
  (#t: Type0)
  (#u: Type0)
  (vmatch1: perm -> t -> u -> slprop)
  (vmatch2: nat -> perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: IT.base_mixed_list t)
  (l: list u)
  (vmatch2_weaken: (
    (n1: nat) -> (n2: nat { n1 <= n2 }) ->
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch2 n1 pm0 x y)
      (fun _ -> vmatch2 n2 pm0 x y)
  ))
  (to_fuel_elem: (
    (x: t) -> (pm0: perm) ->
    (y: u { List.Tot.memP y l }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (vmatch1 pm0 x y)
      (fun n -> vmatch2 (Ghost.reveal n) pm0 x y)
  ))
requires I.base_mixed_list_match_n vmatch1 p off n pm i l
returns m: Ghost.erased nat
ensures I.base_mixed_list_match_n (vmatch2 (Ghost.reveal m)) p off n pm i l
{
  match i {
    Empty -> {
      unfold (I.base_mixed_list_match_n vmatch1 p off n pm (IT.Empty #t) l);
      fold (I.base_mixed_list_match_n (vmatch2 0) p off n pm (IT.Empty #t) l);
      rewrite each (IT.Empty #t) as i;
      Ghost.hide 0
    }
    Singleton sp sv s -> {
      if (n = 0) {
        I.base_mixed_list_match_n_singleton_unfold_0 vmatch1 p off n pm sp sv s l ();
        I.base_mixed_list_match_n_singleton_fold_0 (vmatch2 0) p off n pm sp sv s l ();
        rewrite each (IT.Singleton #t sp sv s) as i;
        Ghost.hide 0
      } else {
        I.base_mixed_list_match_n_singleton_unfold_pos vmatch1 p off n pm sp sv s l ();
        with x y . assert (R.pts_to s #(pm *. sp) x ** vmatch1 (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1));
        let sq : squash (l == [y] /\ off == 0 /\ n == 1) = elim_pure_explicit (l == [y] /\ off == 0 /\ n == 1);
        let m_y = to_fuel_elem x (pm *. sv) y;
        intro_pure (l == [y] /\ off == 0 /\ n == 1) sq;
        I.base_mixed_list_match_n_singleton_fold_pos (vmatch2 (Ghost.reveal m_y)) p off n pm sp sv s l ();
        rewrite each (IT.Singleton #t sp sv s) as i;
        m_y
      }
    }
    Slice sp sv s -> {
      unfold (I.base_mixed_list_match_n vmatch1 p off n pm (IT.Slice #t sp sv s) l);
      with l' l1 . assert (
        pts_to s #(pm *. sp) l' **
        SM.seq_list_match l1 l (vmatch1 (pm *. sv)) **
        pure (off + n <= Seq.length l' /\ l1 == Seq.slice l' off (off + n))
      );
      let m_s = seq_list_match_to_fuel vmatch1 vmatch2 l vmatch2_weaken to_fuel_elem l1 (pm *. sv);
      fold (I.base_mixed_list_match_n (vmatch2 (Ghost.reveal m_s)) p off n pm (IT.Slice #t sp sv s) l);
      rewrite each (IT.Slice #t sp sv s) as i;
      m_s
    }
    Serialized sp count pl -> {
      unfold (I.base_mixed_list_match_n vmatch1 p off n pm (IT.Serialized #t sp count pl) l);
      fold (I.base_mixed_list_match_n (vmatch2 0) p off n pm (IT.Serialized #t sp count pl) l);
      rewrite each (IT.Serialized #t sp count pl) as i;
      Ghost.hide 0
    }
  }
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* Walker for mixed_list_match_n. Recursive in mixed_list_depth.
   For Append: walks before/after halves, takes max, weakens both to max. *)
ghost
fn rec mixed_list_match_n_to_fuel
  (#t: Type0)
  (#u: Type0)
  (vmatch1: perm -> t -> u -> slprop)
  (vmatch2: nat -> perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: IT.mixed_list t)
  (l: list u)
  (vmatch2_weaken: (
    (n1: nat) -> (n2: nat { n1 <= n2 }) ->
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch2 n1 pm0 x y)
      (fun _ -> vmatch2 n2 pm0 x y)
  ))
  (to_fuel_elem: (
    (x: t) -> (pm0: perm) ->
    (y: u { List.Tot.memP y l }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (vmatch1 pm0 x y)
      (fun n -> vmatch2 (Ghost.reveal n) pm0 x y)
  ))
requires I.mixed_list_match_n vmatch1 p off n pm i l
returns m: Ghost.erased nat
ensures I.mixed_list_match_n (vmatch2 (Ghost.reveal m)) p off n pm i l
decreases (I.mixed_list_depth i)
{
  match i {
    Base bi -> {
      unfold (I.mixed_list_match_n vmatch1 p off n pm (Base #t bi) l);
      let m_b = base_mixed_list_match_n_to_fuel vmatch1 vmatch2 p off n pm bi l vmatch2_weaken to_fuel_elem;
      fold (I.mixed_list_match_n (vmatch2 (Ghost.reveal m_b)) p off n pm (Base #t bi) l);
      rewrite each (Base #t bi) as i;
      m_b
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (I.mixed_list_match_n vmatch1 p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        I.mixed_list_match_n vmatch1 p (I.append_off_before off (SZ.v ob) (SZ.v cb)) (I.append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        I.mixed_list_match_n vmatch1 p (I.append_off_after off (SZ.v oa) (SZ.v cb)) (I.append_n_after off n (SZ.v cb)) pm i_after l2
      );
      List.Tot.Properties.append_memP_forall l1 l2;
      ghost fn to_fuel_elem_l1
        (x: t) (pm0: perm)
        (y: u { List.Tot.memP y l1 })
      requires vmatch1 pm0 x y
      returns n: Ghost.erased nat
      ensures vmatch2 (Ghost.reveal n) pm0 x y
      {
        to_fuel_elem x pm0 y
      };
      ghost fn to_fuel_elem_l2
        (x: t) (pm0: perm)
        (y: u { List.Tot.memP y l2 })
      requires vmatch1 pm0 x y
      returns n: Ghost.erased nat
      ensures vmatch2 (Ghost.reveal n) pm0 x y
      {
        to_fuel_elem x pm0 y
      };
      ghost fn vmatch2_weaken_l1
        (n1: nat) (n2: nat { n1 <= n2 })
        (x: t) (pm0: perm)
        (y: u { List.Tot.memP y l1 })
      requires vmatch2 n1 pm0 x y
      ensures vmatch2 n2 pm0 x y
      {
        vmatch2_weaken n1 n2 x pm0 y
      };
      ghost fn vmatch2_weaken_l2
        (n1: nat) (n2: nat { n1 <= n2 })
        (x: t) (pm0: perm)
        (y: u { List.Tot.memP y l2 })
      requires vmatch2 n1 pm0 x y
      ensures vmatch2 n2 pm0 x y
      {
        vmatch2_weaken n1 n2 x pm0 y
      };
      let m_b = mixed_list_match_n_to_fuel vmatch1 vmatch2 p (I.append_off_before off (SZ.v ob) (SZ.v cb)) (I.append_n_before off n (SZ.v cb)) pm i_before l1 vmatch2_weaken_l1 to_fuel_elem_l1;
      let m_a = mixed_list_match_n_to_fuel vmatch1 vmatch2 p (I.append_off_after off (SZ.v oa) (SZ.v cb)) (I.append_n_after off n (SZ.v cb)) pm i_after l2 vmatch2_weaken_l2 to_fuel_elem_l2;
      let m : Ghost.erased nat = Ghost.hide (nat_max (Ghost.reveal m_b) (Ghost.reveal m_a));
      ghost fn weaken_l1
        (x: t) (pm0: perm)
        (y: u { List.Tot.memP y l1 })
      requires vmatch2 (Ghost.reveal m_b) pm0 x y
      ensures vmatch2 (Ghost.reveal m) pm0 x y
      {
        vmatch2_weaken (Ghost.reveal m_b) (Ghost.reveal m) x pm0 y
      };
      ghost fn weaken_l2
        (x: t) (pm0: perm)
        (y: u { List.Tot.memP y l2 })
      requires vmatch2 (Ghost.reveal m_a) pm0 x y
      ensures vmatch2 (Ghost.reveal m) pm0 x y
      {
        vmatch2_weaken (Ghost.reveal m_a) (Ghost.reveal m) x pm0 y
      };
      I.mixed_list_match_n_weaken (vmatch2 (Ghost.reveal m_b)) (vmatch2 (Ghost.reveal m)) p (I.append_off_before off (SZ.v ob) (SZ.v cb)) (I.append_n_before off n (SZ.v cb)) pm i_before l1 weaken_l1;
      I.mixed_list_match_n_weaken (vmatch2 (Ghost.reveal m_a)) (vmatch2 (Ghost.reveal m)) p (I.append_off_after off (SZ.v oa) (SZ.v cb)) (I.append_n_after off n (SZ.v cb)) pm i_after l2 weaken_l2;
      fold (I.mixed_list_match_n (vmatch2 (Ghost.reveal m)) p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
      m
    }
  }
}

#pop-options

(* ======== to_fuel helpers ========

   Helpers analogous to p_weaken_from_memP / p_weaken_pair_from_memP.
   They convert a closure taking (y: { y << bound }) to one taking
   (y: { memP y l }) given that l << bound. *)

inline_for_extraction
let to_fuel_elem_from_memP
  (#bound_t: Type0)
  (#bound: bound_t)
  (l: list raw_data_item)
  (sq_l: squash (l << bound))
  (to_fuel_elem: (
    (x1: cbor_raw) -> (pm0: perm) ->
    (x2: raw_data_item { x2 << bound }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (cbor_raw_match pm0 x1 x2)
      (fun n -> cbor_raw_match_fuel (Ghost.reveal n) pm0 x1 x2)
  ))
  (x1: cbor_raw) (pm0: perm) (x2: raw_data_item { List.Tot.memP x2 l })
: stt_ghost (Ghost.erased nat) emp_inames
    (cbor_raw_match pm0 x1 x2)
    (fun n -> cbor_raw_match_fuel (Ghost.reveal n) pm0 x1 x2)
= List.Tot.Properties.memP_precedes x2 l;
  to_fuel_elem x1 pm0 x2

(* The "vmatch2" weaken for arrays is just cbor_raw_match_fuel_weaken.
   Provided as a closure-friendly form (no memP refinement). *)
let cbor_raw_match_fuel_weaken_unconditional
  (n1: nat) (n2: nat { n1 <= n2 })
  (x: cbor_raw) (pm0: perm) (y: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_raw_match_fuel n1 pm0 x y)
    (fun _ -> cbor_raw_match_fuel n2 pm0 x y)
= cbor_raw_match_fuel_weaken n1 n2 x #pm0 #(Ghost.hide y)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* Walker for one cbor_map_entry: takes two cbor_raw_match (key & value)
   and produces cbor_map_entry_match wrapping cbor_raw_match_fuel m,
   where m is the max of the key and value fuels. *)
ghost
fn cbor_map_entry_match_to_fuel
  (#bound_t: Type0) (#bound: bound_t)
  (to_fuel_elem: (
    (x: cbor_raw) -> (pm0: perm) ->
    (y: raw_data_item { y << bound }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (cbor_raw_match pm0 x y)
      (fun n -> cbor_raw_match_fuel (Ghost.reveal n) pm0 x y)
  ))
  (entry: cbor_map_entry cbor_raw)
  (pm: perm)
  (pair: (raw_data_item & raw_data_item) { pair << bound })
requires cbor_map_entry_match cbor_raw_match pm entry pair
returns m: Ghost.erased nat
ensures cbor_map_entry_match (cbor_raw_match_fuel (Ghost.reveal m)) pm entry pair
{
  unfold (cbor_map_entry_match cbor_raw_match pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm entry.cbor_map_entry_value (snd pair));
  let n_k = to_fuel_elem entry.cbor_map_entry_key pm (fst pair);
  let n_v = to_fuel_elem entry.cbor_map_entry_value pm (snd pair);
  let m : Ghost.erased nat = Ghost.hide (nat_max (Ghost.reveal n_k) (Ghost.reveal n_v));
  cbor_raw_match_fuel_weaken (Ghost.reveal n_k) (Ghost.reveal m) entry.cbor_map_entry_key #pm #(Ghost.hide (fst pair));
  cbor_raw_match_fuel_weaken (Ghost.reveal n_v) (Ghost.reveal m) entry.cbor_map_entry_value #pm #(Ghost.hide (snd pair));
  rewrite (cbor_raw_match_fuel (Ghost.reveal m) pm entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match_fuel (Ghost.reveal m) pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match_fuel (Ghost.reveal m) pm entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match_fuel (Ghost.reveal m) pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match_fuel (Ghost.reveal m) pm) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match_fuel (Ghost.reveal m) pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel (Ghost.reveal m) pm) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match (cbor_raw_match_fuel (Ghost.reveal m)) pm entry pair);
  m
}

#pop-options

inline_for_extraction
let to_fuel_pair_from_memP
  (#bound_t: Type0)
  (#bound: bound_t)
  (l: list (raw_data_item & raw_data_item))
  (sq_l: squash (l << bound))
  (to_fuel_elem: (
    (x1: cbor_raw) -> (pm0: perm) ->
    (x2: raw_data_item { x2 << bound }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (cbor_raw_match pm0 x1 x2)
      (fun n -> cbor_raw_match_fuel (Ghost.reveal n) pm0 x1 x2)
  ))
  (entry: cbor_map_entry cbor_raw)
  (pm0: perm)
  (pair: (raw_data_item & raw_data_item) { List.Tot.memP pair l })
: stt_ghost (Ghost.erased nat) emp_inames
    (cbor_map_entry_match cbor_raw_match pm0 entry pair)
    (fun n -> cbor_map_entry_match (cbor_raw_match_fuel (Ghost.reveal n)) pm0 entry pair)
= List.Tot.Properties.memP_precedes pair l;
  cbor_map_entry_match_to_fuel #bound_t #bound to_fuel_elem entry pm0 pair

ghost
fn cbor_map_entry_match_fuel_weaken
  (n1: nat) (n2: nat { n1 <= n2 })
  (entry: cbor_map_entry cbor_raw) (pm0: perm)
  (pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_match (cbor_raw_match_fuel n1) pm0 entry pair
ensures cbor_map_entry_match (cbor_raw_match_fuel n2) pm0 entry pair
{
  unfold (cbor_map_entry_match (cbor_raw_match_fuel n1) pm0 entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel n1 pm0) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n1 pm0) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel n1 pm0) cbor_map_entry_value_proj entry (snd pair));
  rewrite (cbor_raw_match_fuel n1 pm0 (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match_fuel n1 pm0 entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match_fuel n1 pm0 (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match_fuel n1 pm0 entry.cbor_map_entry_value (snd pair));
  cbor_raw_match_fuel_weaken n1 n2 entry.cbor_map_entry_key #pm0 #(Ghost.hide (fst pair));
  cbor_raw_match_fuel_weaken n1 n2 entry.cbor_map_entry_value #pm0 #(Ghost.hide (snd pair));
  rewrite (cbor_raw_match_fuel n2 pm0 entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match_fuel n2 pm0 (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match_fuel n2 pm0 entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match_fuel n2 pm0 (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match_fuel n2 pm0) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match_fuel n2 pm0) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n2 pm0) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match (cbor_raw_match_fuel n2) pm0 entry pair);
}

(* Wrapper of mixed_list_match_n_to_fuel for non-_n mixed_list_match. *)
let mixed_list_match_to_fuel
  (#t: Type0)
  (#u: Type0)
  (vmatch1: perm -> t -> u -> slprop)
  (vmatch2: nat -> perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: IT.mixed_list t)
  (l: list u)
  (vmatch2_weaken: (
    (n1: nat) -> (n2: nat { n1 <= n2 }) ->
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch2 n1 pm0 x y)
      (fun _ -> vmatch2 n2 pm0 x y)
  ))
  (to_fuel_elem: (
    (x: t) -> (pm0: perm) ->
    (y: u { List.Tot.memP y l }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (vmatch1 pm0 x y)
      (fun n -> vmatch2 (Ghost.reveal n) pm0 x y)
  ))
: stt_ghost (Ghost.erased nat) emp_inames
    (I.mixed_list_match vmatch1 p pm i l)
    (fun n -> I.mixed_list_match (vmatch2 (Ghost.reveal n)) p pm i l)
= mixed_list_match_n_to_fuel vmatch1 vmatch2 p 0 (SZ.v (IT.mixed_list_length i)) pm i l vmatch2_weaken to_fuel_elem

#push-options "--z3rlimit 256 --fuel 4 --ifuel 4"

(* cbor_raw_match_content_to_fuel mirrors cbor_raw_match_content_weaken but
   walks the contents to compute a fuel value. *)

ghost fn cbor_raw_match_content_to_fuel
  (#kp: parser_kind)
  (pp: parser kp raw_data_item)
  (h: header)
  (xl: cbor_raw)
  (pm: perm)
  (c: content h)
  (#bound_t: Type0)
  (#bound: bound_t)
  (to_fuel_elem: (
    (x1: cbor_raw) -> (pm0: perm) ->
    (x2: raw_data_item { x2 << bound }) ->
    stt_ghost (Ghost.erased nat) emp_inames
      (cbor_raw_match pm0 x1 x2)
      (fun n -> cbor_raw_match_fuel (Ghost.reveal n) pm0 x1 x2)
  ))
requires cbor_raw_match_content cbor_raw_match pp pm h xl c **
         pure (content_uses_p_gather h ==> c << bound)
returns m: Ghost.erased nat
ensures cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c
{
  let _sq_bound = elim_pure_explicit (content_uses_p_gather h ==> c << bound);
  let b = dfst h;
  let la = dsnd h;
  header_eta h;
  rewrite (cbor_raw_match_content cbor_raw_match pp pm h xl c)
       as (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) xl c);
  if (b.major_type = cbor_major_type_byte_string || b.major_type = cbor_major_type_text_string) {
    match xl {
      CBOR_Case_String v -> {
        cbor_raw_match_content_eq_string cbor_raw_match pp pm b la v c;
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_String v) c)
             as (S.pts_to (to_slice v.cbor_string_ptr) #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c));
        let m : Ghost.erased nat = Ghost.hide 0;
        cbor_raw_match_content_eq_string (cbor_raw_match_fuel (Ghost.reveal m)) pp pm b la v c;
        rewrite (S.pts_to (to_slice v.cbor_string_ptr) #(pm *. v.cbor_string_perm) (content_as_seq_u8 b la c))
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_String v) c);
        rewrite (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_String v) c)
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c);
        m
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_array) {
    match xl {
      CBOR_Case_Array v -> {
        cbor_raw_match_content_eq_array cbor_raw_match pp pm b la v c;
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (I.mixed_list_match
                   cbor_raw_match
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        let cl = content_as_list_raw b la c;
        rewrite (I.mixed_list_match
                   cbor_raw_match
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (I.mixed_list_match
                   cbor_raw_match
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   cl);
        ghost fn vmatch2_weaken_arr
          (n1: nat) (n2: nat { n1 <= n2 })
          (x: cbor_raw) (pm0: perm) (y: raw_data_item { List.Tot.memP y cl })
        requires cbor_raw_match_fuel n1 pm0 x y
        ensures cbor_raw_match_fuel n2 pm0 x y
        {
          cbor_raw_match_fuel_weaken n1 n2 x #pm0 #(Ghost.hide y)
        };
        let m = mixed_list_match_to_fuel
          cbor_raw_match
          cbor_raw_match_fuel
          pp
          (pm *. v.cbor_array_slice_perm)
          v.cbor_array_ptr
          cl
          vmatch2_weaken_arr
          (to_fuel_elem_from_memP #bound_t #bound cl () to_fuel_elem);
        rewrite (I.mixed_list_match
                   (cbor_raw_match_fuel (Ghost.reveal m))
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   cl)
             as (I.mixed_list_match
                   (cbor_raw_match_fuel (Ghost.reveal m))
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c));
        cbor_raw_match_content_eq_array (cbor_raw_match_fuel (Ghost.reveal m)) pp pm b la v c;
        rewrite (I.mixed_list_match
                   (cbor_raw_match_fuel (Ghost.reveal m))
                   pp
                   (pm *. v.cbor_array_slice_perm)
                   v.cbor_array_ptr
                   (content_as_list_raw b la c))
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Array v) c);
        rewrite (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Array v) c)
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c);
        m
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_map) {
    match xl {
      CBOR_Case_Map v -> {
        cbor_raw_match_content_eq_map cbor_raw_match pp pm b la v c;
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Map v) c)
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match cbor_raw_match pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        let cl = content_as_list_pair b la c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match cbor_raw_match pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match cbor_raw_match pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   cl);
        ghost fn vmatch2_weaken_map
          (n1: nat) (n2: nat { n1 <= n2 })
          (x: cbor_map_entry cbor_raw) (pm0: perm)
          (y: (raw_data_item & raw_data_item) { List.Tot.memP y cl })
        requires cbor_map_entry_match (cbor_raw_match_fuel n1) pm0 x y
        ensures cbor_map_entry_match (cbor_raw_match_fuel n2) pm0 x y
        {
          cbor_map_entry_match_fuel_weaken n1 n2 x pm0 y
        };
        let m = mixed_list_match_to_fuel
          (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
               (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match cbor_raw_match pm' elem x)
          (fun (n: nat) (pm': perm) (elem: cbor_map_entry cbor_raw)
               (x: (raw_data_item & raw_data_item)) ->
            cbor_map_entry_match (cbor_raw_match_fuel n) pm' elem x)
          (nondep_then pp pp)
          (pm *. v.cbor_map_slice_perm)
          v.cbor_map_ptr
          cl
          vmatch2_weaken_map
          (to_fuel_pair_from_memP #bound_t #bound cl () to_fuel_elem);
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match (cbor_raw_match_fuel (Ghost.reveal m)) pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   cl)
             as (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match (cbor_raw_match_fuel (Ghost.reveal m)) pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c));
        cbor_raw_match_content_eq_map (cbor_raw_match_fuel (Ghost.reveal m)) pp pm b la v c;
        rewrite (I.mixed_list_match
                   (fun (pm': perm) (elem: cbor_map_entry cbor_raw)
                        (x: (raw_data_item & raw_data_item)) ->
                     cbor_map_entry_match (cbor_raw_match_fuel (Ghost.reveal m)) pm' elem x)
                   (nondep_then pp pp)
                   (pm *. v.cbor_map_slice_perm)
                   v.cbor_map_ptr
                   (content_as_list_pair b la c))
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Map v) c);
        rewrite (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Map v) c)
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c);
        m
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Tagged_Serialized x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged_Serialized x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
    }
  } else if (b.major_type = cbor_major_type_tagged) {
    match xl {
      CBOR_Case_Tagged v -> {
        cbor_raw_match_content_eq_tagged cbor_raw_match pp pm b la v c;
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_tagged_content_slprop cbor_raw_match pm v (content_as_raw_data_item b la c));
        unfold (cbor_tagged_content_slprop cbor_raw_match pm v (content_as_raw_data_item b la c));
        unfold (vmatch_ref
          (fun (vl: cbor_raw) (vh: raw_data_item) -> cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        with vl . assert (R.pts_to v.cbor_tagged_ptr #(pm *. v.cbor_tagged_ref_perm) vl **
          cbor_raw_match (pm *. v.cbor_tagged_payload_perm) vl (content_as_raw_data_item b la c));
        let m = to_fuel_elem vl (pm *. v.cbor_tagged_payload_perm) (content_as_raw_data_item b la c);
        fold (vmatch_ref
          (fun (vl': cbor_raw) (vh: raw_data_item) -> cbor_raw_match_fuel (Ghost.reveal m) (pm *. v.cbor_tagged_payload_perm) vl' vh)
          ({ v = v.cbor_tagged_ptr; p = pm *. v.cbor_tagged_ref_perm })
          (content_as_raw_data_item b la c));
        fold (cbor_tagged_content_slprop (cbor_raw_match_fuel (Ghost.reveal m)) pm v (content_as_raw_data_item b la c));
        cbor_raw_match_content_eq_tagged (cbor_raw_match_fuel (Ghost.reveal m)) pp pm b la v c;
        rewrite (cbor_tagged_content_slprop (cbor_raw_match_fuel (Ghost.reveal m)) pm v (content_as_raw_data_item b la c))
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Tagged v) c);
        rewrite (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Tagged v) c)
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c);
        m
      }
      CBOR_Case_Tagged_Serialized v -> {
        cbor_raw_match_content_eq_tagged_serialized cbor_raw_match pp pm b la v c;
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (pts_to_parsed_strong_prefix pp (to_slice v.cbor_tagged_serialized_ptr) #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c));
        let m : Ghost.erased nat = Ghost.hide 0;
        cbor_raw_match_content_eq_tagged_serialized (cbor_raw_match_fuel (Ghost.reveal m)) pp pm b la v c;
        rewrite (pts_to_parsed_strong_prefix pp (to_slice v.cbor_tagged_serialized_ptr) #(pm *. v.cbor_tagged_serialized_slice_perm) (content_as_raw_data_item b la c))
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c);
        rewrite (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) (CBOR_Case_Tagged_Serialized v) c)
             as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c);
        m
      }
      CBOR_Case_Invalid -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) CBOR_Case_Invalid c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Int x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Int x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Simple x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Simple x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_String x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_String x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Array x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Array x) c) as (pure False);
        unreachable ()
      }
      CBOR_Case_Map x -> {
        rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) (CBOR_Case_Map x) c) as (pure False);
        unreachable ()
      }
    }
  } else {
    let m : Ghost.erased nat = Ghost.hide 0;
    cbor_raw_match_content_eq_other cbor_raw_match pp pm b la xl c;
    rewrite (cbor_raw_match_content cbor_raw_match pp pm (| b, la |) xl c) as emp;
    cbor_raw_match_content_eq_other (cbor_raw_match_fuel (Ghost.reveal m)) pp pm b la xl c;
    rewrite emp as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) xl c);
    rewrite (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm (| b, la |) xl c)
         as (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) pp pm h xl c);
    m
  }
}

#pop-options

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

(* ======== cbor_raw_match_to_fuel ========

   Recursive walk on xh: convert cbor_raw_match into cbor_raw_match_fuel n
   for some Ghost.erased nat n. Each level computes inner fuel via the
   content walker, then folds via cbor_raw_match_fuel_eq_succ to get n+1. *)

ghost
fn rec cbor_raw_match_to_fuel
  (xl: cbor_raw)
  (#pm: perm)
  (#xh: Ghost.erased raw_data_item)
requires cbor_raw_match pm xl xh
returns n: Ghost.erased nat
ensures cbor_raw_match_fuel (Ghost.reveal n) pm xl xh
decreases (Ghost.reveal xh)
{
  ghost fn to_fuel_elem
    (x1: cbor_raw) (pm0: perm) (x2: raw_data_item { x2 << Ghost.reveal xh })
  requires cbor_raw_match pm0 x1 x2
  returns n: Ghost.erased nat
  ensures cbor_raw_match_fuel (Ghost.reveal n) pm0 x1 x2
  {
    cbor_raw_match_to_fuel x1 #pm0 #(Ghost.hide x2)
  };
  cbor_raw_match_unfold_aux xl #pm #xh;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm xl xh);
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))))
    as
    (pure (cbor_raw_get_header xl ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  let the_prop = cbor_raw_get_header xl ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)));
  let sq = elim_pure_explicit the_prop;
  Classical.move_requires synth_raw_data_item_recip_content_precedes (Ghost.reveal xh);
  intro_pure (content_uses_p_gather (dfst (synth_raw_data_item_recip (Ghost.reveal xh))) ==> dsnd (synth_raw_data_item_recip (Ghost.reveal xh)) << Ghost.reveal xh) ();
  let m = cbor_raw_match_content_to_fuel
    parse_raw_data_item
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))
    xl pm
    (dsnd (synth_raw_data_item_recip (Ghost.reveal xh)))
    #raw_data_item #(Ghost.reveal xh)
    to_fuel_elem;
  intro_pure the_prop sq;
  rewrite (pure the_prop)
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get xl) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal xh)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get xl)
    (dfst (synth_raw_data_item_recip (Ghost.reveal xh))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) parse_raw_data_item pm)
    xl
    (synth_raw_data_item_recip (Ghost.reveal xh)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content (cbor_raw_match_fuel (Ghost.reveal m)) parse_raw_data_item pm))
    synth_raw_data_item_recip
    xl (Ghost.reveal xh));
  fold (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (Ghost.reveal m)) pm xl (Ghost.reveal xh));
  let n : Ghost.erased nat = Ghost.hide (Ghost.reveal m + 1);
  cbor_raw_match_fuel_eq_succ (Ghost.reveal n) pm xl (Ghost.reveal xh);
  rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (Ghost.reveal m)) pm xl (Ghost.reveal xh))
       as (cbor_raw_match_fuel (Ghost.reveal n) pm xl (Ghost.reveal xh));
  n
}

#pop-options
