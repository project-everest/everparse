module LowParse.PulseParse.Iterator.Het
#lang-pulse

(* Heterogeneous splitting and absorption of mixed-list matches.

   - `mixed_list_match_split`: if the element parser `p1` parses some bytes,
     then `p2` parses them too, to a related value (`parsers_fwd p1 p2 r`),
     and every element match `vmatch1 pm x y1` can be split into
     `vmatch1 (pm / 2) x y1 ** vmatch2 (pm / 2) x y2` when `r y1 y2`, then
     `mixed_list_match vmatch1 io p1 pm il l1` can be split into
     `mixed_list_match vmatch1 io p1 (pm / 2) il l1 **
      mixed_list_match vmatch2 io p2 (pm / 2) il l2` when the lists are
     related elementwise (`list_rel r l1 l2`).

   - `mixed_list_match_absorb`: conversely, if every element match
     `vmatch1 pm1 x y1 ** vmatch2 pm2 x y2` can be absorbed into
     `vmatch1 (pm1 + pm2) x y1`, then so can the mixed-list matches, whatever
     the values of the second list. *)

include LowParse.PulseParse.Iterator.Rel
open LowParse.PulseParse.Iterator.Type
open Pulse.Lib.Pervasives
open FStar.Real

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module IO = LowParse.PulseParse.Iterator.IntOps
module SM = Pulse.Lib.SeqMatch
module L = FStar.List.Tot

let parsers_fwd (#k: parser_kind) (#u1 #u2: Type) (p1: parser k u1) (p2: parser k u2) (r: u1 -> u2 -> prop) : prop =
  forall (b: bytes) . match parse p1 b with
  | None -> True
  | Some (v1, c1) ->
    begin match parse p2 b with
    | Some (v2, c2) -> r v1 v2 /\ c1 == c2
    | None -> False
    end

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec parse_nlist_fwd (n: nat) (#k: parser_kind) (#u1 #u2: Type) (p1: parser k u1) (p2: parser k u2) (r: u1 -> u2 -> prop) (b: bytes)
: Lemma (requires (parsers_fwd p1 p2 r))
  (ensures (match parse (parse_nlist n p1) b with
    | None -> True
    | Some (l1, c1) ->
      begin match parse (parse_nlist n p2) b with
      | Some (l2, c2) -> list_rel r l1 l2 /\ c1 == c2
      | None -> False
      end))
  (decreases n)
= parse_nlist_eq n p1 b;
  parse_nlist_eq n p2 b;
  if n = 0 then ()
  else match parse p1 b with
  | None -> ()
  | Some (_, c) ->
    parse_nlist_fwd (n - 1) p1 p2 r (Seq.slice b c (Seq.length b))
#pop-options

(* Element matches of slices *)

ghost
fn rec seq_list_match_split
  (#t #u1 #u2: Type0)
  (c: Seq.seq t)
  (v1: list u1)
  (v2: list u2)
  (vm1: t -> u1 -> slprop)
  (vm1': t -> u1 -> slprop)
  (vm2: t -> u2 -> slprop)
  (r: u1 -> u2 -> prop)
  (prf: (x: t) -> (y1: u1) -> (y2: u2 { r y1 y2 }) -> stt_ghost unit emp_inames (vm1 x y1) (fun _ -> vm1' x y1 ** vm2 x y2))
requires
    SM.seq_list_match c v1 vm1 ** pure (list_rel r v1 v2)
ensures
    SM.seq_list_match c v1 vm1' ** SM.seq_list_match c v2 vm2
decreases v1
{
  if Nil? v1 {
    SM.seq_list_match_nil_elim c v1 vm1;
    SM.seq_list_match_nil_intro c v1 vm1';
    SM.seq_list_match_nil_intro c v2 vm2;
  } else {
    SM.seq_list_match_cons_elim c v1 vm1;
    prf (Seq.head c) (L.hd v1) (L.hd v2);
    seq_list_match_split (Seq.tail c) (L.tl v1) (L.tl v2) vm1 vm1' vm2 r prf;
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (L.hd v1) (Seq.tail c) (L.tl v1) vm1';
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (L.hd v1 :: L.tl v1) vm1')
         as (SM.seq_list_match c v1 vm1');
    SM.seq_list_match_cons_intro (Seq.head c) (L.hd v2) (Seq.tail c) (L.tl v2) vm2;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (L.hd v2 :: L.tl v2) vm2)
         as (SM.seq_list_match c v2 vm2);
  }
}

ghost
fn rec seq_list_match_absorb
  (#t #u1 #u2: Type0)
  (c: Seq.seq t)
  (v1: list u1)
  (v2: list u2)
  (vm1: t -> u1 -> slprop)
  (vm2: t -> u2 -> slprop)
  (vm1': t -> u1 -> slprop)
  (prf: (x: t) -> (y1: u1) -> (y2: u2) -> stt_ghost unit emp_inames (vm1 x y1 ** vm2 x y2) (fun _ -> vm1' x y1))
requires
    SM.seq_list_match c v1 vm1 ** SM.seq_list_match c v2 vm2
ensures
    SM.seq_list_match c v1 vm1'
decreases v1
{
  if Nil? v1 {
    SM.seq_list_match_nil_elim c v1 vm1;
    SM.seq_list_match_nil_elim c v2 vm2;
    SM.seq_list_match_nil_intro c v1 vm1';
  } else {
    SM.seq_list_match_cons_elim c v1 vm1;
    SM.seq_list_match_cons_elim c v2 vm2;
    prf (Seq.head c) (L.hd v1) (L.hd v2);
    seq_list_match_absorb (Seq.tail c) (L.tl v1) (L.tl v2) vm1 vm2 vm1' prf;
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (L.hd v1) (Seq.tail c) (L.tl v1) vm1';
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (L.hd v1 :: L.tl v1) vm1')
         as (SM.seq_list_match c v1 vm1');
  }
}

let split_t (#t #u1 #u2: Type0) (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop) (r: u1 -> u2 -> prop) : Type =
  (x: t) -> (pm0: perm) -> (y1: u1) -> (y2: u2 { r y1 y2 }) ->
  stt_ghost unit emp_inames (vmatch1 pm0 x y1) (fun _ -> vmatch1 (pm0 /. 2.0R) x y1 ** vmatch2 (pm0 /. 2.0R) x y2)

let absorb_t (#t #u1 #u2: Type0) (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop) : Type =
  (x: t) -> (pm1: perm) -> (pm2: perm) -> (y1: u1) -> (y2: u2) ->
  stt_ghost unit emp_inames (vmatch1 pm1 x y1 ** vmatch2 pm2 x y2) (fun _ -> vmatch1 (pm1 +. pm2) x y1)

(* Base mixed lists *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"

ghost
fn base_mixed_list_match_n_split_singleton_pos
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l1: list u1) (l2: list u2)
  (prf: split_t vmatch1 vmatch2 r)
  (_: squash (n <> 0))
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm (Singleton sp sv s) l1 ** pure (list_rel r l1 l2)
ensures
    base_mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) (Singleton sp sv s) l1 **
    base_mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) (Singleton sp sv s) l2
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch1 io p1 off n pm sp sv s l1 ();
  with x y . assert (pts_to s #(pm *. sp) x ** vmatch1 (pm *. sv) x y ** pure (l1 == [y] /\ off == 0 /\ n == 1));
  let y2 = L.hd l2;
  R.share s;
  rewrite (R.pts_to s #((pm *. sp) /. 2.0R) x) as (R.pts_to s #((pm /. 2.0R) *. sp) x);
  rewrite (R.pts_to s #((pm *. sp) /. 2.0R) x) as (R.pts_to s #((pm /. 2.0R) *. sp) x);
  prf x (pm *. sv) y y2;
  rewrite (vmatch1 ((pm *. sv) /. 2.0R) x y) as (vmatch1 ((pm /. 2.0R) *. sv) x y);
  rewrite (vmatch2 ((pm *. sv) /. 2.0R) x y2) as (vmatch2 ((pm /. 2.0R) *. sv) x y2);
  Pulse.Lib.Core.intro_pure (l2 == [y2] /\ off == 0 /\ n == 1) ();
  base_mixed_list_match_n_singleton_fold_pos vmatch2 io p2 off n (pm /. 2.0R) sp sv s l2 ();
  base_mixed_list_match_n_singleton_fold_pos vmatch1 io p1 off n (pm /. 2.0R) sp sv s l1 ()
}

ghost
fn base_mixed_list_match_n_split
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (sq: squash (parsers_fwd p1 p2 r /\ rel_functional r))
  (off: nat)
  (n: nat)
  (pm: perm)
  (il: base_mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: split_t vmatch1 vmatch2 r)
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm il l1 ** pure (list_rel r l1 l2)
ensures
    base_mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) il l1 **
    base_mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) il l2
{
  match il {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm (Empty #i #t) l1);
      fold (base_mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) (Empty #i #t) l1);
      fold (base_mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) (Empty #i #t) l2);
    }
    Singleton sp sv s -> {
      if (n = 0) {
        base_mixed_list_match_n_singleton_unfold_0 vmatch1 io p1 off n pm sp sv s l1 ();
        Pulse.Lib.Core.intro_pure (Nil? l1 /\ off <= 1) ();
        base_mixed_list_match_n_singleton_fold_0 vmatch1 io p1 off n (pm /. 2.0R) sp sv s l1 ();
        base_mixed_list_match_n_singleton_fold_0 vmatch2 io p2 off n (pm /. 2.0R) sp sv s l2 ();
      } else {
        base_mixed_list_match_n_split_singleton_pos vmatch1 vmatch2 io p1 p2 r off n pm sp sv s l1 l2 prf ();
      };
    }
    Slice sp sv s count -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm (Slice #i #t sp sv s count) l1);
      with l' c1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match c1 l1 (vmatch1 (pm *. sv)));
      S.share s;
      rewrite (pts_to s #((pm *. sp) /. 2.0R) l') as (pts_to s #((pm /. 2.0R) *. sp) l');
      rewrite (pts_to s #((pm *. sp) /. 2.0R) l') as (pts_to s #((pm /. 2.0R) *. sp) l');
      ghost fn prf'
        (x: t) (y1: u1) (y2: u2 { r y1 y2 })
      requires vmatch1 (pm *. sv) x y1
      ensures vmatch1 ((pm /. 2.0R) *. sv) x y1 ** vmatch2 ((pm /. 2.0R) *. sv) x y2
      {
        prf x (pm *. sv) y1 y2;
        rewrite (vmatch1 ((pm *. sv) /. 2.0R) x y1) as (vmatch1 ((pm /. 2.0R) *. sv) x y1);
        rewrite (vmatch2 ((pm *. sv) /. 2.0R) x y2) as (vmatch2 ((pm /. 2.0R) *. sv) x y2);
      };
      seq_list_match_split c1 l1 l2 (vmatch1 (pm *. sv)) (vmatch1 ((pm /. 2.0R) *. sv)) (vmatch2 ((pm /. 2.0R) *. sv)) r prf';
      fold (base_mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) (Slice #i #t sp sv s count) l1);
      fold (base_mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) (Slice #i #t sp sv s count) l2);
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm (Serialized #i #t sp count pl) l1);
      with l_all1 . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #(pm *. sp) l_all1);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #(pm *. sp) l_all1);
      with w . assert (S.pts_to pl #(pm *. sp) w);
      parse_nlist_fwd (off + n) p1 p2 r w;
      let l_all2 : Ghost.erased (list u2) = Ghost.hide (fst (Some?.v (parse (parse_nlist (off + n) p2) w)) <: list u2);
      list_rel_splitAt r off l_all1 l_all2;
      list_rel_functional r l1 l2 (snd (L.splitAt off l_all2));
      S.share pl;
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) w) as (S.pts_to pl #((pm /. 2.0R) *. sp) w);
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) w) as (S.pts_to pl #((pm /. 2.0R) *. sp) w);
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #((pm /. 2.0R) *. sp) l_all1);
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p2) pl #((pm /. 2.0R) *. sp) l_all2);
      fold (base_mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) (Serialized #i #t sp count pl) l1);
      fold (base_mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) (Serialized #i #t sp count pl) l2);
    }
  }
}

ghost
fn base_mixed_list_match_n_absorb_singleton_pos
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (off: nat)
  (n: nat)
  (pm1 pm2: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l1: list u1) (l2: list u2)
  (prf: absorb_t vmatch1 vmatch2)
  (_: squash (n <> 0))
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm1 (Singleton sp sv s) l1 **
    base_mixed_list_match_n vmatch2 io p2 off n pm2 (Singleton sp sv s) l2
ensures
    base_mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) (Singleton sp sv s) l1
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch1 io p1 off n pm1 sp sv s l1 ();
  base_mixed_list_match_n_singleton_unfold_pos vmatch2 io p2 off n pm2 sp sv s l2 ();
  with x1 y1 . assert (pts_to s #(pm1 *. sp) x1 ** vmatch1 (pm1 *. sv) x1 y1 ** pure (l1 == [y1] /\ off == 0 /\ n == 1));
  with x2 y2 . assert (pts_to s #(pm2 *. sp) x2 ** vmatch2 (pm2 *. sv) x2 y2);
  R.gather s;
  rewrite (R.pts_to s #(pm1 *. sp +. pm2 *. sp) x1) as (R.pts_to s #((pm1 +. pm2) *. sp) x1);
  rewrite each x2 as x1;
  prf x1 (pm1 *. sv) (pm2 *. sv) y1 y2;
  rewrite (vmatch1 (pm1 *. sv +. pm2 *. sv) x1 y1) as (vmatch1 ((pm1 +. pm2) *. sv) x1 y1);
  base_mixed_list_match_n_singleton_fold_pos vmatch1 io p1 off n (pm1 +. pm2) sp sv s l1 ()
}

ghost
fn base_mixed_list_match_n_absorb
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (off: nat)
  (n: nat)
  (pm1 pm2: perm)
  (il: base_mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: absorb_t vmatch1 vmatch2)
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm1 il l1 **
    base_mixed_list_match_n vmatch2 io p2 off n pm2 il l2
ensures
    base_mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) il l1
{
  match il {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm1 (Empty #i #t) l1);
      unfold (base_mixed_list_match_n vmatch2 io p2 off n pm2 (Empty #i #t) l2);
      fold (base_mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) (Empty #i #t) l1);
    }
    Singleton sp sv s -> {
      if (n = 0) {
        base_mixed_list_match_n_singleton_unfold_0 vmatch1 io p1 off n pm1 sp sv s l1 ();
        base_mixed_list_match_n_singleton_unfold_0 vmatch2 io p2 off n pm2 sp sv s l2 ();
        base_mixed_list_match_n_singleton_fold_0 vmatch1 io p1 off n (pm1 +. pm2) sp sv s l1 ();
      } else {
        base_mixed_list_match_n_absorb_singleton_pos vmatch1 vmatch2 io p1 p2 off n pm1 pm2 sp sv s l1 l2 prf ();
      };
    }
    Slice sp sv s count -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm1 (Slice #i #t sp sv s count) l1);
      unfold (base_mixed_list_match_n vmatch2 io p2 off n pm2 (Slice #i #t sp sv s count) l2);
      with la c1 . assert (pts_to s #(pm1 *. sp) la ** SM.seq_list_match c1 l1 (vmatch1 (pm1 *. sv)));
      with la' c2 . assert (pts_to s #(pm2 *. sp) la' ** SM.seq_list_match c2 l2 (vmatch2 (pm2 *. sv)));
      S.gather s;
      rewrite (pts_to s #(pm1 *. sp +. pm2 *. sp) la) as (pts_to s #((pm1 +. pm2) *. sp) la);
      rewrite each la' as la;
      rewrite each c2 as c1;
      ghost fn prf'
        (x: t) (y1: u1) (y2: u2)
      requires vmatch1 (pm1 *. sv) x y1 ** vmatch2 (pm2 *. sv) x y2
      ensures vmatch1 ((pm1 +. pm2) *. sv) x y1
      {
        prf x (pm1 *. sv) (pm2 *. sv) y1 y2;
        rewrite (vmatch1 (pm1 *. sv +. pm2 *. sv) x y1) as (vmatch1 ((pm1 +. pm2) *. sv) x y1);
      };
      seq_list_match_absorb c1 l1 l2 (vmatch1 (pm1 *. sv)) (vmatch2 (pm2 *. sv)) (vmatch1 ((pm1 +. pm2) *. sv)) prf';
      fold (base_mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) (Slice #i #t sp sv s count) l1);
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm1 (Serialized #i #t sp count pl) l1);
      unfold (base_mixed_list_match_n vmatch2 io p2 off n pm2 (Serialized #i #t sp count pl) l2);
      with lv . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #(pm1 *. sp) lv);
      with lv' . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p2) pl #(pm2 *. sp) lv');
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #(pm1 *. sp) lv);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p2) pl #(pm2 *. sp) lv');
      with v1 . assert (S.pts_to pl #(pm1 *. sp) v1);
      with v2 . assert (S.pts_to pl #(pm2 *. sp) v2);
      S.gather pl;
      rewrite (S.pts_to pl #(pm1 *. sp +. pm2 *. sp) v1) as (S.pts_to pl #((pm1 +. pm2) *. sp) v1);
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #((pm1 +. pm2) *. sp) lv);
      fold (base_mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) (Serialized #i #t sp count pl) l1);
    }
  }
}

#pop-options

(* Mixed lists *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn rec mixed_list_match_n_split
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (sq: squash (parsers_fwd p1 p2 r /\ rel_functional r))
  (off: nat)
  (n: nat)
  (pm: perm)
  (il: mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: split_t vmatch1 vmatch2 r)
requires
    mixed_list_match_n vmatch1 io p1 off n pm il l1 ** pure (list_rel r l1 l2)
ensures
    mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) il l1 **
    mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) il l2
decreases (mixed_list_depth il)
{
  match il {
    Base bi -> {
      unfold (mixed_list_match_n vmatch1 io p1 off n pm (Base #i #t bi) l1);
      base_mixed_list_match_n_split vmatch1 vmatch2 io p1 p2 r sq off n pm bi l1 l2 prf;
      fold (mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) (Base #i #t bi) l1);
      fold (mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) (Base #i #t bi) l2);
    }
    Append depth cb ca tot ob bp before oa ap after sc -> {
      unfold (mixed_list_match_n vmatch1 io p1 off n pm (Append #i #t depth cb ca tot ob bp before oa ap after sc) l1);
      with i_before i_after la lb . assert (
        pts_to before #(pm *. bp) i_before **
        mixed_list_match_n vmatch1 io p1 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm *. sc) i_before la **
        pts_to after #(pm *. ap) i_after **
        mixed_list_match_n vmatch1 io p1 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm *. sc) i_after lb
      );
      list_rel_append_inv r la lb l2;
      let la' : Ghost.erased (list u2) = Ghost.hide (fst (L.splitAt (L.length la) l2));
      let lb' : Ghost.erased (list u2) = Ghost.hide (snd (L.splitAt (L.length la) l2));
      R.share before;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      mixed_list_match_n_split vmatch1 vmatch2 io p1 p2 r sq (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm *. sc) i_before la la' prf;
      mixed_list_match_n_split vmatch1 vmatch2 io p1 p2 r sq (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm *. sc) i_after lb lb' prf;
      rewrite (mixed_list_match_n vmatch1 io p1 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) ((pm *. sc) /. 2.0R) i_before la)
        as (mixed_list_match_n vmatch1 io p1 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) ((pm /. 2.0R) *. sc) i_before la);
      rewrite (mixed_list_match_n vmatch2 io p2 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) ((pm *. sc) /. 2.0R) i_before la')
        as (mixed_list_match_n vmatch2 io p2 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) ((pm /. 2.0R) *. sc) i_before la');
      rewrite (mixed_list_match_n vmatch1 io p1 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) ((pm *. sc) /. 2.0R) i_after lb)
        as (mixed_list_match_n vmatch1 io p1 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) ((pm /. 2.0R) *. sc) i_after lb);
      rewrite (mixed_list_match_n vmatch2 io p2 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) ((pm *. sc) /. 2.0R) i_after lb')
        as (mixed_list_match_n vmatch2 io p2 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) ((pm /. 2.0R) *. sc) i_after lb');
      fold (mixed_list_match_n vmatch1 io p1 off n (pm /. 2.0R) (Append #i #t depth cb ca tot ob bp before oa ap after sc) l1);
      fold (mixed_list_match_n vmatch2 io p2 off n (pm /. 2.0R) (Append #i #t depth cb ca tot ob bp before oa ap after sc) l2);
    }
  }
}

ghost
fn rec mixed_list_match_n_absorb
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (off: nat)
  (n: nat)
  (pm1 pm2: perm)
  (il: mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: absorb_t vmatch1 vmatch2)
requires
    mixed_list_match_n vmatch1 io p1 off n pm1 il l1 **
    mixed_list_match_n vmatch2 io p2 off n pm2 il l2
ensures
    mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) il l1
decreases (mixed_list_depth il)
{
  match il {
    Base bi -> {
      unfold (mixed_list_match_n vmatch1 io p1 off n pm1 (Base #i #t bi) l1);
      unfold (mixed_list_match_n vmatch2 io p2 off n pm2 (Base #i #t bi) l2);
      base_mixed_list_match_n_absorb vmatch1 vmatch2 io p1 p2 off n pm1 pm2 bi l1 l2 prf;
      fold (mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) (Base #i #t bi) l1);
    }
    Append depth cb ca tot ob bp before oa ap after sc -> {
      unfold (mixed_list_match_n vmatch1 io p1 off n pm1 (Append #i #t depth cb ca tot ob bp before oa ap after sc) l1);
      unfold (mixed_list_match_n vmatch2 io p2 off n pm2 (Append #i #t depth cb ca tot ob bp before oa ap after sc) l2);
      with i_before1 i_after1 la lb . assert (
        pts_to before #(pm1 *. bp) i_before1 **
        mixed_list_match_n vmatch1 io p1 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm1 *. sc) i_before1 la **
        pts_to after #(pm1 *. ap) i_after1 **
        mixed_list_match_n vmatch1 io p1 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm1 *. sc) i_after1 lb
      );
      with i_before2 i_after2 la' lb' . assert (
        pts_to before #(pm2 *. bp) i_before2 **
        mixed_list_match_n vmatch2 io p2 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm2 *. sc) i_before2 la' **
        pts_to after #(pm2 *. ap) i_after2 **
        mixed_list_match_n vmatch2 io p2 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm2 *. sc) i_after2 lb'
      );
      R.gather before;
      rewrite (R.pts_to before #(pm1 *. bp +. pm2 *. bp) i_before1) as (R.pts_to before #((pm1 +. pm2) *. bp) i_before1);
      rewrite (mixed_list_match_n vmatch2 io p2 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm2 *. sc) i_before2 la')
        as (mixed_list_match_n vmatch2 io p2 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm2 *. sc) i_before1 la');
      R.gather after;
      rewrite (R.pts_to after #(pm1 *. ap +. pm2 *. ap) i_after1) as (R.pts_to after #((pm1 +. pm2) *. ap) i_after1);
      rewrite (mixed_list_match_n vmatch2 io p2 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm2 *. sc) i_after2 lb')
        as (mixed_list_match_n vmatch2 io p2 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm2 *. sc) i_after1 lb');
      mixed_list_match_n_absorb vmatch1 vmatch2 io p1 p2 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm1 *. sc) (pm2 *. sc) i_before1 la la' prf;
      mixed_list_match_n_absorb vmatch1 vmatch2 io p1 p2 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm1 *. sc) (pm2 *. sc) i_after1 lb lb' prf;
      rewrite (mixed_list_match_n vmatch1 io p1 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm1 *. sc +. pm2 *. sc) i_before1 la)
        as (mixed_list_match_n vmatch1 io p1 (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) ((pm1 +. pm2) *. sc) i_before1 la);
      rewrite (mixed_list_match_n vmatch1 io p1 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm1 *. sc +. pm2 *. sc) i_after1 lb)
        as (mixed_list_match_n vmatch1 io p1 (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) ((pm1 +. pm2) *. sc) i_after1 lb);
      fold (mixed_list_match_n vmatch1 io p1 off n (pm1 +. pm2) (Append #i #t depth cb ca tot ob bp before oa ap after sc) l1);
    }
  }
}

#pop-options

ghost
fn mixed_list_match_split
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (sq: squash (parsers_fwd p1 p2 r /\ rel_functional r))
  (pm: perm)
  (il: mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: split_t vmatch1 vmatch2 r)
requires
    mixed_list_match vmatch1 io p1 pm il l1 ** pure (list_rel r l1 l2)
ensures
    mixed_list_match vmatch1 io p1 (pm /. 2.0R) il l1 **
    mixed_list_match vmatch2 io p2 (pm /. 2.0R) il l2
{
  unfold (mixed_list_match vmatch1 io p1 pm il l1);
  mixed_list_match_n_split vmatch1 vmatch2 io p1 p2 r sq 0 (io.v (mixed_list_length io il)) pm il l1 l2 prf;
  fold (mixed_list_match vmatch1 io p1 (pm /. 2.0R) il l1);
  fold (mixed_list_match vmatch2 io p2 (pm /. 2.0R) il l2)
}

ghost
fn mixed_list_match_absorb
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (pm1 pm2: perm)
  (il: mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: absorb_t vmatch1 vmatch2)
requires
    mixed_list_match vmatch1 io p1 pm1 il l1 **
    mixed_list_match vmatch2 io p2 pm2 il l2
ensures
    mixed_list_match vmatch1 io p1 (pm1 +. pm2) il l1
{
  unfold (mixed_list_match vmatch1 io p1 pm1 il l1);
  unfold (mixed_list_match vmatch2 io p2 pm2 il l2);
  mixed_list_match_n_absorb vmatch1 vmatch2 io p1 p2 0 (io.v (mixed_list_length io il)) pm1 pm2 il l1 l2 prf;
  fold (mixed_list_match vmatch1 io p1 (pm1 +. pm2) il l1)
}
