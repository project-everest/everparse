module LowParse.PulseParse.Iterator.Rel
#lang-pulse

(* Transporting a mixed-list match along a relation between element values:
   if two element parsers `p1` and `p2` parse the same bytes to related
   values (`parsers_rel p1 p2 r`), the relation `r` is functional, and every
   element match `vmatch1 pm x y1` can be turned into `vmatch2 pm x y2` when
   `r y1 y2`, then `mixed_list_match vmatch1 io p1 pm il l1` can be turned
   into `mixed_list_match vmatch2 io p2 pm il l2` when the lists are related
   elementwise (`list_rel r l1 l2`).

   For instance, with `p2 = parse_synth p1 f` and `r y1 y2 = (y2 == f y1)`,
   this maps the list of values by `f`; and conversely, with
   `r y2 y1 = (y2 == f y1)`, if `f` is injective. *)

include LowParse.PulseParse.Iterator
open LowParse.PulseParse.Iterator.Type
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module IO = LowParse.PulseParse.Iterator.IntOps
module SM = Pulse.Lib.SeqMatch
module L = FStar.List.Tot

let rec list_rel (#u1 #u2: Type) (r: u1 -> u2 -> prop) (l1: list u1) (l2: list u2) : Tot prop (decreases l1) =
  match l1, l2 with
  | [], [] -> True
  | a1 :: q1, a2 :: q2 -> r a1 a2 /\ list_rel r q1 q2
  | _ -> False

let rel_functional (#u1 #u2: Type) (r: u1 -> u2 -> prop) : prop =
  forall (a: u1) (b b': u2) . (r a b /\ r a b') ==> b == b'

let parsers_rel (#k: parser_kind) (#u1 #u2: Type) (p1: parser k u1) (p2: parser k u2) (r: u1 -> u2 -> prop) : prop =
  forall (b: bytes) . match parse p1 b, parse p2 b with
  | None, None -> True
  | Some (v1, c1), Some (v2, c2) -> r v1 v2 /\ c1 == c2
  | _ -> False

let rec list_rel_length (#u1 #u2: Type) (r: u1 -> u2 -> prop) (l1: list u1) (l2: list u2)
: Lemma (requires (list_rel r l1 l2)) (ensures (L.length l1 == L.length l2)) (decreases l1)
= match l1, l2 with
  | _ :: q1, _ :: q2 -> list_rel_length r q1 q2
  | _ -> ()

let rec list_rel_functional (#u1 #u2: Type) (r: u1 -> u2 -> prop) (l1: list u1) (l2 l2': list u2)
: Lemma (requires (rel_functional r /\ list_rel r l1 l2 /\ list_rel r l1 l2')) (ensures (l2 == l2')) (decreases l1)
= match l1, l2, l2' with
  | _ :: q1, _ :: q2, _ :: q2' -> list_rel_functional r q1 q2 q2'
  | _ -> ()

let rec list_rel_splitAt (#u1 #u2: Type) (r: u1 -> u2 -> prop) (n: nat) (l1: list u1) (l2: list u2)
: Lemma (requires (list_rel r l1 l2))
  (ensures (
    list_rel r (fst (L.splitAt n l1)) (fst (L.splitAt n l2)) /\
    list_rel r (snd (L.splitAt n l1)) (snd (L.splitAt n l2))))
  (decreases l1)
= if n = 0 then () else
  match l1, l2 with
  | _ :: q1, _ :: q2 -> list_rel_splitAt r (n - 1) q1 q2
  | _ -> ()

let rec list_rel_append_inv (#u1 #u2: Type) (r: u1 -> u2 -> prop) (a b: list u1) (l2: list u2)
: Lemma (requires (list_rel r (L.append a b) l2))
  (ensures (
    let (a', b') = L.splitAt (L.length a) l2 in
    l2 == L.append a' b' /\
    list_rel r a a' /\ list_rel r b b' /\
    L.length a' == L.length a /\ L.length b' == L.length b))
  (decreases a)
= match a, l2 with
  | _ :: q, _ :: q2 -> list_rel_append_inv r q b q2
  | _ -> list_rel_length r b l2

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec parse_nlist_rel (n: nat) (#k: parser_kind) (#u1 #u2: Type) (p1: parser k u1) (p2: parser k u2) (r: u1 -> u2 -> prop) (b: bytes)
: Lemma (requires (parsers_rel p1 p2 r))
  (ensures (match parse (parse_nlist n p1) b, parse (parse_nlist n p2) b with
    | None, None -> True
    | Some (l1, c1), Some (l2, c2) -> list_rel r l1 l2 /\ c1 == c2
    | _ -> False))
  (decreases n)
= parse_nlist_eq n p1 b;
  parse_nlist_eq n p2 b;
  if n = 0 then ()
  else match parse p1 b with
  | None -> ()
  | Some (_, c) ->
    parse_nlist_rel (n - 1) p1 p2 r (Seq.slice b c (Seq.length b))
#pop-options

(* Element matches of slices *)

ghost
fn rec seq_list_match_rel
  (#t #u1 #u2: Type0)
  (c: Seq.seq t)
  (v1: list u1)
  (v2: list u2)
  (vm1: t -> u1 -> slprop)
  (vm2: t -> u2 -> slprop)
  (r: u1 -> u2 -> prop)
  (prf: (x: t) -> (y1: u1) -> (y2: u2 { r y1 y2 }) -> stt_ghost unit emp_inames (vm1 x y1) (fun _ -> vm2 x y2))
requires
    SM.seq_list_match c v1 vm1 ** pure (list_rel r v1 v2)
ensures
    SM.seq_list_match c v2 vm2
decreases v1
{
  if Nil? v1 {
    SM.seq_list_match_nil_elim c v1 vm1;
    SM.seq_list_match_nil_intro c v2 vm2;
  } else {
    SM.seq_list_match_cons_elim c v1 vm1;
    prf (Seq.head c) (L.hd v1) (L.hd v2);
    seq_list_match_rel (Seq.tail c) (L.tl v1) (L.tl v2) vm1 vm2 r prf;
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (L.hd v2) (Seq.tail c) (L.tl v2) vm2;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (L.hd v2 :: L.tl v2) vm2)
         as (SM.seq_list_match c v2 vm2);
  }
}

(* Base mixed lists *)

ghost
fn base_mixed_list_match_n_rel_singleton_pos
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
  (prf: (x: t) -> (pm0: perm) -> (y1: u1) -> (y2: u2 { r y1 y2 }) -> stt_ghost unit emp_inames (vmatch1 pm0 x y1) (fun _ -> vmatch2 pm0 x y2))
  (_: squash (n <> 0))
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm (Singleton sp sv s) l1 ** pure (list_rel r l1 l2)
ensures
    base_mixed_list_match_n vmatch2 io p2 off n pm (Singleton sp sv s) l2
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch1 io p1 off n pm sp sv s l1 ();
  with x y . assert (pts_to s #(pm *. sp) x ** vmatch1 (pm *. sv) x y ** pure (l1 == [y] /\ off == 0 /\ n == 1));
  let y2 = L.hd l2;
  prf x (pm *. sv) y y2;
  Pulse.Lib.Core.intro_pure (l2 == [y2] /\ off == 0 /\ n == 1) ();
  base_mixed_list_match_n_singleton_fold_pos vmatch2 io p2 off n pm sp sv s l2 ()
}

ghost
fn base_mixed_list_match_n_rel_singleton_0
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
  (_: squash (n == 0))
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm (Singleton sp sv s) l1 ** pure (list_rel r l1 l2)
ensures
    base_mixed_list_match_n vmatch2 io p2 off n pm (Singleton sp sv s) l2
{
  base_mixed_list_match_n_singleton_unfold_0 vmatch1 io p1 off n pm sp sv s l1 ();
  base_mixed_list_match_n_singleton_fold_0 vmatch2 io p2 off n pm sp sv s l2 ()
}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"

ghost
fn base_mixed_list_match_n_rel
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (sq: squash (parsers_rel p1 p2 r /\ rel_functional r))
  (off: nat)
  (n: nat)
  (pm: perm)
  (il: base_mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: (x: t) -> (pm0: perm) -> (y1: u1) -> (y2: u2 { r y1 y2 }) -> stt_ghost unit emp_inames (vmatch1 pm0 x y1) (fun _ -> vmatch2 pm0 x y2))
requires
    base_mixed_list_match_n vmatch1 io p1 off n pm il l1 ** pure (list_rel r l1 l2)
ensures
    base_mixed_list_match_n vmatch2 io p2 off n pm il l2
{
  match il {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm (Empty #i #t) l1);
      fold (base_mixed_list_match_n vmatch2 io p2 off n pm (Empty #i #t) l2);
    }
    Singleton sp sv s -> {
      if (n = 0) {
        base_mixed_list_match_n_rel_singleton_0 vmatch1 vmatch2 io p1 p2 r off n pm sp sv s l1 l2 ();
      } else {
        base_mixed_list_match_n_rel_singleton_pos vmatch1 vmatch2 io p1 p2 r off n pm sp sv s l1 l2 prf ();
      };
    }
    Slice sp sv s count -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm (Slice #i #t sp sv s count) l1);
      with l' c1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match c1 l1 (vmatch1 (pm *. sv)));
      ghost fn prf'
        (x: t) (y1: u1) (y2: u2 { r y1 y2 })
      requires vmatch1 (pm *. sv) x y1
      ensures vmatch2 (pm *. sv) x y2
      {
        prf x (pm *. sv) y1 y2
      };
      seq_list_match_rel c1 l1 l2 (vmatch1 (pm *. sv)) (vmatch2 (pm *. sv)) r prf';
      fold (base_mixed_list_match_n vmatch2 io p2 off n pm (Slice #i #t sp sv s count) l2);
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch1 io p1 off n pm (Serialized #i #t sp count pl) l1);
      with l_all1 . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #(pm *. sp) l_all1);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p1) pl #(pm *. sp) l_all1);
      with w . assert (S.pts_to pl #(pm *. sp) w);
      parse_nlist_rel (off + n) p1 p2 r w;
      let l_all2 : Ghost.erased (list u2) = Ghost.hide (fst (Some?.v (parse (parse_nlist (off + n) p2) w)) <: list u2);
      list_rel_splitAt r off l_all1 l_all2;
      list_rel_functional r l1 l2 (snd (L.splitAt off l_all2));
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p2) pl #(pm *. sp) l_all2);
      fold (base_mixed_list_match_n vmatch2 io p2 off n pm (Serialized #i #t sp count pl) l2);
    }
  }
}

#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn rec mixed_list_match_n_rel
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (sq: squash (parsers_rel p1 p2 r /\ rel_functional r))
  (off: nat)
  (n: nat)
  (pm: perm)
  (il: mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: (x: t) -> (pm0: perm) -> (y1: u1) -> (y2: u2 { r y1 y2 }) -> stt_ghost unit emp_inames (vmatch1 pm0 x y1) (fun _ -> vmatch2 pm0 x y2))
requires
    mixed_list_match_n vmatch1 io p1 off n pm il l1 ** pure (list_rel r l1 l2)
ensures
    mixed_list_match_n vmatch2 io p2 off n pm il l2
decreases (mixed_list_depth il)
{
  match il {
    Base bi -> {
      unfold (mixed_list_match_n vmatch1 io p1 off n pm (Base #i #t bi) l1);
      base_mixed_list_match_n_rel vmatch1 vmatch2 io p1 p2 r sq off n pm bi l1 l2 prf;
      fold (mixed_list_match_n vmatch2 io p2 off n pm (Base #i #t bi) l2);
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
      mixed_list_match_n_rel vmatch1 vmatch2 io p1 p2 r sq (append_off_before off (io.v ob) (io.v cb)) (append_n_before off n (io.v cb)) (pm *. sc) i_before la la' prf;
      mixed_list_match_n_rel vmatch1 vmatch2 io p1 p2 r sq (append_off_after off (io.v oa) (io.v cb)) (append_n_after off n (io.v cb)) (pm *. sc) i_after lb lb' prf;
      fold (mixed_list_match_n vmatch2 io p2 off n pm (Append #i #t depth cb ca tot ob bp before oa ap after sc) l2);
    }
  }
}

#pop-options

ghost
fn mixed_list_match_rel
  (#t #u1 #u2: Type0)
  (vmatch1: perm -> t -> u1 -> slprop) (vmatch2: perm -> t -> u2 -> slprop)
  (#i: Type0) (io: IO.int_ops i)
  (#k: parser_kind)
  (p1: parser k u1) (p2: parser k u2)
  (r: u1 -> u2 -> prop)
  (sq: squash (parsers_rel p1 p2 r /\ rel_functional r))
  (pm: perm)
  (il: mixed_list i t)
  (l1: list u1) (l2: list u2)
  (prf: (x: t) -> (pm0: perm) -> (y1: u1) -> (y2: u2 { r y1 y2 }) -> stt_ghost unit emp_inames (vmatch1 pm0 x y1) (fun _ -> vmatch2 pm0 x y2))
requires
    mixed_list_match vmatch1 io p1 pm il l1 ** pure (list_rel r l1 l2)
ensures
    mixed_list_match vmatch2 io p2 pm il l2
{
  unfold (mixed_list_match vmatch1 io p1 pm il l1);
  mixed_list_match_n_rel vmatch1 vmatch2 io p1 p2 r sq 0 (io.v (mixed_list_length io il)) pm il l1 l2 prf;
  fold (mixed_list_match vmatch2 io p2 pm il l2)
}
