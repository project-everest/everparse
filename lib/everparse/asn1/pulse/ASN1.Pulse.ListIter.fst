module ASN1.Pulse.ListIter
#lang-pulse

(* Iterators over parsed SEQUENCE OF / SET OF values.

   A parsed list (`arel true (CD_SEQUENCE_OF ne d)`, i.e. `ml_match d`) is
   always the serialized contents of the list together with its element
   count. An iterator is a cursor over these contents: `next` jumps over
   the identifier and length header of the first element, splits the
   slice, and parses (zero-copy) the first element with `parse_d d`, passed
   as the element parser `pk`. The
   element is returned in `arel true d`, so nested lists can be iterated
   in turn. SET OF elements are enumerated in their (DER sorted) encoding
   order. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.Parser

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module VC = LowParse.Spec.VCList
module It = LowParse.PulseParse.Iterator
module ItT = LowParse.PulseParse.Iterator.Type
module LPB = LowParse.PulseParse.Base
module LPS = LowParse.Pulse.Base
module PSO = ASN1.Pulse.ParseSeqOf
module WC = ASN1.Pulse.WriteComb

(* The cursor: the number of remaining elements and their encoding. It does
   not depend on the element type, so it has a single C type. *)

noeq
type iter = {
  count: SZ.t;
  payload: S.slice U8.t;
}

let iter_prop (#s: _) (k: asn1_k s) (n: nat) (w: SB.bytes) (l: list (asn1_t k)) : prop =
  List.Tot.length l == n /\
  (match SB.parse (VC.parse_nlist n #asn1_strong_parser_kind (asn1_as_parser k)) w with
   | Some (l', _) -> (l' <: list (asn1_t k)) == l
   | None -> False)

let iter_match (#s: _) (k: asn1_k s) (pm: perm) (it: iter) (l: list (asn1_t k)) : slprop =
  exists* w . S.pts_to it.payload #pm w ** pure (iter_prop k (SZ.v it.count) w l)

(* Lemmas *)

let ml_match_eq (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (sp: perm) (count: SZ.t) (input: S.slice U8.t) (pm: perm) (l: list (asn1_t k))
: Lemma (PSO.ml_match0 d pm (ItT.Base (ItT.Serialized sp count input)) l ==
    It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized sp count input)) l)
= assert (PSO.ml_match0 d pm (ItT.Base (ItT.Serialized sp count input)) l ==
    It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized sp count input)) l)
    by (FStar.Tactics.V2.norm [delta_only [`%PSO.ml_match0; `%It.mixed_list_match; `%ItT.mixed_list_length; `%ItT.base_mixed_list_length; `%ml_ops; `%LowParse.PulseParse.Iterator.IntOps.sizet_ops; `%LowParse.PulseParse.Iterator.IntOps.__proj__Mkint_ops__item__v]; iota; zeta; primops]; FStar.Tactics.V2.trefl ())

#push-options "--fuel 1 --ifuel 1"
let split_at_0 (#t: Type) (l: list t) : Lemma (snd (List.Tot.splitAt 0 l) == l) = ()
#pop-options

let start_prop (#s: _) (k: asn1_k s) (n: nat) (w: SB.bytes) (l_all: VC.nlist (0 + n) (asn1_t k)) (l: list (asn1_t k))
: Lemma
  (requires LPB.pts_to_parsed_strong_prefix_prop (VC.parse_nlist (0 + n) #asn1_strong_parser_kind (asn1_as_parser k)) w l_all /\
    l == snd (List.Tot.splitAt 0 l_all))
  (ensures iter_prop k n w l)
= split_at_0 l_all

let stop_prop (#s: _) (k: asn1_k s) (n: nat) (w: SB.bytes) (l: list (asn1_t k))
: Lemma
  (requires iter_prop k n w l)
  (ensures List.Tot.length l == 0 + n /\
    LPB.pts_to_parsed_strong_prefix_prop (VC.parse_nlist (0 + n) #asn1_strong_parser_kind (asn1_as_parser k)) w (l <: VC.nlist (0 + n) (asn1_t k)) /\
    l == snd (List.Tot.splitAt 0 l))
= split_at_0 l

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let next_prop (#s: _) (k: asn1_k s) (n: nat) (w: SB.bytes) (l: list (asn1_t k))
: Lemma
  (requires iter_prop k n w l /\ n > 0)
  (ensures (match SB.parse (asn1_as_parser k <: SB.parser asn1_strong_parser_kind (asn1_t k)) w with
    | Some (hd, c) ->
      Cons? l /\ hd == List.Tot.hd l /\ c <= Seq.length w /\
      Seq.slice w 0 (Seq.length w) == w /\
      parsed #asn1_strong_parser_kind (asn1_as_parser k) (Seq.slice w 0 c) hd /\
      iter_prop k (n - 1) (Seq.slice w c (Seq.length w)) (List.Tot.tl l)
    | None -> False))
= let p : SB.parser asn1_strong_parser_kind (asn1_t k) = asn1_as_parser k in
  VC.parse_nlist_eq n p w;
  Seq.slice_length w;
  match SB.parse p w with
  | Some (hd, c) ->
    SB.parse_strong_prefix p w (Seq.slice w 0 c)
#pop-options

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let cons_prop (#s: _) (k: asn1_k s) (n: nat) (wh: SB.bytes) (wt: SB.bytes) (hd: asn1_t k) (tl: list (asn1_t k))
: Lemma
  (requires parsed #asn1_strong_parser_kind (asn1_as_parser k) wh hd /\ iter_prop k n wt tl)
  (ensures iter_prop k (n + 1) (Seq.append wh wt) (hd :: tl))
= let p : SB.parser asn1_strong_parser_kind (asn1_t k) = asn1_as_parser k in
  let w = Seq.append wh wt in
  SB.parse_strong_prefix p wh w;
  assert (Seq.equal (Seq.slice w (Seq.length wh) (Seq.length w)) wt);
  VC.parse_nlist_eq (n + 1) p w
#pop-options

(* Start iterating over a parsed list *)

let start_post (#s: _) (k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (l: list (asn1_t k)) (res: iter) : slprop =
  exists* pm' . iter_match k pm' res l ** Trade.trade (iter_match k pm' res l) (PSO.ml_match d pm x l)

inline_for_extraction
fn start
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (x: ml t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires PSO.ml_match d pm x l
returns res: iter
ensures start_post k d pm x l res
{
  unfold (PSO.ml_match d pm x l);
  let b = ItT.Base?._0 x;
  let count = ItT.Serialized?.count b;
  let payload = ItT.Serialized?.payload b;
  let sp : Ghost.erased perm = ItT.Serialized?.sp b;
  assert (pure (x == ItT.Base (ItT.Serialized sp count payload)));
  ml_match_eq d sp count payload pm l;
  rewrite (PSO.ml_match0 d pm x l)
    as (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized sp count payload)) l);
  unfold (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized sp count payload)) l);
  unfold (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Serialized sp count payload) l);
  with l_all . assert (LPB.pts_to_parsed_strong_prefix (VC.parse_nlist (0 + SZ.v count) #asn1_strong_parser_kind (asn1_as_parser k)) payload #(pm *. sp) l_all);
  unfold (LPB.pts_to_parsed_strong_prefix (VC.parse_nlist (0 + SZ.v count) #asn1_strong_parser_kind (asn1_as_parser k)) payload #(pm *. sp) l_all);
  with w . assert (S.pts_to payload #(pm *. sp) w);
  start_prop k (SZ.v count) w l_all l;
  let res : iter = { count; payload };
  rewrite (S.pts_to payload #(pm *. sp) w) as (S.pts_to res.payload #(pm *. sp) w);
  fold (iter_match k (pm *. sp) res l);
  intro_trade (iter_match k (pm *. sp) res l) (PSO.ml_match d pm x l) emp fn _ {
    unfold (iter_match k (pm *. sp) res l);
    with w' . assert (S.pts_to res.payload #(pm *. sp) w');
    rewrite (S.pts_to res.payload #(pm *. sp) w') as (S.pts_to payload #(pm *. sp) w');
    stop_prop k (SZ.v count) w' l;
    It.pts_to_parsed_strong_prefix_fold (VC.parse_nlist (0 + SZ.v count) #asn1_strong_parser_kind (asn1_as_parser k)) payload #(pm *. sp) #w' (Ghost.hide (Ghost.reveal l <: VC.nlist (0 + SZ.v count) (asn1_t k)));
    fold (It.base_mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Serialized sp count payload) l);
    fold (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized sp count payload)) l);
    ml_match_eq d sp count payload pm l;
    rewrite (It.mixed_list_match_n (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v count) pm (ItT.Base (ItT.Serialized sp count payload)) l)
      as (PSO.ml_match0 d pm x l);
    fold (PSO.ml_match d pm x l);
  };
  fold (start_post k d pm x l res);
  res
}

(* The number of remaining elements *)

inline_for_extraction
fn length
  (#s: Ghost.erased (Set.set asn1_id_t)) (k: Ghost.erased (asn1_k s))
  (it: iter) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires iter_match k pm it l
returns res: SZ.t
ensures iter_match k pm it l ** pure (SZ.v res == List.Tot.length l)
{
  unfold (iter_match k pm it l);
  fold (iter_match k pm it l);
  it.count
}

inline_for_extraction
fn is_empty
  (#s: Ghost.erased (Set.set asn1_id_t)) (k: Ghost.erased (asn1_k s))
  (it: iter) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires iter_match k pm it l
returns res: bool
ensures iter_match k pm it l ** pure (res == Nil? l)
{
  unfold (iter_match k pm it l);
  fold (iter_match k pm it l);
  (it.count = 0sz)
}

(* Read the first element and advance the cursor. The element is related
   to the head of the list by `arel true d`; the trade gives the iterator
   back. *)

let next_post (#s: _) (k: asn1_k s) (#t: Type0) (d: adesc k t) (pi: R.ref iter) (pm: perm) (it: iter) (l: list (asn1_t k) { Cons? l }) (res: t) : slprop =
  exists* it' .
    R.pts_to pi it' **
    arel true d pm res (List.Tot.hd l) **
    iter_match k pm it' (List.Tot.tl l) **
    Trade.trade (arel true d pm res (List.Tot.hd l) ** iter_match k pm it' (List.Tot.tl l)) (iter_match k pm it l)

inline_for_extraction
fn next
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (pk: aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k))
  (pi: R.ref iter) (#it: Ghost.erased iter) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)) { Cons? (Ghost.reveal l) })
requires R.pts_to pi it ** iter_match k pm it l
returns res: t
ensures next_post k d pi pm it l res
{
  let i = !pi;
  unfold (iter_match k pm it l);
  with w . assert (S.pts_to it.payload #pm w);
  rewrite (S.pts_to it.payload #pm w) as (S.pts_to i.payload #pm w);
  next_prop k (SZ.v i.count) w l;
  S.pts_to_len i.payload;
  let c = WC.jump_k k i.payload 0sz;
  let sp = S.split i.payload c;
  match sp {
    Mktuple2 hs ts -> {
      let x = pk hs #pm #(Seq.slice w 0 (SZ.v c)) #(List.Tot.hd l);
      let i' : iter = { count = SZ.sub i.count 1sz; payload = ts };
      pi := i';
      rewrite (S.pts_to ts #pm (Seq.slice w (SZ.v c) (Seq.length w))) as (S.pts_to i'.payload #pm (Seq.slice w (SZ.v c) (Seq.length w)));
      fold (iter_match k pm i' (List.Tot.tl l));
      intro_trade (arel true d pm x (List.Tot.hd l) ** iter_match k pm i' (List.Tot.tl l)) (iter_match k pm it l)
        (S.is_split i.payload hs ts ** Trade.trade (arel true d pm x (List.Tot.hd l)) (S.pts_to hs #pm (Seq.slice w 0 (SZ.v c)))) fn _ {
        Trade.elim (arel true d pm x (List.Tot.hd l)) (S.pts_to hs #pm (Seq.slice w 0 (SZ.v c)));
        unfold (iter_match k pm i' (List.Tot.tl l));
        with wt . assert (S.pts_to i'.payload #pm wt);
        rewrite (S.pts_to i'.payload #pm wt) as (S.pts_to ts #pm wt);
        S.join hs ts i.payload;
        cons_prop k (SZ.v i'.count) (Seq.slice w 0 (SZ.v c)) wt (List.Tot.hd l) (List.Tot.tl l);
        rewrite (S.pts_to i.payload #pm (Seq.append (Seq.slice w 0 (SZ.v c)) wt))
          as (S.pts_to it.payload #pm (Seq.append (Seq.slice w 0 (SZ.v c)) wt));
        fold (iter_match k pm it l);
      };
      fold (next_post k d pi pm it l x);
      x
    }
  }
}

(* The types of the extraction roots (see ASN1.Pulse.ParseTest, and the
   iterators generated by everparse-asn1) *)

inline_for_extraction
let start_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (x: ml t) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt iter (PSO.ml_match d pm x l) (fun res -> start_post k d pm x l res)

inline_for_extraction
let length_t (#s: _) (k: asn1_k s) : Type =
  (it: iter) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt SZ.t (iter_match k pm it l) (fun res -> iter_match k pm it l ** pure (SZ.v res == List.Tot.length l))

inline_for_extraction
let is_empty_t (#s: _) (k: asn1_k s) : Type =
  (it: iter) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt bool (iter_match k pm it l) (fun res -> iter_match k pm it l ** pure (res == Nil? l))

inline_for_extraction
let next_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (pi: R.ref iter) -> (#it: Ghost.erased iter) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k)) { Cons? (Ghost.reveal l) }) ->
  stt t (R.pts_to pi it ** iter_match k pm it l) (fun res -> next_post k d pi pm it l res)
