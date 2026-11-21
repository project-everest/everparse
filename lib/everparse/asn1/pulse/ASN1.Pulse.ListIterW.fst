module ASN1.Pulse.ListIterW
#lang-pulse

(* Iterators over SEQUENCE OF / SET OF values in writer form.

   A list ready to be written (`crel false (CD_SEQUENCE_OF ne d)`) is a
   `mixed_list` whose nodes may be arrays of elements (`Slice`), serialized
   elements (`Serialized`, e.g. from a parsed value made writable with
   `RelKeep.to_writer`), or concatenations (`Append`). The iterator is the
   generic LowParse iterator over mixed lists, instantiated with the
   share/gather functions of `ASN1.Pulse.TypedShare`. When the next element
   is serialized, it is parsed (zero-copy) and made writable, so `next`
   always returns an element in `arel false d`.

   Elements are enumerated in list order (for SET OF, the writer sorts
   them when serializing). This module also provides builders for these
   lists. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module SM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module It = LowParse.PulseParse.Iterator
module ItT = LowParse.PulseParse.Iterator.Type
module LPB = LowParse.PulseParse.Base
module WC = ASN1.Pulse.WriteComb
module RK = ASN1.Pulse.RelKeep
module TS = ASN1.Pulse.TypedShare
module PSO = ASN1.Pulse.ParseSeqOf

(* The list relation (`crel false` of a SEQUENCE OF / SET OF, up to the
   list view of the value; see `RawVConv.tcontent_seq_of_eq`) *)

let wml_match (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (l: list (asn1_t k)) : slprop =
  It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l

(* The iterator does not depend on the element type of the descriptor, but
   on its implementation type *)

let witer (t: Type0) : Type0 = ItT.iterator SZ.t t

let witer_match (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (it: witer t) (l: list (asn1_t k)) : slprop =
  It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l

(* Start iterating *)

let start_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (l: list (asn1_t k)) (res: witer t) : slprop =
  exists* pm' . witer_match d pm' res l ** Trade.trade (witer_match d pm' res l) (wml_match d pm x l)

inline_for_extraction
fn start
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (x: ml t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires wml_match d pm x l
returns res: witer t
ensures start_post d pm x l res
{
  unfold (wml_match d pm x l);
  let res = It.iterator_start (arel false d) ml_ops #(Ghost.hide asn1_strong_parser_kind) (asn1_as_parser k) (WC.jump_k k) pm x l (TS.share_d d) (TS.gather_d d);
  with pm' . assert (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' res l);
  rewrite (Trade.trade (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' res l)
             (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l))
    as (Trade.trade (witer_match d pm' res l) (wml_match d pm x l));
  fold (witer_match d pm' res l);
  fold (start_post d pm x l res);
  res
}

(* Emptiness test: by the invariant of `iterator_match`, the iterator is
   empty iff its first node is empty *)

inline_for_extraction
let first_length (#t: Type0) (it: witer t) : Tot SZ.t =
  match it with
  | ItT.IBase b -> ItT.base_mixed_list_length ml_ops b
  | ItT.IPair b _ -> ItT.base_mixed_list_length ml_ops b

ghost
fn first_length_prop
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (it: witer t) (pm: perm) (l: list (asn1_t k))
requires witer_match d pm it l
ensures witer_match d pm it l ** pure (SZ.v (first_length it) == 0 <==> Nil? l)
{
  unfold (witer_match d pm it l);
  match it {
    ItT.IBase b -> {
      unfold (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.IBase #SZ.t #t b) l);
      It.base_mixed_list_match_length (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm b l;
      fold (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.IBase #SZ.t #t b) l);
      fold (witer_match d pm it l);
    }
    ItT.IPair b m -> {
      unfold (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.IPair #SZ.t #t b m) l);
      with l1 l2 . assert (
        It.base_mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm b l1 **
        It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm m l2);
      It.base_mixed_list_match_length (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm b l1;
      It.mixed_list_match_length (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm m l2;
      List.Tot.Properties.append_length l1 l2;
      fold (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.IPair #SZ.t #t b m) l);
      fold (witer_match d pm it l);
    }
  }
}

inline_for_extraction
fn is_empty
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (it: witer t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires witer_match d pm it l
returns res: bool
ensures witer_match d pm it l ** pure (res == Nil? l)
{
  first_length_prop d it pm l;
  (first_length it = 0sz)
}

(* Read the first element and advance the iterator. A serialized element
   is parsed with `pk`, then made writable. *)

let next_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pi: R.ref (witer t)) (pm: perm) (it: witer t) (l: list (asn1_t k) { Cons? l }) (res: t) : slprop =
  exists* pm_v it' pm' .
    R.pts_to pi it' **
    arel false d pm_v res (List.Tot.hd l) **
    witer_match d pm' it' (List.Tot.tl l) **
    Trade.trade (arel false d pm_v res (List.Tot.hd l) ** witer_match d pm' it' (List.Tot.tl l)) (witer_match d pm it l)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn next
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (pk: aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k))
  (pi: R.ref (witer t)) (#it: Ghost.erased (witer t)) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)) { Cons? (Ghost.reveal l) })
requires R.pts_to pi it ** witer_match d pm it l
returns res: t
ensures next_post d pi pm it l res
{
  unfold (witer_match d pm it l);
  let xe = It.iterator_next_eos (arel false d) ml_ops #(Ghost.hide asn1_strong_parser_kind) (asn1_as_parser k) (WC.jump_k k) pm pi it l (TS.share_d d) (TS.gather_d d);
  unfold (It.iterator_next_eos_post (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm pi it l xe);
  with pm_v y tl it' pm' . assert (
    It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe y **
    R.pts_to pi it' **
    It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' tl);
  rewrite each tl as (List.Tot.tl l);
  rewrite each y as (List.Tot.hd l);
  match xe {
    It.EElement x -> {
      rewrite (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l))
        as (arel false d pm_v x (List.Tot.hd l));
      intro_trade (arel false d pm_v x (List.Tot.hd l) ** It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l)) (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l)
        (Trade.trade
          (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l) **
           It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l))
          (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l)) fn _ {
        rewrite (arel false d pm_v x (List.Tot.hd l))
          as (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l));
        Trade.elim
          (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l) **
           It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l))
          (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l);
      };
      rewrite (Trade.trade (arel false d pm_v x (List.Tot.hd l) ** It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l)) (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l))
        as (Trade.trade (arel false d pm_v x (List.Tot.hd l) ** witer_match d pm' it' (List.Tot.tl l)) (witer_match d pm it l));
      fold (witer_match d pm' it' (List.Tot.tl l));
      fold (next_post d pi pm it l x);
      x
    }
    It.ESerialized pl -> {
      rewrite (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l))
        as (LPB.pts_to_parsed #asn1_strong_parser_kind (asn1_as_parser k) pl #pm_v (List.Tot.hd l));
      unfold (LPB.pts_to_parsed #asn1_strong_parser_kind (asn1_as_parser k) pl #pm_v (List.Tot.hd l));
      with w . assert (S.pts_to pl #pm_v w);
      let x = pk pl #pm_v #w #(List.Tot.hd l);
      RK.to_writer d pm_v x (List.Tot.hd l);
      Trade.trans (arel false d pm_v x (List.Tot.hd l)) (arel true d pm_v x (List.Tot.hd l)) (S.pts_to pl #pm_v w);
      intro_trade (arel false d pm_v x (List.Tot.hd l) ** It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l)) (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l)
        (Trade.trade (arel false d pm_v x (List.Tot.hd l)) (S.pts_to pl #pm_v w) **
         Trade.trade
          (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l) **
           It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l))
          (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l) **
         pure (LPB.pts_to_parsed_prop #asn1_strong_parser_kind (asn1_as_parser k) w (List.Tot.hd l))) fn _ {
        Trade.elim (arel false d pm_v x (List.Tot.hd l)) (S.pts_to pl #pm_v w);
        fold (LPB.pts_to_parsed #asn1_strong_parser_kind (asn1_as_parser k) pl #pm_v (List.Tot.hd l));
        rewrite (LPB.pts_to_parsed #asn1_strong_parser_kind (asn1_as_parser k) pl #pm_v (List.Tot.hd l))
          as (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l));
        Trade.elim
          (It.elt_or_serialized_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm_v xe (List.Tot.hd l) **
           It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l))
          (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l);
      };
      rewrite (Trade.trade (arel false d pm_v x (List.Tot.hd l) ** It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm' it' (List.Tot.tl l)) (It.iterator_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm it l))
        as (Trade.trade (arel false d pm_v x (List.Tot.hd l) ** witer_match d pm' it' (List.Tot.tl l)) (witer_match d pm it l));
      fold (witer_match d pm' it' (List.Tot.tl l));
      fold (next_post d pi pm it l x);
      x
    }
  }
}

#pop-options

(* Builders *)

inline_for_extraction
fn empty
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (_: unit)
requires emp
returns res: ml t
ensures wml_match d 1.0R res []
{
  let res : ml t = ItT.Base (ItT.Empty #SZ.t #t);
  fold (It.base_mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 0 1.0R (ItT.Empty #SZ.t #t) []);
  rewrite (It.base_mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 0 1.0R (ItT.Empty #SZ.t #t) [])
    as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops res)) 1.0R res []);
  fold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 1.0R res []);
  fold (wml_match d 1.0R res []);
  res
}

(* An array of elements, each in `arel false d` *)

let of_slice_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (a: S.slice t) (pm: perm) (va: Seq.seq t) (l: list (asn1_t k)) (res: ml t) : slprop =
  wml_match d 1.0R res l **
  Trade.trade (wml_match d 1.0R res l) (exists* va' . S.pts_to a #pm va' ** SM.seq_list_match va' l (arel false d pm))

#push-options "--z3rlimit 32"

inline_for_extraction
fn of_slice
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (a: S.slice t) (#pm: perm) (#va: Ghost.erased (Seq.seq t)) (#l: Ghost.erased (list (asn1_t k)))
requires S.pts_to a #pm va ** SM.seq_list_match va l (arel false d pm)
returns res: ml t
ensures of_slice_post d a pm va l res
{
  S.pts_to_len a;
  let n = S.len a;
  let res : ml t = ItT.Base (ItT.Slice pm pm a n);
  assert (pure (Seq.equal (Seq.slice va 0 (0 + SZ.v n)) va));
  rewrite (S.pts_to a #pm va) as (S.pts_to a #(1.0R *. pm) va);
  rewrite (SM.seq_list_match va l (arel false d pm))
    as (SM.seq_list_match (Seq.slice va 0 (0 + SZ.v n)) l (arel false d (1.0R *. pm)));
  fold (It.base_mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v n) 1.0R (ItT.Slice pm pm a n) l);
  rewrite (It.base_mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v n) 1.0R (ItT.Slice pm pm a n) l)
    as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops res)) 1.0R res l);
  fold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 1.0R res l);
  fold (wml_match d 1.0R res l);
  intro_trade (wml_match d 1.0R res l) (exists* va' . S.pts_to a #pm va' ** SM.seq_list_match va' l (arel false d pm)) emp fn _ {
    unfold (wml_match d 1.0R res l);
    unfold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 1.0R res l);
    rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops res)) 1.0R res l)
      as (It.base_mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v n) 1.0R (ItT.Slice pm pm a n) l);
    unfold (It.base_mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v n) 1.0R (ItT.Slice pm pm a n) l);
    with va' l1 . assert (S.pts_to a #(1.0R *. pm) va' ** SM.seq_list_match l1 l (arel false d (1.0R *. pm)));
    S.pts_to_len a;
    assert (pure (Seq.equal (Seq.slice va' 0 (0 + SZ.v n)) va'));
    rewrite (S.pts_to a #(1.0R *. pm) va') as (S.pts_to a #pm va');
    rewrite (SM.seq_list_match l1 l (arel false d (1.0R *. pm))) as (SM.seq_list_match va' l (arel false d pm));
  };
  fold (of_slice_post d a pm va l res);
  res
}

#pop-options

(* The concatenation of two lists, given by references *)

let append_pre (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (rb: R.ref (ml t)) (pb: perm) (lb: list (asn1_t k)) (ra: R.ref (ml t)) (pa: perm) (la: list (asn1_t k)) (pm: perm) : slprop =
  exists* xb xa . R.pts_to rb #pb xb ** wml_match d pm xb lb ** R.pts_to ra #pa xa ** wml_match d pm xa la

let append_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (rb: R.ref (ml t)) (pb: perm) (lb: list (asn1_t k)) (ra: R.ref (ml t)) (pa: perm) (la: list (asn1_t k)) (pm: perm) (res: ml t) : slprop =
  wml_match d 1.0R res (List.Tot.append lb la) **
  Trade.trade (wml_match d 1.0R res (List.Tot.append lb la)) (append_pre d rb pb lb ra pa la pm)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn append
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (rb: R.ref (ml t)) (ra: R.ref (ml t))
  (#pb: perm) (#lb: Ghost.erased (list (asn1_t k))) (#pa: perm) (#la: Ghost.erased (list (asn1_t k))) (#pm: perm)
requires append_pre d rb pb lb ra pa la pm ** pure (SZ.fits (List.Tot.length lb + List.Tot.length la))
returns res: ml t
ensures append_post d rb pb lb ra pa la pm res
{
  unfold (append_pre d rb pb lb ra pa la pm);
  with xb xa . assert (R.pts_to rb #pb xb ** R.pts_to ra #pa xa);
  unfold (wml_match d pm xb lb);
  unfold (wml_match d pm xa la);
  It.mixed_list_match_length (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm xb lb;
  It.mixed_list_match_length (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm xa la;
  let vb = R.read rb;
  let va = R.read ra;
  let cb = ItT.mixed_list_length ml_ops vb;
  let ca = ItT.mixed_list_length ml_ops va;
  let tot = SZ.add cb ca;
  let depth : Ghost.erased nat = Ghost.hide (1 + (if It.mixed_list_depth xb < It.mixed_list_depth xa then It.mixed_list_depth xa else It.mixed_list_depth xb));
  let res : ml t = ItT.Append depth cb ca tot 0sz (pb /. 2.0R) rb 0sz (pa /. 2.0R) ra pm;
  List.Tot.Properties.append_length lb la;
  R.share rb;
  R.share ra;
  unfold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm xb lb);
  unfold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm xa la);
  rewrite (R.pts_to rb #(pb /. 2.0R) xb) as (R.pts_to rb #(1.0R *. (pb /. 2.0R)) xb);
  rewrite (R.pts_to ra #(pa /. 2.0R) xa) as (R.pts_to ra #(1.0R *. (pa /. 2.0R)) xa);
  rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops xb)) pm xb lb)
    as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (It.append_off_before 0 (ml_ops.v 0sz) (ml_ops.v cb)) (It.append_n_before 0 (SZ.v tot) (ml_ops.v cb)) (1.0R *. pm) xb lb);
  rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops xa)) pm xa la)
    as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (It.append_off_after 0 (ml_ops.v 0sz) (ml_ops.v cb)) (It.append_n_after 0 (SZ.v tot) (ml_ops.v cb)) (1.0R *. pm) xa la);
  fold (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v tot) 1.0R (ItT.Append depth cb ca tot 0sz (pb /. 2.0R) rb 0sz (pa /. 2.0R) ra pm) (List.Tot.append lb la));
  rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v tot) 1.0R (ItT.Append depth cb ca tot 0sz (pb /. 2.0R) rb 0sz (pa /. 2.0R) ra pm) (List.Tot.append lb la))
    as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops res)) 1.0R res (List.Tot.append lb la));
  fold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 1.0R res (List.Tot.append lb la));
  fold (wml_match d 1.0R res (List.Tot.append lb la));
  intro_trade (wml_match d 1.0R res (List.Tot.append lb la)) (append_pre d rb pb lb ra pa la pm)
    (R.pts_to rb #(pb /. 2.0R) xb ** R.pts_to ra #(pa /. 2.0R) xa) fn _ {
    unfold (wml_match d 1.0R res (List.Tot.append lb la));
    unfold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 1.0R res (List.Tot.append lb la));
    rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops res)) 1.0R res (List.Tot.append lb la))
      as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v tot) 1.0R (ItT.Append depth cb ca tot 0sz (pb /. 2.0R) rb 0sz (pa /. 2.0R) ra pm) (List.Tot.append lb la));
    unfold (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (SZ.v tot) 1.0R (ItT.Append depth cb ca tot 0sz (pb /. 2.0R) rb 0sz (pa /. 2.0R) ra pm) (List.Tot.append lb la));
    with ib ia l1 l2 . assert (R.pts_to rb #(1.0R *. (pb /. 2.0R)) ib ** R.pts_to ra #(1.0R *. (pa /. 2.0R)) ia **
      It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (It.append_off_before 0 (ml_ops.v 0sz) (ml_ops.v cb)) (It.append_n_before 0 (SZ.v tot) (ml_ops.v cb)) (1.0R *. pm) ib l1 **
      It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (It.append_off_after 0 (ml_ops.v 0sz) (ml_ops.v cb)) (It.append_n_after 0 (SZ.v tot) (ml_ops.v cb)) (1.0R *. pm) ia l2);
    List.Tot.Properties.append_length_inv_head l1 l2 lb la;
    rewrite (R.pts_to rb #(1.0R *. (pb /. 2.0R)) ib) as (R.pts_to rb #(pb /. 2.0R) ib);
    rewrite (R.pts_to ra #(1.0R *. (pa /. 2.0R)) ia) as (R.pts_to ra #(pa /. 2.0R) ia);
    R.gather rb #xb #ib;
    R.gather ra #xa #ia;
    rewrite (R.pts_to rb #(pb /. 2.0R +. pb /. 2.0R) xb) as (R.pts_to rb #pb xb);
    rewrite (R.pts_to ra #(pa /. 2.0R +. pa /. 2.0R) xa) as (R.pts_to ra #pa xa);
    rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (It.append_off_before 0 (ml_ops.v 0sz) (ml_ops.v cb)) (It.append_n_before 0 (SZ.v tot) (ml_ops.v cb)) (1.0R *. pm) ib l1)
      as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops xb)) pm xb lb);
    rewrite (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (It.append_off_after 0 (ml_ops.v 0sz) (ml_ops.v cb)) (It.append_n_after 0 (SZ.v tot) (ml_ops.v cb)) (1.0R *. pm) ia l2)
      as (It.mixed_list_match_n (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) 0 (ml_ops.v (ItT.mixed_list_length ml_ops xa)) pm xa la);
    fold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm xb lb);
    fold (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm xa la);
    fold (wml_match d pm xb lb);
    fold (wml_match d pm xa la);
    fold (append_pre d rb pb lb ra pa la pm);
  };
  fold (append_post d rb pb lb ra pa la pm res);
  res
}

#pop-options

(* The types of the extraction roots (see ASN1.Pulse.ParseTest, and the
   iterators generated by everparse-asn1) *)

inline_for_extraction
let start_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (x: ml t) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt (ItT.iterator SZ.t t) (wml_match d pm x l) (fun res -> start_post d pm x l res)

inline_for_extraction
let is_empty_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (it: witer t) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt bool (witer_match d pm it l) (fun res -> witer_match d pm it l ** pure (res == Nil? l))

inline_for_extraction
let next_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (pi: R.ref (witer t)) -> (#it: Ghost.erased (witer t)) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k)) { Cons? (Ghost.reveal l) }) ->
  stt t (R.pts_to pi it ** witer_match d pm it l) (fun res -> next_post d pi pm it l res)

inline_for_extraction
let empty_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  unit -> stt (ItT.mixed_list SZ.t t) emp (fun res -> wml_match d 1.0R res [])

inline_for_extraction
let of_slice_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (a: S.slice t) -> (#pm: perm) -> (#va: Ghost.erased (Seq.seq t)) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt (ItT.mixed_list SZ.t t) (S.pts_to a #pm va ** SM.seq_list_match va l (arel false d pm)) (fun res -> of_slice_post d a pm va l res)

inline_for_extraction
let append_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (rb: R.ref (ml t)) -> (ra: R.ref (ml t)) ->
  (#pb: perm) -> (#lb: Ghost.erased (list (asn1_t k))) -> (#pa: perm) -> (#la: Ghost.erased (list (asn1_t k))) -> (#pm: perm) ->
  stt (ItT.mixed_list SZ.t t) (append_pre d rb pb lb ra pa la pm ** pure (SZ.fits (List.Tot.length lb + List.Tot.length la))) (fun res -> append_post d rb pb lb ra pa la pm res)

(* Parsed lists (`arel true`, always serialized) are lists in writer form
   as they are: a serialized node does not depend on the element relation *)

let serialized_match_eq (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (sp: perm) (count: SZ.t) (input: S.slice U8.t) (pm: perm) (l: list (asn1_t k))
: Lemma (It.mixed_list_match (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.Base (ItT.Serialized sp count input)) l ==
    It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.Base (ItT.Serialized sp count input)) l)
= assert (It.mixed_list_match (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.Base (ItT.Serialized sp count input)) l ==
    It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm (ItT.Base (ItT.Serialized sp count input)) l)
    by (FStar.Tactics.V2.norm [delta_only [`%It.mixed_list_match; `%It.mixed_list_match_n; `%It.base_mixed_list_match_n]; iota; zeta]; FStar.Tactics.V2.trefl ())

ghost
fn of_parsed
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (x: ml t) (pm: perm) (l: list (asn1_t k))
requires PSO.ml_match d pm x l
ensures wml_match d pm x l ** Trade.trade (wml_match d pm x l) (PSO.ml_match d pm x l)
{
  unfold (PSO.ml_match d pm x l);
  unfold (PSO.ml_match0 d pm x l);
  let b = ItT.Base?._0 x;
  serialized_match_eq d (ItT.Serialized?.sp b) (ItT.Serialized?.count b) (ItT.Serialized?.payload b) pm l;
  rewrite (It.mixed_list_match (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l)
    as (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l);
  fold (wml_match d pm x l);
  intro_trade (wml_match d pm x l) (PSO.ml_match d pm x l) emp fn _ {
    unfold (wml_match d pm x l);
    rewrite (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l)
      as (It.mixed_list_match (arel true d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l);
    fold (PSO.ml_match0 d pm x l);
    fold (PSO.ml_match d pm x l);
  };
}

(* The number of elements of a list, in O(1) *)

inline_for_extraction
fn length
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (x: ml t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires wml_match d pm x l
returns res: SZ.t
ensures wml_match d pm x l ** pure (SZ.v res == List.Tot.length l)
{
  unfold (wml_match d pm x l);
  It.mixed_list_match_length (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm x l;
  fold (wml_match d pm x l);
  ItT.mixed_list_length ml_ops x
}

(* Iterators with a nominal type `w` (one per list type, generated by
   everparse-asn1, for stable C names), and a total `next`: it returns false
   at the end of the list, otherwise true and the element in `*out` *)

let next_n_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (#w: Type0) (unwrap: w -> witer t)
  (pi: R.ref w) (out: R.ref t) (pm: perm) (it: w) (l: list (asn1_t k)) (res: bool) : slprop =
  if res
  then exists* x pm_v it' pm' hd tl .
    pure (l == hd :: tl) **
    R.pts_to pi it' ** R.pts_to out x **
    arel false d pm_v x hd **
    witer_match d pm' (unwrap it') tl **
    Trade.trade (arel false d pm_v x hd ** witer_match d pm' (unwrap it') tl) (witer_match d pm (unwrap it) l)
  else pure (l == []) ** R.pts_to pi it ** witer_match d pm (unwrap it) l ** (exists* v . R.pts_to out v)

let start_n_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (#w: Type0) (unwrap: w -> witer t) (pm: perm) (x: ml t) (l: list (asn1_t k)) (res: w) : slprop =
  exists* pm' . witer_match d pm' (unwrap res) l ** Trade.trade (witer_match d pm' (unwrap res) l) (wml_match d pm x l)

inline_for_extraction
fn start_n
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (#w: Type0) (wrap: witer t -> w) (unwrap: w -> witer t) (law: squash (forall (x: witer t) . unwrap (wrap x) == x))
  (x: ml t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires wml_match d pm x l
returns res: w
ensures start_n_post d unwrap pm x l res
{
  let it = start d x;
  unfold (start_post d pm x l it);
  with pm' . assert (witer_match d pm' it l);
  let res = wrap it;
  rewrite (witer_match d pm' it l ** Trade.trade (witer_match d pm' it l) (wml_match d pm x l))
    as (witer_match d pm' (unwrap res) l ** Trade.trade (witer_match d pm' (unwrap res) l) (wml_match d pm x l));
  fold (start_n_post d unwrap pm x l res);
  res
}

inline_for_extraction
fn is_empty_n
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (#w: Type0) (unwrap: w -> witer t)
  (it: w) (#pm: perm) (#l: Ghost.erased (list (asn1_t k)))
requires witer_match d pm (unwrap it) l
returns res: bool
ensures witer_match d pm (unwrap it) l ** pure (res == Nil? l)
{
  is_empty d (unwrap it)
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn next_n
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (pk: aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k))
  (#w: Type0) (wrap: witer t -> w) (unwrap: w -> witer t) (law: squash (forall (x: witer t) . unwrap (wrap x) == x))
  (pi: R.ref w) (out: R.ref t) (#it: Ghost.erased w) (#pm: perm) (#l: Ghost.erased (list (asn1_t k))) (#v: Ghost.erased t)
requires R.pts_to pi it ** witer_match d pm (unwrap it) l ** R.pts_to out v
returns res: bool
ensures next_n_post d unwrap pi out pm it l res
{
  let v = !pi;
  let e = is_empty d (unwrap v);
  if (e) {
    fold (next_n_post d unwrap pi out pm it l false);
    false
  } else {
    let mut r = unwrap v;
    let x = next d pk r #(Ghost.hide (unwrap v)) #pm #l;
    unfold (next_post d r pm (unwrap v) l x);
    with pm_v it' pm' . assert (R.pts_to r it' ** arel false d pm_v x (List.Tot.hd l) ** witer_match d pm' it' (List.Tot.tl l));
    let it2 = !r;
    pi := wrap it2;
    out := x;
    rewrite (witer_match d pm' it' (List.Tot.tl l) **
      Trade.trade (arel false d pm_v x (List.Tot.hd l) ** witer_match d pm' it' (List.Tot.tl l)) (witer_match d pm (unwrap v) l))
      as (witer_match d pm' (unwrap (wrap it2)) (List.Tot.tl l) **
      Trade.trade (arel false d pm_v x (List.Tot.hd l) ** witer_match d pm' (unwrap (wrap it2)) (List.Tot.tl l)) (witer_match d pm (unwrap it) l));
    fold (next_n_post d unwrap pi out pm it l true);
    true
  }
}

#pop-options

(* The i-th element of a list (O(i)), or false if there is none *)

let rec ldrop (#a: Type) (n: nat) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | _ :: q -> if n = 0 then l else ldrop (n - 1) q

let rec ldrop_cons (#a: Type) (n: nat) (l: list a)
: Lemma (requires n < List.Tot.length l)
  (ensures Cons? (ldrop n l) /\ List.Tot.tl (ldrop n l) == ldrop (n + 1) l /\ List.Tot.hd (ldrop n l) == List.Tot.index l n)
  (decreases l)
= match l with
  | _ :: q -> if n = 0 then () else ldrop_cons (n - 1) q

let get_post (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (x: ml t) (i: SZ.t) (out: R.ref t) (pm: perm) (l: list (asn1_t k)) (res: bool) : slprop =
  if res
  then exists* y pm_v hd .
    pure (SZ.v i < List.Tot.length l /\ Cons? (ldrop (SZ.v i) l) /\ hd == List.Tot.hd (ldrop (SZ.v i) l)) **
    R.pts_to out y ** arel false d pm_v y hd **
    Trade.trade (arel false d pm_v y hd) (wml_match d pm x l)
  else pure (SZ.v i >= List.Tot.length l) ** wml_match d pm x l ** (exists* v . R.pts_to out v)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn get
  (#s: Ghost.erased (Set.set asn1_id_t)) (#k: Ghost.erased (asn1_k s)) (#t: Type0) (d: Ghost.erased (adesc k t))
  (pk: aparser #t #(asn1_t k) (arel true d) #asn1_strong_parser_kind (asn1_as_parser k))
  (x: ml t) (i: SZ.t) (out: R.ref t) (#pm: perm) (#l: Ghost.erased (list (asn1_t k))) (#v: Ghost.erased t)
requires wml_match d pm x l ** R.pts_to out v
returns res: bool
ensures get_post d x i out pm l res
{
  let n = length d x;
  if (SZ.lt i n) {
    let it0 = start d x;
    unfold (start_post d pm x l it0);
    with pm0 . assert (witer_match d pm0 it0 l);
    let mut pi = it0;
    let mut pj = 0sz;
    rewrite (witer_match d pm0 it0 l ** Trade.trade (witer_match d pm0 it0 l) (wml_match d pm x l))
      as (witer_match d pm0 it0 (ldrop (SZ.v 0sz) l) ** Trade.trade (witer_match d pm0 it0 (ldrop (SZ.v 0sz) l)) (wml_match d pm x l));
    while (
      let j = !pj;
      SZ.lt j i
    ) invariant exists* j it pm' .
      R.pts_to pj j ** R.pts_to pi it **
      witer_match d pm' it (ldrop (SZ.v j) l) **
      Trade.trade (witer_match d pm' it (ldrop (SZ.v j) l)) (wml_match d pm x l) **
      pure (SZ.v j <= SZ.v i)
    decreases (SZ.v i - SZ.v (!pj))
    {
      let j = !pj;
      with it pm' . assert (R.pts_to pi it ** witer_match d pm' it (ldrop (SZ.v j) l));
      ldrop_cons (SZ.v j) l;
      let _ = next d pk pi #it #pm' #(Ghost.hide (ldrop (SZ.v j) l));
      unfold (next_post d pi pm' it (ldrop (SZ.v j) l) _);
      with pm_v y it' pm'' . assert (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v j) l)) ** R.pts_to pi it' ** witer_match d pm'' it' (List.Tot.tl (ldrop (SZ.v j) l)));
      rewrite each (List.Tot.tl (ldrop (SZ.v j) l)) as (ldrop (SZ.v (SZ.add j 1sz)) l);
      intro_trade (witer_match d pm'' it' (ldrop (SZ.v (SZ.add j 1sz)) l)) (wml_match d pm x l)
        (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v j) l)) **
         Trade.trade (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v j) l)) ** witer_match d pm'' it' (ldrop (SZ.v (SZ.add j 1sz)) l)) (witer_match d pm' it (ldrop (SZ.v j) l)) **
         Trade.trade (witer_match d pm' it (ldrop (SZ.v j) l)) (wml_match d pm x l)) fn _ {
        Trade.elim (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v j) l)) ** witer_match d pm'' it' (ldrop (SZ.v (SZ.add j 1sz)) l)) (witer_match d pm' it (ldrop (SZ.v j) l));
        Trade.elim (witer_match d pm' it (ldrop (SZ.v j) l)) (wml_match d pm x l);
      };
      pj := SZ.add j 1sz;
    };
    let j = !pj;
    with it pm' . assert (R.pts_to pi it ** witer_match d pm' it (ldrop (SZ.v j) l));
    rewrite each (SZ.v j) as (SZ.v i);
    ldrop_cons (SZ.v i) l;
    let y = next d pk pi #it #pm' #(Ghost.hide (ldrop (SZ.v i) l));
    unfold (next_post d pi pm' it (ldrop (SZ.v i) l) y);
    with pm_v it' pm'' . assert (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v i) l)) ** witer_match d pm'' it' (List.Tot.tl (ldrop (SZ.v i) l)));
    out := y;
    intro_trade (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v i) l))) (wml_match d pm x l)
      (witer_match d pm'' it' (List.Tot.tl (ldrop (SZ.v i) l)) **
       Trade.trade (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v i) l)) ** witer_match d pm'' it' (List.Tot.tl (ldrop (SZ.v i) l))) (witer_match d pm' it (ldrop (SZ.v i) l)) **
       Trade.trade (witer_match d pm' it (ldrop (SZ.v i) l)) (wml_match d pm x l)) fn _ {
      Trade.elim (arel false d pm_v y (List.Tot.hd (ldrop (SZ.v i) l)) ** witer_match d pm'' it' (List.Tot.tl (ldrop (SZ.v i) l))) (witer_match d pm' it (ldrop (SZ.v i) l));
      Trade.elim (witer_match d pm' it (ldrop (SZ.v i) l)) (wml_match d pm x l);
    };
    fold (get_post d x i out pm l true);
    true
  } else {
    fold (get_post d x i out pm l false);
    false
  }
}

#pop-options

(* The types of the extraction roots of the nominal API *)

inline_for_extraction
let length_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (x: ml t) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt SZ.t (wml_match d pm x l) (fun res -> wml_match d pm x l ** pure (SZ.v res == List.Tot.length l))

inline_for_extraction
let get_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  (x: ml t) -> (i: SZ.t) -> (out: R.ref t) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) -> (#v: Ghost.erased t) ->
  stt bool (wml_match d pm x l ** R.pts_to out v) (fun res -> get_post d x i out pm l res)

inline_for_extraction
let start_n_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (w: Type0) (unwrap: w -> witer t) : Type =
  (x: ml t) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt w (wml_match d pm x l) (fun res -> start_n_post d unwrap pm x l res)

inline_for_extraction
let is_empty_n_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (w: Type0) (unwrap: w -> witer t) : Type =
  (it: w) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) ->
  stt bool (witer_match d pm (unwrap it) l) (fun res -> witer_match d pm (unwrap it) l ** pure (res == Nil? l))

inline_for_extraction
let next_n_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (w: Type0) (unwrap: w -> witer t) : Type =
  (pi: R.ref w) -> (out: R.ref t) -> (#it: Ghost.erased w) -> (#pm: perm) -> (#l: Ghost.erased (list (asn1_t k))) -> (#v: Ghost.erased t) ->
  stt bool (R.pts_to pi it ** witer_match d pm (unwrap it) l ** R.pts_to out v) (fun res -> next_n_post d unwrap pi out pm it l res)
