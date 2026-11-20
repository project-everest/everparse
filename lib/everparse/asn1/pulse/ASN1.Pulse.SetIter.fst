module ASN1.Pulse.SetIter
#lang-pulse

(* Lazy iterators over the components of a SET { ... }.

   As for SEQUENCE (ASN1.Pulse.SeqIter), starting from a validated SET, an
   iterator is a cursor over the remaining contents; `next` reads the
   identifier of the next TLV, finds the component it belongs to (by tag,
   as ASN1.Pulse.ParseSetAny does) and returns the component index and the
   slice of its TLV, without parsing it. Components come in their encoding
   order (the canonical order of their tags in DER), absent OPTIONAL and
   DEFAULT components being skipped. Items are those of
   ASN1.Pulse.SeqIter, so they are parsed by `ASN1.Pulse.SeqIter.get`.

   The iterator invariant is that of ASN1.Pulse.ParseSetAny: the remaining
   bytes are a suffix of the elements of the SET, none of whose components
   has been read yet. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.ParseSequence

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
module L = ASN1.Pulse.ParseSequence.Lemmas
module In = ASN1.Pulse.Interpreter
module SC = ASN1.Pulse.SetComp
module SA = ASN1.Pulse.ParseSetAny.Lemmas
module SI = ASN1.Pulse.SeqIter

(* The iterator state: `wr` is the rest of the contents *)

let set_rest (#i: _) (ls: asn1_gen_items_l i) (v: asn1_sequence_t_core ls) (wr: SB.bytes) : prop =
  exists (w: SB.bytes) (st: SA.opt_tuple ls) . SA.full ls w v /\ SA.inv ls w wr st

(* Marking the component of an identifier as read *)

let rec mark (#i: _) (ls: asn1_gen_items_l i) (st: SA.opt_tuple ls) (id: asn1_id_t) : Tot (SA.opt_tuple ls) (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> st
  | ASN1_GEN_ITEMS_CONS s _ dk _ tl ->
    if Set.mem id s
    then SA.scons dk tl (Some ()) (SA.ssnd dk tl st)
    else SA.scons dk tl (SA.sfst dk tl st) (mark tl (SA.ssnd dk tl st) id)

let rec mark_is_some (#i: _) (ls: asn1_gen_items_l i) (st: SA.opt_tuple ls) (id: asn1_id_t)
: Lemma
  (ensures (forall (c: nat) . SA.is_some ls (mark ls st id) c ==
    (SA.is_some ls st c || SC.comp_of_id (In.twins_of ls) id = Some c)))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s _ dk _ tl ->
    if Set.mem id s
    then SA.is_some_fill dk tl st id
    else begin
      mark_is_some tl (SA.ssnd dk tl st) id;
      SA.is_some_pass dk tl st (mark tl (SA.ssnd dk tl st) id) id
    end

(* The TLV dispatched to a component is that of its value *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec dpre_item_ok (#i: _) (ls: asn1_gen_items_l i) (id: asn1_id_t) (we: SB.bytes) (st: SA.opt_tuple ls) (v: asn1_sequence_t_core ls)
: Lemma
  (requires SA.dpre ls id we st v)
  (ensures (match SC.comp_of_id (In.twins_of ls) id with
    | Some c -> SI.item_ok ls c we v
    | None -> False))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL ->
    In.comp_of_id_cons ls id
  | ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    let tl = ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2 in
    In.comp_of_id_cons ls id;
    if Set.mem id s then ()
    else dpre_item_ok tl id we (SA.ssnd dk tl st) (SA.vtl dk tl v)
#pop-options

(* Start *)

let start_lemma (#ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids)) (w: SB.bytes) (v: asn1_content_t (ASN1_SET ids items pf))
: Lemma
  (requires parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf)) w v)
  (ensures set_rest items v w)
= SA.init items pf w v;
  let v' : asn1_sequence_t_core items = v in
  introduce exists (w0: SB.bytes) (st: SA.opt_tuple items) . SA.full items w0 v' /\ SA.inv items w0 w st
  with w (SA.none_tuple items)
  and ()

(* One step *)

let next_ok (#i: _) (ls: asn1_gen_items_l i) (v: asn1_sequence_t_core ls) (wr: SB.bytes) : prop =
  match SB.parse parse_asn1_identifier_U32 wr with
  | None -> False
  | Some (id, _) ->
    match SC.comp_of_id (In.twins_of ls) id with
    | None -> False
    | Some c ->
      match L.tlv_size wr with
      | None -> False
      | Some n -> 0 < n /\ n <= Seq.length wr /\
        SI.item_ok ls c (Seq.slice wr 0 n) v /\ set_rest ls v (Seq.slice wr n (Seq.length wr))

#push-options "--z3rlimit 64"
let next_lemma (#i: _) (ls: asn1_gen_items_l i) (v: asn1_sequence_t_core ls) (wr: SB.bytes)
: Lemma
  (requires set_rest ls v wr /\ Seq.length wr > 0)
  (ensures next_ok ls v wr)
= eliminate exists (w: SB.bytes) (st: SA.opt_tuple ls) . SA.full ls w v /\ SA.inv ls w wr st
  with begin
    SA.step_pre ls w wr st v;
    let Some (id, _) = SB.parse parse_asn1_identifier_U32 wr in
    let Some n = L.tlv_size wr in
    dpre_item_ok ls id (Seq.slice wr 0 n) st v;
    let st' = mark ls st id in
    mark_is_some ls st id;
    SA.step_post ls w wr st st' v;
    let wr' = Seq.slice wr n (Seq.length wr) in
    introduce exists (w0: SB.bytes) (st0: SA.opt_tuple ls) . SA.full ls w0 v /\ SA.inv ls w0 wr' st0
    with w st'
    and ()
  end
#pop-options

(* Finding the component of an identifier, at run time *)

inline_for_extraction
let comp_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (id: asn1_id_t) -> Tot (r: U32.t { match SC.comp_of_id (In.twins_of ls) id with Some c -> U32.v r == c | None -> True })

inline_for_extraction
let comp (#i: _) (ls: asn1_gen_items_l i) (u: squash (In.supported_items ls /\ In.items_len ls <= 64)) : Tot (comp_t ls) =
  fun id -> match In.set_comp ls () 0ul id with
  | Some r -> r
  | None -> 0ul

(* Iterators *)

let iter_match (#i: _) (ls: asn1_gen_items_l i) (pm: perm) (it: SI.seq_iter) (v: asn1_sequence_t_core ls) (w: SB.bytes) : slprop =
  S.pts_to it.SI.rest #pm w ** pure (set_rest ls v w)

let set_k (id: asn1_id_t) (#ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids)) : asn1_k (Set.singleton id) =
  ASN1_ILC id (ASN1_SET ids items pf)

let start_post (#ids: id_decs) (items: asn1_gen_items_l ids) (input: S.slice U8.t) (pm: perm) (w: SB.bytes) (v: asn1_sequence_t_core items) (res: SI.seq_iter) : slprop =
  exists* wc . iter_match items pm res v wc ** Trade.trade (iter_match items pm res v wc) (S.pts_to input #pm w)

inline_for_extraction
fn start
  (id: Ghost.erased asn1_id_t) (#ids: Ghost.erased id_decs) (items: Ghost.erased (asn1_gen_items_l ids)) (pf: squash (asn1_set_k_wf ids))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core items))
requires S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind (asn1_as_parser (set_k id items pf)) w v)
returns res: SI.seq_iter
ensures start_post items input pm w v res
{
  let c = ilc_content id #(ASN1_SET ids items pf) (asn1_content_as_parser (ASN1_SET ids items pf)) input #pm #w #v;
  with wc . assert (S.pts_to c #pm wc);
  start_lemma items pf wc v;
  let res : SI.seq_iter = { SI.rest = c; idx = 0ul };
  rewrite (S.pts_to c #pm wc) as (S.pts_to res.SI.rest #pm wc);
  fold (iter_match items pm res v wc);
  intro_trade (iter_match items pm res v wc) (S.pts_to input #pm w) (Trade.trade (S.pts_to c #pm wc) (S.pts_to input #pm w)) fn _ {
    unfold (iter_match items pm res v wc);
    rewrite (S.pts_to res.SI.rest #pm wc) as (S.pts_to c #pm wc);
    Trade.elim (S.pts_to c #pm wc) (S.pts_to input #pm w);
  };
  fold (start_post items input pm w v res);
  res
}

inline_for_extraction
fn is_empty
  (#i: Ghost.erased id_decs) (ls: Ghost.erased (asn1_gen_items_l i))
  (it: SI.seq_iter) (#pm: perm) (#v: Ghost.erased (asn1_sequence_t_core ls)) (#w: Ghost.erased SB.bytes)
requires iter_match ls pm it v w
returns res: bool
ensures iter_match ls pm it v w ** pure (res == (Seq.length w = 0))
{
  unfold (iter_match ls pm it v w);
  S.pts_to_len it.SI.rest;
  let res = SZ.eq (S.len it.SI.rest) 0sz;
  fold (iter_match ls pm it v w);
  res
}

(* Read the next component and advance the cursor *)

let next_post (#i: _) (ls: asn1_gen_items_l i) (pi: R.ref SI.seq_iter) (pm: perm) (it: SI.seq_iter) (v: asn1_sequence_t_core ls) (w: SB.bytes) (res: SI.seq_item) : slprop =
  exists* it' wi w' .
    R.pts_to pi it' **
    SI.item_match ls pm res v wi **
    iter_match ls pm it' v w' **
    pure (Seq.length w' < Seq.length w) **
    Trade.trade (SI.item_match ls pm res v wi ** iter_match ls pm it' v w') (iter_match ls pm it v w)

#push-options "--z3rlimit 64"

inline_for_extraction
fn next
  (#i: Ghost.erased id_decs) (ls: Ghost.erased (asn1_gen_items_l i))
  (fc: comp_t ls)
  (pi: R.ref SI.seq_iter) (#it: Ghost.erased SI.seq_iter) (#pm: perm) (#v: Ghost.erased (asn1_sequence_t_core ls)) (#w: Ghost.erased SB.bytes { Seq.length w > 0 })
requires R.pts_to pi it ** iter_match ls pm it v w
returns res: SI.seq_item
ensures next_post ls pi pm it v w res
{
  let it0 = !pi;
  unfold (iter_match ls pm it v w);
  rewrite (S.pts_to it.SI.rest #pm w) as (S.pts_to it0.SI.rest #pm w);
  next_lemma ls v w;
  L.identifier_nonempty w;
  S.pts_to_len it0.SI.rest;
  let mut poff = 0sz;
  let oid = I.vread_identifier it0.SI.rest poff;
  match oid {
    Some id -> {
      let c1 = !poff;
      let ol = ILC.vread_length it0.SI.rest poff;
      match ol {
        Some len -> {
          let off2 = !poff;
          tlv_size_eq w (SZ.v c1) (SZ.v off2 - SZ.v c1) len;
          SZ.fits_lte (SZ.v off2 + U32.v len) (Seq.length w);
          let sz = SZ.add off2 (SZ.uint32_to_sizet len);
          let j = fc id;
          let sp = SU.split_trade it0.SI.rest sz;
          match sp {
            Mktuple2 s1 s2 -> {
              let item : SI.seq_item = { SI.comp = j; bytes = s1 };
              let it' : SI.seq_iter = { SI.rest = s2; idx = 0ul };
              pi := it';
              let wi : Ghost.erased SB.bytes = Seq.slice w 0 (SZ.v sz);
              let w' : Ghost.erased SB.bytes = Seq.slice w (SZ.v sz) (Seq.length w);
              rewrite (S.pts_to s1 #pm (Seq.slice w 0 (SZ.v sz))) as (S.pts_to item.SI.bytes #pm wi);
              fold (SI.item_match ls pm item v wi);
              rewrite (S.pts_to s2 #pm (Seq.slice w (SZ.v sz) (Seq.length w))) as (S.pts_to it'.SI.rest #pm w');
              fold (iter_match ls pm it' v w');
              intro_trade (SI.item_match ls pm item v wi ** iter_match ls pm it' v w') (iter_match ls pm it v w)
                (Trade.trade (S.pts_to s1 #pm (Seq.slice w 0 (SZ.v sz)) ** S.pts_to s2 #pm (Seq.slice w (SZ.v sz) (Seq.length w))) (S.pts_to it0.SI.rest #pm w) **
                  pure (it0 == Ghost.reveal it /\ set_rest ls v w)) fn _ {
                unfold (SI.item_match ls pm item v wi);
                unfold (iter_match ls pm it' v w');
                rewrite (S.pts_to item.SI.bytes #pm wi) as (S.pts_to s1 #pm (Seq.slice w 0 (SZ.v sz)));
                rewrite (S.pts_to it'.SI.rest #pm w') as (S.pts_to s2 #pm (Seq.slice w (SZ.v sz) (Seq.length w)));
                Trade.elim _ (S.pts_to it0.SI.rest #pm w);
                rewrite (S.pts_to it0.SI.rest #pm w) as (S.pts_to it.SI.rest #pm w);
                fold (iter_match ls pm it v w);
              };
              fold (next_post ls pi pm it v w item);
              item
            }
          }
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

(* The types of the extraction roots; the components are read with
   ASN1.Pulse.SeqIter.get_t *)

inline_for_extraction
let start_t (id: asn1_id_t) (#ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids)) : Type =
  (input: S.slice U8.t) -> (#pm: perm) -> (#w: Ghost.erased SB.bytes) -> (#v: Ghost.erased (asn1_sequence_t_core items)) ->
  stt SI.seq_iter
    (S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind (asn1_as_parser (set_k id items pf)) w v))
    (fun res -> start_post items input pm w v res)

inline_for_extraction
let is_empty_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (it: SI.seq_iter) -> (#pm: perm) -> (#v: Ghost.erased (asn1_sequence_t_core ls)) -> (#w: Ghost.erased SB.bytes) ->
  stt bool (iter_match ls pm it v w) (fun res -> iter_match ls pm it v w ** pure (res == (Seq.length w = 0)))

inline_for_extraction
let next_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (pi: R.ref SI.seq_iter) -> (#it: Ghost.erased SI.seq_iter) -> (#pm: perm) -> (#v: Ghost.erased (asn1_sequence_t_core ls)) -> (#w: Ghost.erased SB.bytes { Seq.length w > 0 }) ->
  stt SI.seq_item (R.pts_to pi it ** iter_match ls pm it v w) (fun res -> next_post ls pi pm it v w res)
