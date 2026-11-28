module ASN1.Pulse.SeqIter
#lang-pulse

(* Lazy iterators over the components of a SEQUENCE { ... }.

   Starting from a validated SEQUENCE (its identifier, length and contents),
   an iterator is a cursor over the remaining contents together with the
   index of the next schema component that may be present. `next` reads the
   identifier of the next TLV, finds the first component (from the current
   index) it belongs to, skipping absent OPTIONAL / DEFAULT components, and
   returns the component index and the slice of its TLV, without parsing it.
   The bytes of a component can then be parsed (zero-copy) by `get`, with
   the parser of that component (e.g. `parse_dd dd`), which relates the
   result to the corresponding component of the SEQUENCE value. *)

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
module P = ASN1.Pulse.Parser

(* The cursor and the items it yields do not depend on the SEQUENCE type,
   so they have a single C type each. *)

noeq
type seq_iter = {
  rest: S.slice U8.t;
  idx: U32.t;
}

noeq
type seq_item = {
  comp: U32.t;
  bytes: S.slice U8.t;
}

(* Components *)

let rec ilen (#i: _) (ls: asn1_gen_items_l i) : Tot nat (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> 0
  | ASN1_GEN_ITEMS_CONS _ _ _ _ tl -> 1 + ilen tl

let item_t (it: asn1_gen_item_k) : Type =
  asn1_decorated_t_core (Mkdtuple3?._3 it)

let rec item_k (#i: _) (ls: asn1_gen_items_l i) (j: nat { j < ilen ls }) : Tot asn1_gen_item_k (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_CONS s d dk _ tl -> if j = 0 then (| s, d, dk |) else item_k tl (j - 1)

let as_cons2 (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
  (#i: _) (ls: asn1_gen_items_l i { i == (s, d) :: (s2, d2) :: ids2 /\ ls == ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) })
  (v: asn1_sequence_t_core ls)
: Tot (asn1_sequence_t_core (cons2 dk dk2 tl2))
= v

let as_single (#s: _) (#d: _) (dk: asn1_decorated_k s d)
  (#i: _) (ls: asn1_gen_items_l i { i == [(s, d)] /\ ls == ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL })
  (v: asn1_sequence_t_core ls)
: Tot (asn1_decorated_t_core dk)
= v

(* The value of the j-th component *)

let rec vitem (#i: _) (ls: asn1_gen_items_l i) (j: nat { j < ilen ls }) (v: asn1_sequence_t_core ls)
: Tot (item_t (item_k ls j)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL -> as_single dk ls v
  | ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    let v' = as_cons2 dk dk2 tl2 ls v in
    if j = 0 then vfst dk dk2 tl2 v'
    else vitem (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) (j - 1) (vsnd dk dk2 tl2 v')

(* The iterator state: `w` is the rest of the contents, from component `n` *)

let rec at_ok (#i: _) (ls: asn1_gen_items_l i) (n: nat) (w: SB.bytes) (v: asn1_sequence_t_core ls) : Tot prop (decreases ls) =
  if n = 0 then seq_parsed_core ls w v
  else match ls with
  | ASN1_GEN_ITEMS_NIL -> False
  | ASN1_GEN_ITEMS_CONS _ _ _ _ ASN1_GEN_ITEMS_NIL -> n == 1 /\ Seq.length w == 0
  | ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    at_ok (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) (n - 1) w (vsnd dk dk2 tl2 (as_cons2 dk dk2 tl2 ls v))

(* `w` is the TLV of the j-th component *)

let rec item_ok (#i: _) (ls: asn1_gen_items_l i) (j: nat) (w: SB.bytes) (v: asn1_sequence_t_core ls) : Tot prop (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> False
  | ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL -> j == 0 /\ item_parsed_core dk w (as_single dk ls v)
  | ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    let v' = as_cons2 dk dk2 tl2 ls v in
    if j = 0 then item_parsed_core dk w (vfst dk dk2 tl2 v')
    else item_ok (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) (j - 1) w (vsnd dk dk2 tl2 v')

(* The component of an identifier, from component n on: the last component
   is always present if there are bytes left *)

let rec find_comp (#i: _) (ls: asn1_gen_items_l i) (n: nat) (id: asn1_id_t) : Tot (option nat) (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> None
  | ASN1_GEN_ITEMS_CONS _ _ _ _ ASN1_GEN_ITEMS_NIL -> Some 0
  | ASN1_GEN_ITEMS_CONS s _ _ _ tl ->
    if n = 0 && Set.mem id s then Some 0
    else match find_comp tl (if n = 0 then 0 else n - 1) id with
    | None -> None
    | Some j -> Some (j + 1)

(* Lemmas *)

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let item_tlv_size (#s: _) (#d: _) (dk: asn1_decorated_k s d) (w: SB.bytes) (v: asn1_decorated_t_core dk)
: Lemma
  (requires item_parsed_core dk w v)
  (ensures L.tlv_size w == Some (Seq.length w))
= let _ = twin_d dk in
  L.dec_shaped dk;
  let hd = ASN1.Pulse.Interpreter.twin_of dk in
  match SB.parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    assert (L.lc_shaped (ASN1.Spec.Sequence.parse_asn1_sequence_item_twin hd id));
    ()
#pop-options

let next_ok (#i: _) (ls: asn1_gen_items_l i) (n: nat) (w: SB.bytes) (v: asn1_sequence_t_core ls) : prop =
  match SB.parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, _) ->
    match find_comp ls n id with
    | None -> False
    | Some j ->
      n <= j /\ j < ilen ls /\
      (match L.tlv_size w with
       | None -> False
       | Some sz -> sz <= Seq.length w /\ item_ok ls j (Seq.slice w 0 sz) v /\ at_ok ls (j + 1) (Seq.slice w sz (Seq.length w)) v)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec next_lemma (#i: _) (ls: asn1_gen_items_l i) (n: nat) (w: SB.bytes) (v: asn1_sequence_t_core ls)
: Lemma
  (requires at_ok ls n w v /\ Seq.length w > 0)
  (ensures next_ok ls n w v)
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> seq_nil_core w v
  | ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL ->
    if n = 0 then begin
      seq_single_core dk w (as_single dk ls v);
      item_tlv_size dk w (as_single dk ls v);
      Seq.slice_length w
    end
  | ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    let tl = ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2 in
    let v' = as_cons2 dk dk2 tl2 ls v in
    if n = 0 then begin
      seq_cons_core dk dk2 tl2 w v';
      match SB.parse parse_asn1_identifier_U32 w with
      | Some (id, _) ->
        if Set.mem id s then ()
        else next_lemma tl 0 w (vsnd dk dk2 tl2 v')
    end
    else next_lemma tl (n - 1) w (vsnd dk dk2 tl2 v')
#pop-options

let rec item_ok_at (#i: _) (ls: asn1_gen_items_l i) (j: nat) (w: SB.bytes) (v: asn1_sequence_t_core ls)
: Lemma
  (requires item_ok ls j w v)
  (ensures j < ilen ls /\ item_parsed_core (Mkdtuple3?._3 (item_k ls j)) w (vitem ls j v))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_CONS s d dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s d dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    if j = 0 then ()
    else item_ok_at (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) (j - 1) w (vsnd dk dk2 tl2 (as_cons2 dk dk2 tl2 ls v))

(* The value of the j-th component, at the type of its schema *)

let item_is (#i: _) (ls: asn1_gen_items_l i) (j: nat) (#s: _) (#d: _) (dk: asn1_decorated_k s d) : prop =
  j < ilen ls /\ item_k ls j == (| s, d, dk |)

let vitem_at (#i: _) (ls: asn1_gen_items_l i) (j: nat) (#s: _) (#d: _) (dk: asn1_decorated_k s d) (h: squash (item_is ls j dk)) (v: asn1_sequence_t_core ls)
: Tot (asn1_decorated_t_core dk)
= coerce_eq () (vitem ls j v)

(* Finding the component of an identifier, at run time. `j` is the index of
   the first component of `ls`, and `n` the index of the next component that
   may be present. *)

inline_for_extraction
let pick (b: bool) (j: U32.t) (r: U32.t) : Tot (o: U32.t { o == (if b then j else r) }) =
  if b then j else r

let comp_spec (#i: _) (ls: asn1_gen_items_l i) (j: nat) (n: nat) (id: asn1_id_t) (r: U32.t) : prop =
  U32.v r < 4294967295 /\
  (match find_comp ls (if n >= j then n - j else 0) id with
   | Some c -> U32.v r == j + c
   | None -> True)

[@@ASN1.Pulse.Interpreter.asn1_pulse_attr]
let rec seq_comp (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i)
  (j: U32.t { U32.v j + ilen ls < 4294967295 }) (n: U32.t) (id: asn1_id_t)
: Tot (r: U32.t { comp_spec ls (U32.v j) (U32.v n) id r })
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> j
  | ASN1_GEN_ITEMS_CONS _ _ _ _ ASN1_GEN_ITEMS_NIL -> j
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    pick (U32.lte n j && P.phas_id_dec dk id) j (seq_comp tl (U32.add j 1ul) n id)

inline_for_extraction
let comp_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (n: U32.t) -> (id: asn1_id_t) -> Tot (r: U32.t { comp_spec ls 0 (U32.v n) id r })

inline_for_extraction
let comp (#i: _) (ls: asn1_gen_items_l i) (u: squash (ilen ls < 4294967295)) : Tot (comp_t ls) =
  fun n id -> seq_comp ls 0ul n id

(* Iterators and items *)

let iter_match (#i: _) (ls: asn1_gen_items_l i) (pm: perm) (it: seq_iter) (v: asn1_sequence_t_core ls) (w: SB.bytes) : slprop =
  S.pts_to it.rest #pm w ** pure (at_ok ls (U32.v it.idx) w v)

let item_match (#i: _) (ls: asn1_gen_items_l i) (pm: perm) (x: seq_item) (v: asn1_sequence_t_core ls) (w: SB.bytes) : slprop =
  S.pts_to x.bytes #pm w ** pure (item_ok ls (U32.v x.comp) w v)

(* Start iterating over the components of a SEQUENCE, from its encoding *)

let seq_k (id: asn1_id_t) (gitems: asn1_gen_items_lk) : asn1_k (Set.singleton id) =
  ASN1_ILC id (ASN1_SEQUENCE gitems)

let start_post (id: asn1_id_t) (gitems: asn1_gen_items_lk) (input: S.slice U8.t) (pm: perm) (w: SB.bytes) (v: asn1_sequence_t_core (dsnd gitems)) (res: seq_iter) : slprop =
  exists* wc . iter_match (dsnd gitems) pm res v wc ** Trade.trade (iter_match (dsnd gitems) pm res v wc) (S.pts_to input #pm w)

inline_for_extraction
fn start
  (id: Ghost.erased asn1_id_t) (gitems: Ghost.erased asn1_gen_items_lk)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_t_core (dsnd (Ghost.reveal gitems))))
requires S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind (asn1_as_parser (seq_k id gitems)) w v)
returns res: seq_iter
ensures start_post id gitems input pm w v res
{
  let c = ilc_content id #(ASN1_SEQUENCE gitems) (asn1_content_as_parser (ASN1_SEQUENCE gitems)) input #pm #w #v;
  with wc . assert (S.pts_to c #pm wc);
  seq_content gitems wc v;
  let res : seq_iter = { rest = c; idx = 0ul };
  rewrite (S.pts_to c #pm wc) as (S.pts_to res.rest #pm wc);
  fold (iter_match (dsnd gitems) pm res v wc);
  intro_trade (iter_match (dsnd gitems) pm res v wc) (S.pts_to input #pm w) (Trade.trade (S.pts_to c #pm wc) (S.pts_to input #pm w)) fn _ {
    unfold (iter_match (dsnd gitems) pm res v wc);
    rewrite (S.pts_to res.rest #pm wc) as (S.pts_to c #pm wc);
    Trade.elim (S.pts_to c #pm wc) (S.pts_to input #pm w);
  };
  fold (start_post id gitems input pm w v res);
  res
}

inline_for_extraction
fn is_empty
  (#i: Ghost.erased id_decs) (ls: Ghost.erased (asn1_gen_items_l i))
  (it: seq_iter) (#pm: perm) (#v: Ghost.erased (asn1_sequence_t_core ls)) (#w: Ghost.erased SB.bytes)
requires iter_match ls pm it v w
returns res: bool
ensures iter_match ls pm it v w ** pure (res == (Seq.length w = 0))
{
  unfold (iter_match ls pm it v w);
  S.pts_to_len it.rest;
  let res = SZ.eq (S.len it.rest) 0sz;
  fold (iter_match ls pm it v w);
  res
}

(* Read the next present component and advance the cursor. The item is the
   index of the component and the slice of its TLV. *)

let next_post (#i: _) (ls: asn1_gen_items_l i) (pi: R.ref seq_iter) (pm: perm) (it: seq_iter) (v: asn1_sequence_t_core ls) (w: SB.bytes) (res: seq_item) : slprop =
  exists* it' wi w' .
    R.pts_to pi it' **
    item_match ls pm res v wi **
    iter_match ls pm it' v w' **
    pure (Seq.length w' < Seq.length w) **
    Trade.trade (item_match ls pm res v wi ** iter_match ls pm it' v w') (iter_match ls pm it v w)

#push-options "--z3rlimit 64"

inline_for_extraction
fn next
  (#i: Ghost.erased id_decs) (ls: Ghost.erased (asn1_gen_items_l i))
  (fc: comp_t ls)
  (pi: R.ref seq_iter) (#it: Ghost.erased seq_iter) (#pm: perm) (#v: Ghost.erased (asn1_sequence_t_core ls)) (#w: Ghost.erased SB.bytes { Seq.length w > 0 })
requires R.pts_to pi it ** iter_match ls pm it v w
returns res: seq_item
ensures next_post ls pi pm it v w res
{
  let it0 = !pi;
  unfold (iter_match ls pm it v w);
  rewrite (S.pts_to it.rest #pm w) as (S.pts_to it0.rest #pm w);
  next_lemma ls (U32.v it0.idx) w v;
  L.identifier_nonempty w;
  S.pts_to_len it0.rest;
  let mut poff = 0sz;
  let oid = I.vread_identifier it0.rest poff;
  match oid {
    Some id -> {
      let c1 = !poff;
      let ol = ILC.vread_length it0.rest poff;
      match ol {
        Some len -> {
          let off2 = !poff;
          tlv_size_eq w (SZ.v c1) (SZ.v off2 - SZ.v c1) len;
          SZ.fits_lte (SZ.v off2 + U32.v len) (Seq.length w);
          let sz = SZ.add off2 (SZ.uint32_to_sizet len);
          let j = fc it0.idx id;
          let sp = SU.split_trade it0.rest sz;
          match sp {
            Mktuple2 s1 s2 -> {
              let item : seq_item = { comp = j; bytes = s1 };
              let it' : seq_iter = { rest = s2; idx = U32.add j 1ul };
              pi := it';
              let wi : Ghost.erased SB.bytes = Seq.slice w 0 (SZ.v sz);
              let w' : Ghost.erased SB.bytes = Seq.slice w (SZ.v sz) (Seq.length w);
              rewrite (S.pts_to s1 #pm (Seq.slice w 0 (SZ.v sz))) as (S.pts_to item.bytes #pm wi);
              fold (item_match ls pm item v wi);
              rewrite (S.pts_to s2 #pm (Seq.slice w (SZ.v sz) (Seq.length w))) as (S.pts_to it'.rest #pm w');
              fold (iter_match ls pm it' v w');
              intro_trade (item_match ls pm item v wi ** iter_match ls pm it' v w') (iter_match ls pm it v w)
                (Trade.trade (S.pts_to s1 #pm (Seq.slice w 0 (SZ.v sz)) ** S.pts_to s2 #pm (Seq.slice w (SZ.v sz) (Seq.length w))) (S.pts_to it0.rest #pm w) **
                  pure (it0 == Ghost.reveal it /\ at_ok ls (U32.v it.idx) w v)) fn _ {
                unfold (item_match ls pm item v wi);
                unfold (iter_match ls pm it' v w');
                rewrite (S.pts_to item.bytes #pm wi) as (S.pts_to s1 #pm (Seq.slice w 0 (SZ.v sz)));
                rewrite (S.pts_to it'.rest #pm w') as (S.pts_to s2 #pm (Seq.slice w (SZ.v sz) (Seq.length w)));
                Trade.elim _ (S.pts_to it0.rest #pm w);
                rewrite (S.pts_to it0.rest #pm w) as (S.pts_to it.rest #pm w);
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

(* Parse the bytes of an item, known to be the j-th component, with the
   parser of that component *)

let get_post (#i: _) (ls: asn1_gen_items_l i) (j: nat) (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (h: squash (item_is ls j dk))
  (pm: perm) (x: seq_item) (v: asn1_sequence_t_core ls) (w: SB.bytes) (res: t) : slprop =
  drel true dd pm res (vitem_at ls j dk h v) **
  Trade.trade (drel true dd pm res (vitem_at ls j dk h v)) (item_match ls pm x v w)

inline_for_extraction
fn get
  (#i: Ghost.erased id_decs) (ls: Ghost.erased (asn1_gen_items_l i)) (j: Ghost.erased nat)
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t: Type0) (dd: Ghost.erased (ddesc dk t))
  (h: squash (item_is ls j dk))
  (pres: dpresent dd)
  (x: seq_item) (#pm: perm) (#v: Ghost.erased (asn1_sequence_t_core ls)) (#w: Ghost.erased SB.bytes)
requires item_match ls pm x v w ** pure (U32.v x.comp == Ghost.reveal j)
returns res: t
ensures get_post ls j dd h pm x v w res
{
  unfold (item_match ls pm x v w);
  item_ok_at ls j w v;
  let res = pres x.bytes #pm #w #(vitem_at ls j dk h v);
  intro_trade (S.pts_to x.bytes #pm w) (item_match ls pm x v w) (pure (item_ok ls (U32.v x.comp) w v)) fn _ {
    fold (item_match ls pm x v w);
  };
  Trade.trans (drel true dd pm res (vitem_at ls j dk h v)) (S.pts_to x.bytes #pm w) (item_match ls pm x v w);
  fold (get_post ls j dd h pm x v w res);
  res
}

(* The types of the extraction roots *)

inline_for_extraction
let start_t (id: asn1_id_t) (gitems: asn1_gen_items_lk) : Type =
  (input: S.slice U8.t) -> (#pm: perm) -> (#w: Ghost.erased SB.bytes) -> (#v: Ghost.erased (asn1_sequence_t_core (dsnd gitems))) ->
  stt seq_iter
    (S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind (asn1_as_parser (seq_k id gitems)) w v))
    (fun res -> start_post id gitems input pm w v res)

inline_for_extraction
let is_empty_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (it: seq_iter) -> (#pm: perm) -> (#v: Ghost.erased (asn1_sequence_t_core ls)) -> (#w: Ghost.erased SB.bytes) ->
  stt bool (iter_match ls pm it v w) (fun res -> iter_match ls pm it v w ** pure (res == (Seq.length w = 0)))

inline_for_extraction
let next_t (#i: _) (ls: asn1_gen_items_l i) : Type =
  (pi: R.ref seq_iter) -> (#it: Ghost.erased seq_iter) -> (#pm: perm) -> (#v: Ghost.erased (asn1_sequence_t_core ls)) -> (#w: Ghost.erased SB.bytes { Seq.length w > 0 }) ->
  stt seq_item (R.pts_to pi it ** iter_match ls pm it v w) (fun res -> next_post ls pi pm it v w res)

inline_for_extraction
let get_t (#i: _) (ls: asn1_gen_items_l i) (j: nat) (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (h: squash (item_is ls j dk)) : Type =
  (x: seq_item) -> (#pm: perm) -> (#v: Ghost.erased (asn1_sequence_t_core ls)) -> (#w: Ghost.erased SB.bytes) ->
  stt t (item_match ls pm x v w ** pure (U32.v x.comp == j)) (fun res -> get_post ls j dd h pm x v w res)
