module ASN1.Pulse.ParseAdb
#lang-pulse

(* Zero-copy parsing of ANY DEFINED BY: the prefix items are visited as for
   a SEQUENCE, then the key TLV is read, its contents compared against each
   supported key in turn, and the remaining bytes are parsed as the SEQUENCE
   contents of the matching items (or, if none matches, of the fallback
   items, if any.) Only OBJECT IDENTIFIER keys are supported. *)

open Pulse.Lib.Pervasives
open LowParse.PulseParse.VReader
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.Any
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
module SC = LowParse.Spec.Combinators
module LPS = LowParse.Pulse.Base
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module In = ASN1.Pulse.Interpreter
module L = ASN1.Pulse.ParseSequence.Lemmas
module PS = ASN1.Pulse.ParseSequence
module AL = ASN1.Pulse.ParseAdb.Lemmas
module ADB = ASN1.Pulse.AnyDefinedBy
module T = FStar.Tactics

(* The prefix machine *)

let seqa_t_eq (#i: _) (ls: asn1_gen_items_l i) (t: Type)
: squash (asn1_sequence_any_t_core ls t == asn1_sequence_any_t (List.Tot.map Mkgendcparser?.d (In.twins_of ls)) t)
= PS.twins_d ls; asn1_sequence_any_t_equiv ls t

let seqa_parsed_core (#i: _) (ls: asn1_gen_items_l i) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: SB.bytes) (v: asn1_sequence_any_t_core ls t) : prop =
  AL.seqa_parsed (In.twins_of ls) sfx w (coerce_eq (seqa_t_eq ls t) v)

let consa (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids)
: Tot (asn1_gen_items_l ((s, d) :: ids))
= ASN1_GEN_ITEMS_CONS s d dk ids tl

#push-options "--fuel 2 --ifuel 2"
let consa_t_eq (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids) (t: Type)
: squash (asn1_sequence_any_t_core (consa dk tl) t == (asn1_decorated_t_core dk & asn1_sequence_any_t_core tl t))
= match tl with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ -> ()

#pop-options

let avfst (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids) (#t: Type) (v: asn1_sequence_any_t_core (consa dk tl) t)
: Tot (asn1_decorated_t_core dk)
= fst (coerce_eq (consa_t_eq dk tl t) v)

let avsnd (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids) (#t: Type) (v: asn1_sequence_any_t_core (consa dk tl) t)
: Tot (asn1_sequence_any_t_core tl t)
= snd (coerce_eq (consa_t_eq dk tl t) v)

(* The descriptor `dia` of `consa dk tl` relates a pair as `dd` and `dtl`:
   this holds for `IA_SINGLE dd` with `dtl == IA_NIL`, and `IA_CONS dd dtl`. *)
let ia_cons_prop (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#ids: _) (#tl: asn1_gen_items_l ids) (#sfxi: Type0) (#t2: Type0) (dtl: iadesc tl sfxi t2)
  (dia: iadesc (consa dk tl) sfxi (t1 & t2)) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) : prop
= forall (pm: perm) (r1: t1) (r2: t2) (y: asn1_sequence_any_t_core (consa dk tl) sfxs) .
    iarel true dia sfxr pm (r1, r2) y == (drel true dd pm r1 (avfst dk tl y) ** iarel true dtl sfxr pm r2 (avsnd dk tl y))

let ia_cons_inst (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#ids: _) (#tl: asn1_gen_items_l ids) (#sfxi: Type0) (#t2: Type0) (dtl: iadesc tl sfxi t2)
  (dia: iadesc (consa dk tl) sfxi (t1 & t2)) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop)
  (sq: squash (ia_cons_prop dd dtl dia sfxr))
  (pm: perm) (r1: t1) (r2: t2) (y: asn1_sequence_any_t_core (consa dk tl) sfxs)
: Lemma (iarel true dia sfxr pm (r1, r2) y == (drel true dd pm r1 (avfst dk tl y) ** iarel true dtl sfxr pm r2 (avsnd dk tl y)))
= ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let ia_single_prop (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop)
: Lemma (ia_cons_prop dd (IA_NIL #sfxi) (IA_SINGLE dd) sfxr)
= let aux (pm: perm) (r1: t1) (r2: sfxi) (y: asn1_sequence_any_t_core (consa dk ASN1_GEN_ITEMS_NIL) sfxs)
  : Lemma (iarel true (IA_SINGLE #_ #_ #_ #_ dd #sfxi) sfxr pm (r1, r2) y == (drel true dd pm r1 (avfst dk ASN1_GEN_ITEMS_NIL y) ** iarel true (IA_NIL #sfxi) sfxr pm r2 (avsnd dk ASN1_GEN_ITEMS_NIL y)))
  = assert_norm (iarel true (IA_NIL #sfxi) sfxr pm r2 (avsnd dk ASN1_GEN_ITEMS_NIL y) == sfxr pm r2 (avsnd dk ASN1_GEN_ITEMS_NIL y))
  in
  Classical.forall_intro_4 aux

let ia_cons_cons_prop (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#sfxi: Type0) (#t2: Type0)
  (dtl: iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi t2) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop)
: Lemma (ia_cons_prop dd dtl (IA_CONS dd dtl) sfxr)
= ()
#pop-options

let items_any_rel_nil_eq (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm) (x: sfxi) (y: sfxs)
: Lemma (iarel true (IA_NIL #sfxi) sfxr pm x y == sfxr pm x y)
= assert_norm (iarel true (IA_NIL #sfxi) sfxr pm x y == sfxr pm x y)

let seqa_cons_post_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (w: SB.bytes) (v: asn1_sequence_any_t_core (consa dk tl) t) : prop
= let v1 = avfst dk tl v in
  let v2 = avsnd dk tl v in
  match SB.parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, _) ->
    if Set.mem id s
    then (match L.tlv_size w with
      | None -> False
      | Some n -> n <= Seq.length w /\ PS.item_parsed_core dk (Seq.slice w 0 n) v1 /\ seqa_parsed_core tl sfx (Seq.slice w n (Seq.length w)) v2)
    else PS.absent_core dk v1 /\ seqa_parsed_core tl sfx w v2

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let seqa_cons_core (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (w: SB.bytes) (v: asn1_sequence_any_t_core (consa dk tl) t)
: Lemma
  (requires seqa_parsed_core (consa dk tl) sfx w v /\ AL.sfx_shaped sfx)
  (ensures seqa_cons_post_core dk tl sfx w v)
= let _ = seqa_t_eq (consa dk tl) t in
  let _ = seqa_t_eq tl t in
  let _ = PS.twin_d dk in
  let _ = consa_t_eq dk tl t in
  PS.twin_d_eq dk;
  L.dec_shaped dk;
  AL.seqa_cons (In.twin_of dk) (In.twins_of tl) sfx w (coerce_eq (seqa_t_eq (consa dk tl) t) v)
#pop-options

let seqa_nil_core (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: SB.bytes) (v: asn1_sequence_any_t_core ASN1_GEN_ITEMS_NIL t)
: Lemma
  (requires seqa_parsed_core ASN1_GEN_ITEMS_NIL sfx w v)
  (ensures parsed #asn1_weak_parser_kind (Mkparsertwin?.p sfx) w v)
= AL.seqa_nil sfx w v

(* Prefix parsers *)

inline_for_extraction
let saparser (#i: _) (#ls: asn1_gen_items_l i) (#sfxi: Type0) (#t: Type0) (dia: iadesc ls sfxi t) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (sfx: parser_twin asn1_weak_parser_kind sfxs) : Type =
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#w: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (asn1_sequence_any_t_core ls sfxs)) ->
  stt t
    (S.pts_to input #pm w ** pure (seqa_parsed_core ls sfx w v /\ AL.sfx_shaped sfx))
    (fun res -> iarel true dia sfxr pm res v ** Trade.trade (iarel true dia sfxr pm res v) (S.pts_to input #pm w))

inline_for_extraction
fn seqa_nil
  (#sfxi: Type0) (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (psfx: aparser #sfxi #sfxs sfxr #asn1_weak_parser_kind (Mkparsertwin?.p (Ghost.reveal sfx)))
: saparser (IA_NIL #sfxi) #sfxs sfxr (Ghost.reveal sfx)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seqa_nil_core sfx w v;
  let v' : Ghost.erased sfxs = Ghost.hide #sfxs (Ghost.reveal v);
  let res : sfxi = psfx input #pm #w #v';
  items_any_rel_nil_eq sfxr pm res v';
  rewrite each (sfxr pm res v') as (iarel true (IA_NIL #sfxi) sfxr pm res v);
  res
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn seqa_cons_absent
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#ids: Ghost.erased id_decs) (#tl: Ghost.erased (asn1_gen_items_l ids)) (#sfxi: Type0) (#t2: Type0) (dtl: Ghost.erased (iadesc tl sfxi t2))
  (dia: Ghost.erased (iadesc (consa dk tl) sfxi (t1 & t2)))
  (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (sq: squash (ia_cons_prop dd dtl dia sfxr))
  (abs: PS.dabsent dd)
  (ptail: saparser dtl sfxr sfx)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_any_t_core (consa dk tl) sfxs))
  requires S.pts_to input #pm w ** pure (PS.absent_core dk (avfst dk tl v) /\ seqa_parsed_core tl sfx w (avsnd dk tl v) /\ AL.sfx_shaped sfx)
  returns res: (t1 & t2)
  ensures iarel true dia sfxr pm res v ** Trade.trade (iarel true dia sfxr pm res v) (S.pts_to input #pm w)
{
  let r1 = abs pm (avfst dk tl v);
  let r2 = ptail input #pm #w #(avsnd dk tl v);
  PS.trade_emp_l (drel true dd pm r1 (avfst dk tl v)) (iarel true dtl sfxr pm r2 (avsnd dk tl v)) (S.pts_to input #pm w);
  let res : (t1 & t2) = (r1, r2);
  ia_cons_inst dd dtl dia sfxr sq pm r1 r2 v;
  rewrite (drel true dd pm r1 (avfst dk tl v) ** iarel true dtl sfxr pm r2 (avsnd dk tl v))
    as (iarel true dia sfxr pm res v);
  rewrite (Trade.trade (drel true dd pm r1 (avfst dk tl v) ** iarel true dtl sfxr pm r2 (avsnd dk tl v)) (S.pts_to input #pm w))
    as (Trade.trade (iarel true dia sfxr pm res v) (S.pts_to input #pm w));
  res
}

inline_for_extraction
fn seqa_cons_present
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#ids: Ghost.erased id_decs) (#tl: Ghost.erased (asn1_gen_items_l ids)) (#sfxi: Type0) (#t2: Type0) (dtl: Ghost.erased (iadesc tl sfxi t2))
  (dia: Ghost.erased (iadesc (consa dk tl) sfxi (t1 & t2)))
  (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (sq: squash (ia_cons_prop dd dtl dia sfxr))
  (pres: PS.dpresent dd)
  (ptail: saparser dtl sfxr sfx)
  (n: SZ.t)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_any_t_core (consa dk tl) sfxs))
  requires S.pts_to input #pm w ** pure (SZ.v n <= Seq.length w /\ PS.item_parsed_core dk (Seq.slice w 0 (SZ.v n)) (avfst dk tl v) /\ seqa_parsed_core tl sfx (Seq.slice w (SZ.v n) (Seq.length w)) (avsnd dk tl v) /\ AL.sfx_shaped sfx)
  returns res: (t1 & t2)
  ensures iarel true dia sfxr pm res v ** Trade.trade (iarel true dia sfxr pm res v) (S.pts_to input #pm w)
{
  let in1, in2 = SU.split_trade input n;
  let r1 = pres in1 #pm #(Seq.slice w 0 (SZ.v n)) #(avfst dk tl v);
  let r2 = ptail in2 #pm #(Seq.slice w (SZ.v n) (Seq.length w)) #(avsnd dk tl v);
  Trade.prod
    (drel true dd pm r1 (avfst dk tl v)) (S.pts_to in1 #pm (Seq.slice w 0 (SZ.v n)))
    (iarel true dtl sfxr pm r2 (avsnd dk tl v)) (S.pts_to in2 #pm (Seq.slice w (SZ.v n) (Seq.length w)));
  Trade.trans
    (drel true dd pm r1 (avfst dk tl v) ** iarel true dtl sfxr pm r2 (avsnd dk tl v))
    (S.pts_to in1 #pm (Seq.slice w 0 (SZ.v n)) ** S.pts_to in2 #pm (Seq.slice w (SZ.v n) (Seq.length w)))
    (S.pts_to input #pm w);
  let res : (t1 & t2) = (r1, r2);
  ia_cons_inst dd dtl dia sfxr sq pm r1 r2 v;
  rewrite (drel true dd pm r1 (avfst dk tl v) ** iarel true dtl sfxr pm r2 (avsnd dk tl v))
    as (iarel true dia sfxr pm res v);
  rewrite (Trade.trade (drel true dd pm r1 (avfst dk tl v) ** iarel true dtl sfxr pm r2 (avsnd dk tl v)) (S.pts_to input #pm w))
    as (Trade.trade (iarel true dia sfxr pm res v) (S.pts_to input #pm w));
  res
}

(* `dia` is `IA_SINGLE dd` (with `dtl == IA_NIL`) or `IA_CONS dd dtl` *)
inline_for_extraction
fn seqa_cons
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (#dk: Ghost.erased (asn1_decorated_k s d)) (#t1: Type0) (dd: Ghost.erased (ddesc dk t1))
  (#ids: Ghost.erased id_decs) (#tl: Ghost.erased (asn1_gen_items_l ids)) (#sfxi: Type0) (#t2: Type0) (dtl: Ghost.erased (iadesc tl sfxi t2))
  (dia: Ghost.erased (iadesc (consa dk tl) sfxi (t1 & t2)))
  (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (sq: squash (ia_cons_prop dd dtl dia sfxr))
  (has_id: (id: asn1_id_t) -> Tot (b: bool { b == Set.mem id s }))
  (pres: PS.dpresent dd) (abs: PS.dabsent dd)
  (ptail: saparser dtl sfxr sfx)
: saparser (Ghost.reveal dia) sfxr sfx
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seqa_cons_core dk tl sfx w v;
  S.pts_to_len input;
  Seq.slice_length (Ghost.reveal w);
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
            PS.tlv_size_eq w (SZ.v c1) (SZ.v off2 - SZ.v c1) len;
            SZ.fits_lte (SZ.v off2 + U32.v len) (Seq.length w);
            let n = SZ.add off2 (SZ.uint32_to_sizet len);
            seqa_cons_present dd dtl dia sq pres ptail n input #pm #w #v
          }
          None -> {
            unreachable ()
          }
        }
      } else {
        seqa_cons_absent dd dtl dia sq abs ptail input #pm #w #v
      }
    }
    None -> {
      unreachable ()
    }
  }
}

#pop-options

(* The suffix: splitting the key TLV from the payload *)

ghost
fn trade_frame_l (h a b: slprop)
  requires h ** Trade.trade a b
  ensures Trade.trade a (h ** b)
{
  intro (Trade.trade a (h ** b)) #(h ** Trade.trade a b) fn _ {
    Trade.elim a b;
  };
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn sfx_split
  (key_k: Ghost.erased asn1_terminal_k) (key: Ghost.erased (asn1_terminal_t key_k)) (q: Ghost.erased (SB.bytes -> prop))
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes)
  requires S.pts_to input #pm w ** pure (AL.layout_post key_k key q w)
  returns res: (S.slice U8.t & S.slice U8.t)
  ensures exists* wk wp .
    S.pts_to (fst res) #pm wk ** S.pts_to (snd res) #pm wp **
    Trade.trade (S.pts_to (fst res) #pm wk ** S.pts_to (snd res) #pm wp) (S.pts_to input #pm w) **
    pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk key /\ Ghost.reveal q wp)
{
  S.pts_to_len input;
  Seq.slice_length (Ghost.reveal w);
  let mut poff = 0sz;
  let oid = I.vread_identifier input poff;
  match oid {
    Some id -> {
      let ol = ILC.vread_length input poff;
      match ol {
        Some len -> {
          let off2 = !poff;
          SZ.fits_lte (SZ.v off2 + U32.v len) (Seq.length w);
          let rest = SU.subslice_trade input off2 (S.len input);
          let kc, pin = SU.split_trade rest (SZ.uint32_to_sizet len);
          with wk . assert (S.pts_to kc #pm wk);
          with wp . assert (S.pts_to pin #pm wp);
          with wr . assert (Trade.trade (S.pts_to kc #pm wk ** S.pts_to pin #pm wp) (S.pts_to rest #pm wr));
          Seq.slice_slice w (SZ.v off2) (Seq.length w) 0 (U32.v len);
          Seq.slice_slice w (SZ.v off2) (Seq.length w) (U32.v len) (Seq.length w - SZ.v off2);
          Trade.trans (S.pts_to kc #pm wk ** S.pts_to pin #pm wp) (S.pts_to rest #pm wr) (S.pts_to input #pm w);
          (kc, pin)
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

(* Dispatching on the key, without a fallback *)

let pl_single (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (wp: SB.bytes) (v: AL.ady key_k [(x, y)])
: Lemma (requires AL.pl_parsed key_k [(x, y)] wp v) (ensures dfst v == key_of_lit key_k x)
= if dfst v <> key_of_lit key_k x
  then begin
    AL.pl_tail x y [] wp v;
    AL.pl_nil key_k wp (AL.ady_tail_val x y [] v ())
  end

let adb_rel_single_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (pm: perm)
  (r: t) (v: AL.ady key_k [(x, y)]) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (sxrel true (SX_SINGLE key_k x y di) pm r v == irel true di pm r (AL.ady_head_val x y [] v ()))
= assert_norm (sxrel true (SX_SINGLE key_k x y di) pm r v == (let (| key, v |) = v in if key = key_of_lit key_k x then irel true di pm r v else pure False))

let adb_rel_cons_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: asn1_key_lit key_k & asn1_gen_items_lk) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (r: either t1 t2) (key: asn1_terminal_t key_k) (w: idlookup_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((x, y) :: hd2 :: tl2)))
: Lemma (sxrel true (SX_CONS key_k x y di dtl) pm r ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ==
    (match r with
     | Inl a -> if key = key_of_lit key_k x then irel true di pm a w else pure False
     | Inr b -> if key = key_of_lit key_k x then pure False else sxrel true dtl pm b (AL.ady_tail_val x y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ())))
= assert (sxrel true (SX_CONS key_k x y di dtl) pm r ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ==
    (match r with
     | Inl a -> if key = key_of_lit key_k x then irel true di pm a w else pure False
     | Inr b -> if key = key_of_lit key_k x then pure False else sxrel true dtl pm b (AL.ady_tail_val x y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ())))
  by (T.norm [delta_only [`%sxrel; `%AL.ady_tail_val]; zeta; iota]; T.trefl ())

let adb_rel_cons_inl_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: asn1_key_lit key_k & asn1_gen_items_lk) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (a: t1) (v: AL.ady key_k ((x, y) :: hd2 :: tl2)) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (sxrel true (SX_CONS key_k x y di dtl) pm (Inl #_ #t2 a) v == irel true di pm a (AL.ady_head_val x y (hd2 :: tl2) v ()))
= let (| key, w |) = v in
  adb_rel_cons_aux x y di dtl pm (Inl a) key w

let adb_rel_cons_inr_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: asn1_key_lit key_k & asn1_gen_items_lk) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (pm: perm) (b: t2) (v: AL.ady key_k ((x, y) :: hd2 :: tl2)) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (sxrel true (SX_CONS key_k x y di dtl) pm (Inr #t1 b) v == sxrel true dtl pm b (AL.ady_tail_val x y (hd2 :: tl2) v ()))
= let (| key, w |) = v in
  adb_rel_cons_aux x y di dtl pm (Inr b) key w

inline_for_extraction
let ndisp (key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t) : Type =
  (kc: S.slice U8.t) ->
  (pin: S.slice U8.t) ->
  (#pm: perm) ->
  (#wk: Ghost.erased SB.bytes) ->
  (#wp: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (AL.ady key_k ls)) ->
  stt t
    (S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk (dfst (Ghost.reveal v)) /\ AL.pl_parsed key_k ls wp v))
    (fun res -> sxrel true dsx pm res v ** Trade.trade (sxrel true dsx pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))

inline_for_extraction
let items_parser (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) : Type =
  aparser #t #(asn1_sequence_t_core (dsnd y)) (irel true di) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE y))

inline_for_extraction
fn ndisp_nil (key_k: asn1_terminal_k)
: ndisp key_k (SX_NIL key_k)
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  AL.pl_nil key_k wp v;
  unreachable ()
}

inline_for_extraction
fn ndisp_single (key_k: asn1_terminal_k) (x: Ghost.erased (asn1_key_lit key_k)) (y: Ghost.erased asn1_gen_items_lk) (#t: Type0) (di: Ghost.erased (idesc (dsnd y) t))
  (pitems: items_parser y di)
: ndisp key_k (SX_SINGLE key_k x y di)
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  pl_single x y wp v;
  AL.pl_head x y [] wp v;
  let res = pitems pin #pm #wp #(AL.ady_head_val x y [] v ());
  trade_frame_l (S.pts_to kc #pm wk) (irel true di pm res (AL.ady_head_val x y [] v ())) (S.pts_to pin #pm wp);
  adb_rel_single_eq x y di pm res v ();
  rewrite each (irel true di pm res (AL.ady_head_val x y [] v ())) as (sxrel true (SX_SINGLE key_k x y di) pm res v);
  res
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn ndisp_cons (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (x: asn1_key_lit key_k) (y: Ghost.erased asn1_gen_items_lk) (#t1: Type0) (di: Ghost.erased (idesc (dsnd y) t1))
  (#hd2: Ghost.erased (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (#t2: Type0) (dtl: Ghost.erased (sxdesc key_k (Ghost.reveal hd2 :: Ghost.reveal tl2) t2))
  (pitems: items_parser y di)
  (ptail: ndisp key_k dtl)
: ndisp key_k (SX_CONS key_k x y di dtl)
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  S.pts_to_len kc;
  AL.key_check_fl key_k (key_of_lit key_k x) (dfst v) wk;
  let mut poff = 0sz;
  let ok = In.validate_key_eq_fl key_k () x (S.len kc) kc poff;
  if ok {
    AL.pl_head x y (Ghost.reveal hd2 :: Ghost.reveal tl2) wp v;
    let r = pitems pin #pm #wp #(AL.ady_head_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) v ());
    trade_frame_l (S.pts_to kc #pm wk) (irel true di pm r (AL.ady_head_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) v ())) (S.pts_to pin #pm wp);
    let res : either t1 t2 = Inl #_ #t2 r;
    adb_rel_cons_inl_eq x y di dtl pm r v ();
    rewrite each (irel true di pm r (AL.ady_head_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) v ())) as (sxrel true (SX_CONS key_k x y di dtl) pm res v);
    res
  } else {
    AL.pl_tail x y (Ghost.reveal hd2 :: Ghost.reveal tl2) wp v;
    let r = ptail kc pin #pm #wk #wp #(AL.ady_tail_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) v ());
    let res : either t1 t2 = Inr #t1 r;
    adb_rel_cons_inr_eq x y di dtl pm r v ();
    rewrite each (sxrel true dtl pm r (AL.ady_tail_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) v ())) as (sxrel true (SX_CONS key_k x y di dtl) pm res v);
    res
  }
}

#pop-options

(* Dispatching on the key, with a fallback *)

(* The legacy fallback type. `Mkdtuple2?._2` rather than `dsnd`, so that Custard can reduce this type *)
let fbt (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) : Type0 =
  asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb)

let fbs (fb: asn1_gen_items_lk) : Type =
  asn1_sequence_t_core (dsnd fb)

let fbr (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) : perm -> (asn1_terminal_impl_t key_k & tfb) -> asn1_terminal_t key_k -> fbs fb -> slprop =
  fun pm (z: asn1_terminal_impl_t key_k & tfb) key (v: asn1_sequence_t_core (dsnd fb)) ->
    asn1_terminal_rel key_k pm (fst z) key ** irel true dfb pm (snd z) v

let afb_rel (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts)
= fxrel true dfx (fbs fb) (fbr key_k fb dfb)

let afb_rel_nil_aux (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (pm: perm)
  (rk: asn1_terminal_impl_t key_k) (ri: tfb) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) []) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel fb dfb (FX_NIL key_k) pm (rk, ri) ((| key, w |) <: AL.ady_fb key_k [] fb) ==
    (asn1_terminal_rel key_k pm rk key ** irel true dfb pm ri (AL.ady_fb_nil_val fb ((| key, w |) <: AL.ady_fb key_k [] fb))))
= assert (afb_rel fb dfb (FX_NIL key_k) pm (rk, ri) ((| key, w |) <: AL.ady_fb key_k [] fb) ==
    (asn1_terminal_rel key_k pm rk key ** irel true dfb pm ri (AL.ady_fb_nil_val fb ((| key, w |) <: AL.ady_fb key_k [] fb))))
  by (T.norm [delta_only [`%afb_rel; `%fxrel; `%fbr; `%AL.ady_fb_nil_val; `%dsnd; `%fst; `%snd]; zeta; iota]; T.trefl ())

let afb_rel_nil_eq (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (pm: perm)
  (rk: asn1_terminal_impl_t key_k) (ri: tfb) (v: AL.ady_fb key_k [] fb)
: Lemma (afb_rel fb dfb (FX_NIL key_k) pm (rk, ri) v ==
    (asn1_terminal_rel key_k pm rk (dfst v) ** irel true dfb pm ri (AL.ady_fb_nil_val fb v)))
= let (| key, w |) = v in
  afb_rel_nil_aux fb dfb pm rk ri key w

let afb_rel_single_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (pm: perm) (r: either t1 (asn1_terminal_impl_t key_k & tfb))
  (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) [(x, y)]) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel fb dfb (FX_SINGLE key_k x y di) pm r ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ==
    (match r with
     | Inl a -> if key = key_of_lit key_k x then irel true di pm a (AL.ady_fb_head_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()) else pure False
     | Inr b -> if key = key_of_lit key_k x then pure False else fbr key_k fb dfb pm b key (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()))))
= assert (afb_rel fb dfb (FX_SINGLE key_k x y di) pm r ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ==
    (match r with
     | Inl a -> if key = key_of_lit key_k x then irel true di pm a (AL.ady_fb_head_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()) else pure False
     | Inr b -> if key = key_of_lit key_k x then pure False else fbr key_k fb dfb pm b key (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()))))
  by (T.norm [delta_only [`%afb_rel; `%fxrel; `%AL.ady_fb_head_val; `%AL.ady_fb_tail_val; `%AL.ady_fb_nil_val]; zeta; iota]; T.trefl ())

let afb_rel_cons_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: asn1_key_lit key_k & asn1_gen_items_lk) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2)
  (pm: perm) (r: either t1 t2)
  (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((x, y) :: hd2 :: tl2)) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel fb dfb (FX_CONS key_k x y di dtl) pm r ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ==
    (match r with
     | Inl a -> if key = key_of_lit key_k x then irel true di pm a (AL.ady_fb_head_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ()) else pure False
     | Inr b -> if key = key_of_lit key_k x then pure False else afb_rel fb dfb dtl pm b (AL.ady_fb_tail_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ())))
= assert (afb_rel fb dfb (FX_CONS key_k x y di dtl) pm r ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ==
    (match r with
     | Inl a -> if key = key_of_lit key_k x then irel true di pm a (AL.ady_fb_head_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ()) else pure False
     | Inr b -> if key = key_of_lit key_k x then pure False else afb_rel fb dfb dtl pm b (AL.ady_fb_tail_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ())))
  by (T.norm [delta_only [`%afb_rel; `%fxrel; `%AL.ady_fb_head_val; `%AL.ady_fb_tail_val]; zeta; iota]; T.trefl ())

let afb_rel_single_inl_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (pm: perm)
  (a: t1) (v: AL.ady_fb key_k [(x, y)] fb) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (afb_rel fb dfb (FX_SINGLE key_k x y di) pm (Inl #_ #(asn1_terminal_impl_t key_k & tfb) a) v == irel true di pm a (AL.ady_fb_head_val x y [] fb v ()))
= let (| key, w |) = v in
  afb_rel_single_aux x y di fb dfb pm (Inl a) key w

let afb_rel_single_inr_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (pm: perm)
  (b: asn1_terminal_impl_t key_k & tfb) (v: AL.ady_fb key_k [(x, y)] fb) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (afb_rel fb dfb (FX_SINGLE key_k x y di) pm (Inr #t1 b) v == fbr key_k fb dfb pm b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb v ())))
= let (| key, w |) = v in
  afb_rel_single_aux x y di fb dfb pm (Inr b) key w

let afb_rel_cons_inl_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: asn1_key_lit key_k & asn1_gen_items_lk) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2) (pm: perm)
  (a: t1) (v: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (afb_rel fb dfb (FX_CONS key_k x y di dtl) pm (Inl #_ #t2 a) v == irel true di pm a (AL.ady_fb_head_val x y (hd2 :: tl2) fb v ()))
= let (| key, w |) = v in
  afb_rel_cons_aux x y di fb dfb dtl pm (Inl a) key w

let afb_rel_cons_inr_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: asn1_key_lit key_k & asn1_gen_items_lk) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2) (pm: perm)
  (b: t2) (v: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (afb_rel fb dfb (FX_CONS key_k x y di dtl) pm (Inr #t1 b) v == afb_rel fb dfb dtl pm b (AL.ady_fb_tail_val x y (hd2 :: tl2) fb v ()))
= let (| key, w |) = v in
  afb_rel_cons_aux x y di fb dfb dtl pm (Inr b) key w

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let dfst_fb_tail_val (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: AL.ady_fb key_k ((x, y) :: tl) fb) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (dfst (AL.ady_fb_tail_val x y tl fb v ()) == dfst v)
= ()
#pop-options

inline_for_extraction
let fdisp (key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts) : Type =
  (kc: S.slice U8.t) ->
  (pin: S.slice U8.t) ->
  (#pm: perm) ->
  (#wk: Ghost.erased SB.bytes) ->
  (#wp: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (AL.ady_fb key_k ls fb)) ->
  stt ts
    (S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk (dfst (Ghost.reveal v)) /\ AL.pl_fb_parsed key_k ls fb wp v))
    (fun res -> afb_rel fb dfb dfx pm res v ** Trade.trade (afb_rel fb dfb dfx pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))

inline_for_extraction
let key_parser (key_k: asn1_terminal_k) : Type =
  aparser #(asn1_terminal_impl_t key_k) #(asn1_terminal_t key_k) (asn1_terminal_rel key_k) #asn1_weak_parser_kind (asn1_terminal_as_parser key_k)

inline_for_extraction
fn fb_core (key_k: asn1_terminal_k) (fb: Ghost.erased asn1_gen_items_lk) (#tfb: Type0) (dfb: Ghost.erased (idesc (dsnd fb) tfb))
  (pkey: key_parser key_k) (pitems: items_parser fb dfb)
  (kc: S.slice U8.t) (pin: S.slice U8.t) (#pm: perm) (#wk: Ghost.erased SB.bytes) (#wp: Ghost.erased SB.bytes)
  (key: Ghost.erased (asn1_terminal_t key_k)) (v: Ghost.erased (asn1_sequence_t_core (dsnd fb)))
  requires S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk key /\ parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE fb)) wp v)
  returns res: (asn1_terminal_impl_t key_k & tfb)
  ensures fbr key_k fb dfb pm res key v ** Trade.trade (fbr key_k fb dfb pm res key v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp)
{
  let rk = pkey kc #pm #wk #key;
  let ri = pitems pin #pm #wp #v;
  Trade.prod
    (asn1_terminal_rel key_k pm rk key) (S.pts_to kc #pm wk)
    (irel true dfb pm ri v) (S.pts_to pin #pm wp);
  let res : (asn1_terminal_impl_t key_k & tfb) = (rk, ri);
  rewrite (asn1_terminal_rel key_k pm rk key ** irel true dfb pm ri v)
    as (fbr key_k fb dfb pm res key v);
  rewrite (Trade.trade (asn1_terminal_rel key_k pm rk key ** irel true dfb pm ri v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))
    as (Trade.trade (fbr key_k fb dfb pm res key v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp));
  res
}

inline_for_extraction
fn fdisp_nil (key_k: asn1_terminal_k) (fb: Ghost.erased asn1_gen_items_lk) (#tfb: Type0) (dfb: Ghost.erased (idesc (dsnd fb) tfb))
  (pkey: key_parser key_k) (pitems: items_parser fb dfb)
: fdisp key_k fb dfb (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb))
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  AL.pl_fb_nil fb wp v;
  let res = fb_core key_k fb dfb pkey pitems kc pin (dfst v) (AL.ady_fb_nil_val fb v);
  afb_rel_nil_eq fb dfb pm (fst res) (snd res) v;
  rewrite each (fbr key_k fb dfb pm res (dfst v) (AL.ady_fb_nil_val fb v)) as (afb_rel fb dfb (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) pm res v);
  res
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn fdisp_single (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (x: asn1_key_lit key_k) (y: Ghost.erased asn1_gen_items_lk) (#t1: Type0) (di: Ghost.erased (idesc (dsnd y) t1))
  (fb: Ghost.erased asn1_gen_items_lk) (#tfb: Type0) (dfb: Ghost.erased (idesc (dsnd fb) tfb))
  (pitems: items_parser y di)
  (pkey: key_parser key_k) (pfb: items_parser fb dfb)
: fdisp key_k fb dfb (FX_SINGLE key_k x y di #(asn1_terminal_impl_t key_k & tfb))
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  S.pts_to_len kc;
  AL.key_check_fl key_k (key_of_lit key_k x) (dfst v) wk;
  let mut poff = 0sz;
  let ok = In.validate_key_eq_fl key_k () x (S.len kc) kc poff;
  if ok {
    AL.pl_fb_head x y [] fb wp v;
    let r = pitems pin #pm #wp #(AL.ady_fb_head_val x y [] fb v ());
    trade_frame_l (S.pts_to kc #pm wk) (irel true di pm r (AL.ady_fb_head_val x y [] fb v ())) (S.pts_to pin #pm wp);
    let res : either t1 (asn1_terminal_impl_t key_k & tfb) = Inl #_ #(asn1_terminal_impl_t key_k & tfb) r;
    afb_rel_single_inl_eq x y di fb dfb pm r v ();
    rewrite each (irel true di pm r (AL.ady_fb_head_val x y [] fb v ())) as (afb_rel fb dfb (FX_SINGLE key_k x y di #(asn1_terminal_impl_t key_k & tfb)) pm res v);
    res
  } else {
    AL.pl_fb_tail x y [] fb wp v;
    AL.pl_fb_nil fb wp (AL.ady_fb_tail_val x y [] fb v ());
    dfst_fb_tail_val x y [] fb v ();
    let r = fb_core key_k fb dfb pkey pfb kc pin (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb v ()));
    let res : either t1 (asn1_terminal_impl_t key_k & tfb) = Inr #t1 r;
    afb_rel_single_inr_eq x y di fb dfb pm r v ();
    rewrite each (fbr key_k fb dfb pm r (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb v ()))) as (afb_rel fb dfb (FX_SINGLE key_k x y di #(asn1_terminal_impl_t key_k & tfb)) pm res v);
    res
  }
}

inline_for_extraction
fn fdisp_cons (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (x: asn1_key_lit key_k) (y: Ghost.erased asn1_gen_items_lk) (#t1: Type0) (di: Ghost.erased (idesc (dsnd y) t1))
  (#hd2: Ghost.erased (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk)))
  (fb: Ghost.erased asn1_gen_items_lk) (#tfb: Type0) (dfb: Ghost.erased (idesc (dsnd fb) tfb))
  (#t2: Type0) (dtl: Ghost.erased (fxdesc key_k (Ghost.reveal hd2 :: Ghost.reveal tl2) (asn1_terminal_impl_t key_k & tfb) t2))
  (pitems: items_parser y di)
  (ptail: fdisp key_k fb dfb dtl)
: fdisp key_k fb dfb (FX_CONS key_k x y di dtl)
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  S.pts_to_len kc;
  AL.key_check_fl key_k (key_of_lit key_k x) (dfst v) wk;
  let mut poff = 0sz;
  let ok = In.validate_key_eq_fl key_k () x (S.len kc) kc poff;
  if ok {
    AL.pl_fb_head x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb wp v;
    let r = pitems pin #pm #wp #(AL.ady_fb_head_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb v ());
    trade_frame_l (S.pts_to kc #pm wk) (irel true di pm r (AL.ady_fb_head_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb v ())) (S.pts_to pin #pm wp);
    let res : either t1 t2 = Inl #_ #t2 r;
    afb_rel_cons_inl_eq x y di fb dfb dtl pm r v ();
    rewrite each (irel true di pm r (AL.ady_fb_head_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb v ())) as (afb_rel fb dfb (FX_CONS key_k x y di dtl) pm res v);
    res
  } else {
    AL.pl_fb_tail x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb wp v;
    dfst_fb_tail_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb v ();
    let r = ptail kc pin #pm #wk #wp #(AL.ady_fb_tail_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb v ());
    let res : either t1 t2 = Inr #t1 r;
    afb_rel_cons_inr_eq x y di fb dfb dtl pm r v ();
    rewrite each (afb_rel fb dfb dtl pm r (AL.ady_fb_tail_val x y (Ghost.reveal hd2 :: Ghost.reveal tl2) fb v ())) as (afb_rel fb dfb (FX_CONS key_k x y di dtl) pm res v);
    res
  }
}

#pop-options

(* The suffix parsers *)

let sfx_none (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Tot (parser_twin asn1_weak_parser_kind (AL.ady key_k ls))
= ADB.adb_sfx_none kid key_k ls

let sfx_some (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: Tot (parser_twin asn1_weak_parser_kind (AL.ady_fb key_k ls fb))
= ADB.adb_sfx_some kid key_k ls fb

inline_for_extraction
fn sfx_none_parser (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k) (#ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (#t: Type0) (dsx: Ghost.erased (sxdesc key_k ls t))
  (disp: ndisp key_k dsx)
: aparser #t #(AL.ady key_k ls) (sxrel true dsx) #asn1_weak_parser_kind (Mkparsertwin?.p (sfx_none kid key_k ls))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  AL.sfx_none_layout kid key_k ls w v;
  let kc, pin = sfx_split key_k (dfst v) (fun wp -> AL.pl_parsed key_k ls wp v) input;
  with wk wp . assert (S.pts_to kc #pm wk ** S.pts_to pin #pm wp);
  let res = disp kc pin #pm #wk #wp #v;
  Trade.trans (sxrel true dsx pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp) (S.pts_to input #pm w);
  res
}

inline_for_extraction
fn sfx_some_parser (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k) (#ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (fb: Ghost.erased asn1_gen_items_lk)
  (#tfb: Type0) (dfb: Ghost.erased (idesc (dsnd fb) tfb)) (#ts: Type0) (dfx: Ghost.erased (fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts))
  (disp: fdisp key_k fb dfb dfx)
: aparser #ts #(AL.ady_fb key_k ls fb) (afb_rel fb dfb dfx) #asn1_weak_parser_kind (Mkparsertwin?.p (sfx_some kid key_k ls fb))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  AL.sfx_some_layout kid key_k ls fb w v;
  let kc, pin = sfx_split key_k (dfst v) (fun wp -> AL.pl_fb_parsed key_k ls fb wp v) input;
  with wk wp . assert (S.pts_to kc #pm wk ** S.pts_to pin #pm wp);
  let res = disp kc pin #pm #wk #wp #v;
  Trade.trans (afb_rel fb dfb dfx pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp) (S.pts_to input #pm w);
  res
}

(* The top-level ANY DEFINED BY content parsers *)

let adb_k_none (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Tot asn1_content_k
= ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf'

let adb_k_some (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Tot asn1_content_k
= ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf'

#push-options "--z3rlimit 64"

let adb_content_none (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (w: SB.bytes) (v: asn1_sequence_any_t_core prefix (AL.ady key_k ls))
: Lemma
  (requires parsed #asn1_weak_parser_kind (asn1_content_as_parser (adb_k_none ipd prefix kid key_k ls pf pf')) w v)
  (ensures seqa_parsed_core prefix (sfx_none kid key_k ls) w v /\ AL.sfx_shaped (sfx_none kid key_k ls))
= assert (
    asn1_content_as_parser (adb_k_none ipd prefix kid key_k ls pf pf') ==
    make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (ADB.adb_sfx_none kid key_k ls))
    by (T.norm [delta_only [`%adb_k_none; `%asn1_content_as_parser; `%ADB.adb_sfx_none; `%ADB.adb_fb; `%ADB.key_p; `%ADB.key_fp; `%Mkparsertwin?.p; `%Mkparsertwin?.fp]; zeta; iota; primops]; T.trefl ());
  seqa_t_eq prefix (AL.ady key_k ls);
  AL.sfx_none_shaped kid key_k ls

let adb_content_some (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (w: SB.bytes) (v: asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
: Lemma
  (requires parsed #asn1_weak_parser_kind (asn1_content_as_parser (adb_k_some ipd prefix kid key_k ls fb pf pf')) w v)
  (ensures seqa_parsed_core prefix (sfx_some kid key_k ls fb) w v /\ AL.sfx_shaped (sfx_some kid key_k ls fb))
= assert (
    asn1_content_as_parser (adb_k_some ipd prefix kid key_k ls fb pf pf') ==
    make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (ADB.adb_sfx_some kid key_k ls fb))
    by (T.norm [delta_only [`%adb_k_some; `%asn1_content_as_parser; `%ADB.adb_sfx_some; `%ADB.adb_fb; `%ADB.key_p; `%ADB.key_fp; `%Mkparsertwin?.p; `%Mkparsertwin?.fp]; zeta; iota; primops]; T.trefl ());
  seqa_t_eq prefix (AL.ady_fb key_k ls fb);
  AL.sfx_some_shaped kid key_k ls fb

#pop-options

let adb_rel_none_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#ts: Type0) (dsx: sxdesc key_k ls ts) (#t: Type0) (dpre: iadesc prefix ts t)
  (pm: perm) (x: t) (y: asn1_sequence_any_t_core prefix (AL.ady key_k ls))
: Lemma (crel true (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre) pm x y == iarel true dpre (sxrel true dsx) pm x y)
= assert (crel true (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre) pm x y == iarel true dpre (sxrel true dsx) pm x y)
    by (T.norm [delta_only [`%crel]; zeta; iota]; T.trefl ())

let adb_rel_some_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts) (#t: Type0) (dpre: iadesc prefix ts t)
  (pm: perm) (x: t) (y: asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
: Lemma (crel true (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre) pm x y == iarel true dpre (afb_rel fb dfb dfx) pm x y)
= assert (crel true (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre) pm x y == iarel true dpre (afb_rel fb dfb dfx) pm x y)
    by (T.norm [delta_only [`%crel; `%afb_rel; `%fbr; `%fbs]; zeta; iota]; T.trefl ())

inline_for_extraction
fn adb_none_parser (ipd: Ghost.erased id_decs) (prefix: Ghost.erased (asn1_gen_items_l ipd)) (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k)
  (ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk)))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton (Ghost.reveal kid)) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal ls))))
  (#ts: Type0) (dsx: Ghost.erased (sxdesc key_k ls ts)) (#t: Type0) (dpre: Ghost.erased (iadesc prefix ts t))
  (pp: saparser dpre (sxrel true dsx) (sfx_none kid key_k ls))
: aparser #t #(asn1_content_t (adb_k_none ipd prefix kid key_k ls pf pf')) (crel true (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre)) #asn1_weak_parser_kind (asn1_content_as_parser (adb_k_none ipd prefix kid key_k ls pf pf'))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let v' : Ghost.erased (asn1_sequence_any_t_core prefix (AL.ady key_k ls)) = Ghost.hide #(asn1_sequence_any_t_core prefix (AL.ady key_k ls)) (Ghost.reveal v);
  adb_content_none ipd prefix kid key_k ls pf pf' w v';
  let res = pp input #pm #w #v';
  adb_rel_none_eq ipd prefix kid key_k ls pf pf' dsx dpre pm res v';
  rewrite each (iarel true dpre (sxrel true dsx) pm res v') as (crel true (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre) pm res v);
  res
}

inline_for_extraction
fn adb_some_parser (ipd: Ghost.erased id_decs) (prefix: Ghost.erased (asn1_gen_items_l ipd)) (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k)
  (ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (fb: Ghost.erased asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton (Ghost.reveal kid)) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal ls))))
  (#tfb: Type0) (dfb: Ghost.erased (idesc (dsnd fb) tfb)) (#ts: Type0) (dfx: Ghost.erased (fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts)) (#t: Type0) (dpre: Ghost.erased (iadesc prefix ts t))
  (pp: saparser dpre (afb_rel fb dfb dfx) (sfx_some kid key_k ls fb))
: aparser #t #(asn1_content_t (adb_k_some ipd prefix kid key_k ls fb pf pf')) (crel true (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre)) #asn1_weak_parser_kind (asn1_content_as_parser (adb_k_some ipd prefix kid key_k ls fb pf pf'))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let v' : Ghost.erased (asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb)) = Ghost.hide #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb)) (Ghost.reveal v);
  adb_content_some ipd prefix kid key_k ls fb pf pf' w v';
  let res = pp input #pm #w #v';
  adb_rel_some_eq ipd prefix kid key_k ls fb pf pf' dfb dfx dpre pm res v';
  rewrite each (iarel true dpre (afb_rel fb dfb dfx) pm res v') as (crel true (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre) pm res v);
  res
}
