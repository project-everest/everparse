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

let consa_impl_eq (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids) (t: Type0)
: squash (asn1_items_any_impl_t (consa dk tl) t == (asn1_decorated_impl_t dk & asn1_items_any_impl_t tl t))
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

inline_for_extraction
let mkpair (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d)) (#ids: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l ids)) (#t: Type0)
  (r1: asn1_decorated_impl_t dk) (r2: asn1_items_any_impl_t tl t)
: Tot (asn1_items_any_impl_t (consa dk tl) t)
= coerce_eq (consa_impl_eq dk tl t) (r1, r2)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let items_any_rel_cons_eq (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#ids: _) (tl: asn1_gen_items_l ids)
  (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm)
  (r1: asn1_decorated_impl_t dk) (r2: asn1_items_any_impl_t tl sfxi) (y: asn1_sequence_any_t_core (consa dk tl) sfxs)
: Lemma (asn1_items_any_rel (consa dk tl) sfxr pm (mkpair dk tl r1 r2) y ==
    (asn1_decorated_rel dk pm r1 (avfst dk tl y) ** asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl y)))
= match tl with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ -> ()
#pop-options

let items_any_rel_nil_eq (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (pm: perm) (x: sfxi) (y: sfxs)
: Lemma (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr pm x y == sfxr pm x y)
= assert_norm (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr pm x y == sfxr pm x y)

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
let saparser (#i: _) (ls: asn1_gen_items_l i) (#sfxi: Type0) (#sfxs: Type) (sfxr: perm -> sfxi -> sfxs -> slprop) (sfx: parser_twin asn1_weak_parser_kind sfxs) : Type =
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#w: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (asn1_sequence_any_t_core ls sfxs)) ->
  stt (asn1_items_any_impl_t ls sfxi)
    (S.pts_to input #pm w ** pure (seqa_parsed_core ls sfx w v /\ AL.sfx_shaped sfx))
    (fun res -> asn1_items_any_rel ls sfxr pm res v ** Trade.trade (asn1_items_any_rel ls sfxr pm res v) (S.pts_to input #pm w))

inline_for_extraction
fn seqa_nil
  (#sfxi: Type0) (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (psfx: aparser #sfxi #sfxs sfxr #asn1_weak_parser_kind (Mkparsertwin?.p (Ghost.reveal sfx)))
: saparser #_ ASN1_GEN_ITEMS_NIL #sfxi #sfxs sfxr (Ghost.reveal sfx)
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  seqa_nil_core sfx w v;
  let v' : Ghost.erased sfxs = Ghost.hide #sfxs (Ghost.reveal v);
  let res : sfxi = psfx input #pm #w #v';
  items_any_rel_nil_eq sfxr pm res v';
  rewrite each (sfxr pm res v') as (asn1_items_any_rel ASN1_GEN_ITEMS_NIL sfxr pm res v);
  res
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn seqa_cons_absent
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#ids: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l ids))
  (#sfxi: Type0) (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (abs: PS.dabsent dk)
  (ptail: saparser tl sfxr sfx)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_any_t_core (consa dk tl) sfxs))
  requires S.pts_to input #pm w ** pure (PS.absent_core dk (avfst dk tl v) /\ seqa_parsed_core tl sfx w (avsnd dk tl v) /\ AL.sfx_shaped sfx)
  returns res: asn1_items_any_impl_t (consa dk tl) sfxi
  ensures asn1_items_any_rel (consa dk tl) sfxr pm res v ** Trade.trade (asn1_items_any_rel (consa dk tl) sfxr pm res v) (S.pts_to input #pm w)
{
  let r1 = abs pm (avfst dk tl v);
  let r2 = ptail input #pm #w #(avsnd dk tl v);
  PS.trade_emp_l (asn1_decorated_rel dk pm r1 (avfst dk tl v)) (asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v)) (S.pts_to input #pm w);
  let res = mkpair dk tl r1 r2;
  items_any_rel_cons_eq dk tl sfxr pm r1 r2 v;
  rewrite (asn1_decorated_rel dk pm r1 (avfst dk tl v) ** asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v))
    as (asn1_items_any_rel (consa dk tl) sfxr pm res v);
  rewrite (Trade.trade (asn1_decorated_rel dk pm r1 (avfst dk tl v) ** asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v)) (S.pts_to input #pm w))
    as (Trade.trade (asn1_items_any_rel (consa dk tl) sfxr pm res v) (S.pts_to input #pm w));
  res
}

inline_for_extraction
fn seqa_cons_present
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#ids: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l ids))
  (#sfxi: Type0) (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (pres: PS.dpresent dk)
  (ptail: saparser tl sfxr sfx)
  (n: SZ.t)
  (input: S.slice U8.t) (#pm: perm) (#w: Ghost.erased SB.bytes) (#v: Ghost.erased (asn1_sequence_any_t_core (consa dk tl) sfxs))
  requires S.pts_to input #pm w ** pure (SZ.v n <= Seq.length w /\ PS.item_parsed_core dk (Seq.slice w 0 (SZ.v n)) (avfst dk tl v) /\ seqa_parsed_core tl sfx (Seq.slice w (SZ.v n) (Seq.length w)) (avsnd dk tl v) /\ AL.sfx_shaped sfx)
  returns res: asn1_items_any_impl_t (consa dk tl) sfxi
  ensures asn1_items_any_rel (consa dk tl) sfxr pm res v ** Trade.trade (asn1_items_any_rel (consa dk tl) sfxr pm res v) (S.pts_to input #pm w)
{
  let in1, in2 = SU.split_trade input n;
  let r1 = pres in1 #pm #(Seq.slice w 0 (SZ.v n)) #(avfst dk tl v);
  let r2 = ptail in2 #pm #(Seq.slice w (SZ.v n) (Seq.length w)) #(avsnd dk tl v);
  Trade.prod
    (asn1_decorated_rel dk pm r1 (avfst dk tl v)) (S.pts_to in1 #pm (Seq.slice w 0 (SZ.v n)))
    (asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v)) (S.pts_to in2 #pm (Seq.slice w (SZ.v n) (Seq.length w)));
  Trade.trans
    (asn1_decorated_rel dk pm r1 (avfst dk tl v) ** asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v))
    (S.pts_to in1 #pm (Seq.slice w 0 (SZ.v n)) ** S.pts_to in2 #pm (Seq.slice w (SZ.v n) (Seq.length w)))
    (S.pts_to input #pm w);
  let res = mkpair dk tl r1 r2;
  items_any_rel_cons_eq dk tl sfxr pm r1 r2 v;
  rewrite (asn1_decorated_rel dk pm r1 (avfst dk tl v) ** asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v))
    as (asn1_items_any_rel (consa dk tl) sfxr pm res v);
  rewrite (Trade.trade (asn1_decorated_rel dk pm r1 (avfst dk tl v) ** asn1_items_any_rel tl sfxr pm r2 (avsnd dk tl v)) (S.pts_to input #pm w))
    as (Trade.trade (asn1_items_any_rel (consa dk tl) sfxr pm res v) (S.pts_to input #pm w));
  res
}

inline_for_extraction
fn seqa_cons
  (#s: Ghost.erased (Set.set asn1_id_t)) (#d: Ghost.erased asn1_decorator) (dk: Ghost.erased (asn1_decorated_k s d))
  (#ids: Ghost.erased id_decs) (tl: Ghost.erased (asn1_gen_items_l ids))
  (#sfxi: Type0) (#sfxs: Type) (#sfxr: perm -> sfxi -> sfxs -> slprop) (#sfx: Ghost.erased (parser_twin asn1_weak_parser_kind sfxs))
  (has_id: (id: asn1_id_t) -> Tot (b: bool { b == Set.mem id s }))
  (pres: PS.dpresent dk) (abs: PS.dabsent dk)
  (ptail: saparser tl sfxr sfx)
: saparser (consa (Ghost.reveal dk) (Ghost.reveal tl)) sfxr sfx
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
            seqa_cons_present dk tl pres ptail n input #pm #w #v
          }
          None -> {
            unreachable ()
          }
        }
      } else {
        seqa_cons_absent dk tl abs ptail input #pm #w #v
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

let adb_rel_single_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (pm: perm)
  (r: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k [(x, y)]) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (asn1_adb_rel key_k [(x, y)] pm r v == asn1_items_rel (dsnd y) pm r (AL.ady_head_val x y [] v ()))
= assert_norm (asn1_adb_rel key_k [(x, y)] pm r v == (let (| key, v |) = v in if key = key_of_lit key_k x then asn1_items_rel (dsnd y) pm r v else pure False))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let adb_rel_cons_inl_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady key_k ((x, y) :: hd2 :: tl2)) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (asn1_adb_rel key_k ((x, y) :: hd2 :: tl2) pm (Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) a) v ==
    asn1_items_rel (dsnd y) pm a (AL.ady_head_val x y (hd2 :: tl2) v ()))
= ()

#pop-options

let adb_rel_cons_inr_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (key: asn1_terminal_t key_k) (w: idlookup_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((x, y) :: hd2 :: tl2)))
: Lemma (asn1_adb_rel key_k ((x, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ==
    (if key = key_of_lit key_k x then pure False else asn1_adb_rel key_k (hd2 :: tl2) pm b (AL.ady_tail_val x y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ())))
= assert (asn1_adb_rel key_k ((x, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ==
    (if key = key_of_lit key_k x then pure False else asn1_adb_rel key_k (hd2 :: tl2) pm b (AL.ady_tail_val x y (hd2 :: tl2) ((| key, w |) <: AL.ady key_k ((x, y) :: hd2 :: tl2)) ())))
  by (T.norm [delta_only [`%asn1_adb_rel; `%AL.ady_tail_val; `%sxrel; `%legacy_sxdesc]; zeta; iota]; T.trefl ())

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let adb_rel_cons_inr_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (v: AL.ady key_k ((x, y) :: hd2 :: tl2)) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (asn1_adb_rel key_k ((x, y) :: hd2 :: tl2) pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) b) v ==
    asn1_adb_rel key_k (hd2 :: tl2) pm b (AL.ady_tail_val x y (hd2 :: tl2) v ()))
= let (| key, w |) = v in
  adb_rel_cons_inr_aux x y hd2 tl2 pm b key w
#pop-options

inline_for_extraction
let ndisp (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Type =
  (kc: S.slice U8.t) ->
  (pin: S.slice U8.t) ->
  (#pm: perm) ->
  (#wk: Ghost.erased SB.bytes) ->
  (#wp: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (AL.ady key_k ls)) ->
  stt (asn1_adb_suffix_impl_t key_k ls None)
    (S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk (dfst (Ghost.reveal v)) /\ AL.pl_parsed key_k ls wp v))
    (fun res -> asn1_adb_rel key_k ls pm res v ** Trade.trade (asn1_adb_rel key_k ls pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))

inline_for_extraction
let items_parser (y: asn1_gen_items_lk) : Type =
  aparser #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_sequence_t_core (dsnd y)) (asn1_items_rel (dsnd y)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE y))

inline_for_extraction
fn ndisp_nil (key_k: asn1_terminal_k)
: ndisp key_k []
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  AL.pl_nil key_k wp v;
  unreachable ()
}

inline_for_extraction
fn ndisp_single (key_k: asn1_terminal_k) (x: Ghost.erased (asn1_key_lit key_k)) (y: Ghost.erased asn1_gen_items_lk)
  (pitems: items_parser y)
: ndisp key_k [(Ghost.reveal x, Ghost.reveal y)]
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  pl_single x y wp v;
  AL.pl_head x y [] wp v;
  let res = pitems pin #pm #wp #(AL.ady_head_val x y [] v ());
  trade_frame_l (S.pts_to kc #pm wk) (asn1_items_rel (dsnd y) pm res (AL.ady_head_val x y [] v ())) (S.pts_to pin #pm wp);
  adb_rel_single_eq x y pm res v ();
  rewrite each (asn1_items_rel (dsnd y) pm res (AL.ady_head_val x y [] v ())) as (asn1_adb_rel key_k [(Ghost.reveal x, Ghost.reveal y)] pm res v);
  res
}

#push-options "--z3rlimit 64"

(* `hd2` and `tl2` are not erased: Custard must reduce
   `asn1_adb_suffix_impl_t key_k (hd2 :: tl2) _` by matching on them. *)
inline_for_extraction
fn ndisp_cons (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (x: asn1_key_lit key_k) (y: Ghost.erased asn1_gen_items_lk)
  (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pitems: items_parser y)
  (ptail: ndisp key_k (hd2 :: tl2))
: ndisp key_k ((x, Ghost.reveal y) :: hd2 :: tl2)
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  S.pts_to_len kc;
  AL.key_check_fl key_k (key_of_lit key_k x) (dfst v) wk;
  let mut poff = 0sz;
  let ok = In.validate_key_eq_fl key_k () x (S.len kc) kc poff;
  if ok {
    AL.pl_head x y (hd2 :: tl2) wp v;
    let r = pitems pin #pm #wp #(AL.ady_head_val x y (hd2 :: tl2) v ());
    trade_frame_l (S.pts_to kc #pm wk) (asn1_items_rel (dsnd y) pm r (AL.ady_head_val x y (hd2 :: tl2) v ())) (S.pts_to pin #pm wp);
    let res : asn1_adb_suffix_impl_t key_k ((x, Ghost.reveal y) :: hd2 :: tl2) None = Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) r;
    adb_rel_cons_inl_eq x y hd2 tl2 pm r v ();
    rewrite each (asn1_items_rel (dsnd y) pm r (AL.ady_head_val x y (hd2 :: tl2) v ())) as (asn1_adb_rel key_k ((x, Ghost.reveal y) :: hd2 :: tl2) pm res v);
    res
  } else {
    AL.pl_tail x y (hd2 :: tl2) wp v;
    let r = ptail kc pin #pm #wk #wp #(AL.ady_tail_val x y (hd2 :: tl2) v ());
    let res : asn1_adb_suffix_impl_t key_k ((x, Ghost.reveal y) :: hd2 :: tl2) None = Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) r;
    adb_rel_cons_inr_eq x y hd2 tl2 pm r v ();
    rewrite each (asn1_adb_rel key_k (hd2 :: tl2) pm r (AL.ady_tail_val x y (hd2 :: tl2) v ())) as (asn1_adb_rel key_k ((x, Ghost.reveal y) :: hd2 :: tl2) pm res v);
    res
  }
}

#pop-options

(* Dispatching on the key, with a fallback *)

(* `Mkdtuple2?._2` rather than `dsnd`, so that Custard can reduce this type *)
let fbt (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) : Type0 =
  asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb)

let fbs (fb: asn1_gen_items_lk) : Type =
  asn1_sequence_t_core (dsnd fb)

let fbr (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) : perm -> fbt key_k fb -> asn1_terminal_t key_k -> fbs fb -> slprop =
  fun pm (z: asn1_terminal_impl_t key_k & asn1_items_impl_t (Mkdtuple2?._2 fb)) key (v: asn1_sequence_t_core (dsnd fb)) ->
    asn1_terminal_rel key_k pm (fst z) key ** asn1_items_rel (dsnd fb) pm (snd z) v

let afb_rel (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) =
  asn1_adb_fb_rel key_k ls (fbt key_k fb) (fbs fb) (fbr key_k fb)

let afb_rel_nil_aux (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm)
  (rk: asn1_terminal_impl_t key_k) (ri: asn1_items_impl_t (Mkdtuple2?._2 fb)) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) []) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel key_k [] fb pm (rk, ri) ((| key, w |) <: AL.ady_fb key_k [] fb) ==
    (asn1_terminal_rel key_k pm rk key ** asn1_items_rel (dsnd fb) pm ri (AL.ady_fb_nil_val fb ((| key, w |) <: AL.ady_fb key_k [] fb))))
= assert (afb_rel key_k [] fb pm (rk, ri) ((| key, w |) <: AL.ady_fb key_k [] fb) ==
    (asn1_terminal_rel key_k pm rk key ** asn1_items_rel (dsnd fb) pm ri (AL.ady_fb_nil_val fb ((| key, w |) <: AL.ady_fb key_k [] fb))))
  by (T.norm [delta_only [`%afb_rel; `%asn1_adb_fb_rel; `%fbr; `%AL.ady_fb_nil_val; `%dsnd; `%fst; `%snd]; zeta; iota]; T.trefl ())

let afb_rel_nil_eq (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (pm: perm)
  (rk: asn1_terminal_impl_t key_k) (ri: asn1_items_impl_t (Mkdtuple2?._2 fb)) (v: AL.ady_fb key_k [] fb)
: Lemma (afb_rel key_k [] fb pm (rk, ri) v ==
    (asn1_terminal_rel key_k pm rk (dfst v) ** asn1_items_rel (dsnd fb) pm ri (AL.ady_fb_nil_val fb v)))
= let (| key, w |) = v in
  afb_rel_nil_aux fb pm rk ri key w

let afb_rel_single_inl_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) [(x, y)]) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel key_k [(x, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(fbt key_k fb) a) ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) == (if key = key_of_lit key_k x then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()) else pure False))
= assert (afb_rel key_k [(x, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(fbt key_k fb) a) ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) == (if key = key_of_lit key_k x then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()) else pure False))
  by (T.norm [delta_only [`%afb_rel; `%asn1_adb_fb_rel; `%AL.ady_fb_head_val; `%AL.ady_fb_tail_val]; zeta; iota]; T.trefl ())

let afb_rel_single_inr_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm) (b: fbt key_k fb) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) [(x, y)]) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel key_k [(x, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(fbt key_k fb) b) ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) == (if key = key_of_lit key_k x then pure False else fbr key_k fb pm b key (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()))))
= assert (afb_rel key_k [(x, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(fbt key_k fb) b) ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) == (if key = key_of_lit key_k x then pure False else fbr key_k fb pm b key (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb ((| key, w |) <: AL.ady_fb key_k [(x, y)] fb) ()))))
  by (T.norm [delta_only [`%afb_rel; `%asn1_adb_fb_rel; `%AL.ady_fb_head_val; `%AL.ady_fb_tail_val; `%AL.ady_fb_nil_val]; zeta; iota]; T.trefl ())

let afb_rel_cons_inl_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm) (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((x, y) :: hd2 :: tl2)) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel key_k ((x, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) a) ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) == (if key = key_of_lit key_k x then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ()) else pure False))
= assert (afb_rel key_k ((x, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) a) ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) == (if key = key_of_lit key_k x then asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ()) else pure False))
  by (T.norm [delta_only [`%afb_rel; `%asn1_adb_fb_rel; `%AL.ady_fb_head_val; `%AL.ady_fb_tail_val]; zeta; iota]; T.trefl ())

let afb_rel_cons_inr_aux (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm) (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) (key: asn1_terminal_t key_k) (w: idlookup_with_fallback_t key (asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ((x, y) :: hd2 :: tl2)) (asn1_sequence_t_core (dsnd fb)))
: Lemma (afb_rel key_k ((x, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) b) ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) == (if key = key_of_lit key_k x then pure False else afb_rel key_k (hd2 :: tl2) fb pm b (AL.ady_fb_tail_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ())))
= assert (afb_rel key_k ((x, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) b) ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) == (if key = key_of_lit key_k x then pure False else afb_rel key_k (hd2 :: tl2) fb pm b (AL.ady_fb_tail_val x y (hd2 :: tl2) fb ((| key, w |) <: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) ())))
  by (T.norm [delta_only [`%afb_rel; `%asn1_adb_fb_rel; `%fxrel; `%legacy_fxdesc; `%AL.ady_fb_head_val; `%AL.ady_fb_tail_val]; zeta; iota]; T.trefl ())

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let afb_rel_single_inl_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k [(x, y)] fb) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (afb_rel key_k [(x, y)] fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(fbt key_k fb) a) v == asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val x y [] fb v ()))
= let (| key, w |) = v in
  afb_rel_single_inl_aux x y fb pm a key w

let afb_rel_single_inr_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (pm: perm)
  (b: fbt key_k fb) (v: AL.ady_fb key_k [(x, y)] fb) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (afb_rel key_k [(x, y)] fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(fbt key_k fb) b) v == fbr key_k fb pm b (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb v ())))
= let (| key, w |) = v in
  afb_rel_single_inr_aux x y fb pm b key w

let afb_rel_cons_inl_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (a: asn1_items_impl_t (Mkdtuple2?._2 y)) (v: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) (sq: squash (dfst v == key_of_lit key_k x))
: Lemma (afb_rel key_k ((x, y) :: hd2 :: tl2) fb pm (Inl #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) a) v == asn1_items_rel (dsnd y) pm a (AL.ady_fb_head_val x y (hd2 :: tl2) fb v ()))
= let (| key, w |) = v in
  afb_rel_cons_inl_aux x y hd2 tl2 fb pm a key w

let afb_rel_cons_inr_eq (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (pm: perm)
  (b: asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) (v: AL.ady_fb key_k ((x, y) :: hd2 :: tl2) fb) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (afb_rel key_k ((x, y) :: hd2 :: tl2) fb pm (Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) b) v == afb_rel key_k (hd2 :: tl2) fb pm b (AL.ady_fb_tail_val x y (hd2 :: tl2) fb v ()))
= let (| key, w |) = v in
  afb_rel_cons_inr_aux x y hd2 tl2 fb pm b key w

let dfst_fb_tail_val (#key_k: asn1_terminal_k) (x: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: AL.ady_fb key_k ((x, y) :: tl) fb) (sq: squash (dfst v <> key_of_lit key_k x))
: Lemma (dfst (AL.ady_fb_tail_val x y tl fb v ()) == dfst v)
= ()
#pop-options

inline_for_extraction
let fdisp (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) : Type =
  (kc: S.slice U8.t) ->
  (pin: S.slice U8.t) ->
  (#pm: perm) ->
  (#wk: Ghost.erased SB.bytes) ->
  (#wp: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (AL.ady_fb key_k ls fb)) ->
  stt (asn1_adb_suffix_impl_t key_k ls (Some (fbt key_k fb)))
    (S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk (dfst (Ghost.reveal v)) /\ AL.pl_fb_parsed key_k ls fb wp v))
    (fun res -> afb_rel key_k ls fb pm res v ** Trade.trade (afb_rel key_k ls fb pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))

inline_for_extraction
let key_parser (key_k: asn1_terminal_k) : Type =
  aparser #(asn1_terminal_impl_t key_k) #(asn1_terminal_t key_k) (asn1_terminal_rel key_k) #asn1_weak_parser_kind (asn1_terminal_as_parser key_k)

inline_for_extraction
fn fb_core (key_k: asn1_terminal_k) (fb: Ghost.erased asn1_gen_items_lk)
  (pkey: key_parser key_k) (pitems: items_parser fb)
  (kc: S.slice U8.t) (pin: S.slice U8.t) (#pm: perm) (#wk: Ghost.erased SB.bytes) (#wp: Ghost.erased SB.bytes)
  (key: Ghost.erased (asn1_terminal_t key_k)) (v: Ghost.erased (asn1_sequence_t_core (dsnd fb)))
  requires S.pts_to kc #pm wk ** S.pts_to pin #pm wp ** pure (parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk key /\ parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE fb)) wp v)
  returns res: fbt key_k fb
  ensures fbr key_k fb pm res key v ** Trade.trade (fbr key_k fb pm res key v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp)
{
  let rk = pkey kc #pm #wk #key;
  let ri = pitems pin #pm #wp #v;
  Trade.prod
    (asn1_terminal_rel key_k pm rk key) (S.pts_to kc #pm wk)
    (asn1_items_rel (dsnd fb) pm ri v) (S.pts_to pin #pm wp);
  let res : fbt key_k fb = (rk, ri);
  rewrite (asn1_terminal_rel key_k pm rk key ** asn1_items_rel (dsnd fb) pm ri v)
    as (fbr key_k fb pm res key v);
  rewrite (Trade.trade (asn1_terminal_rel key_k pm rk key ** asn1_items_rel (dsnd fb) pm ri v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp))
    as (Trade.trade (fbr key_k fb pm res key v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp));
  res
}

inline_for_extraction
fn fdisp_nil (key_k: asn1_terminal_k) (fb: Ghost.erased asn1_gen_items_lk)
  (pkey: key_parser key_k) (pitems: items_parser fb)
: fdisp key_k [] fb
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  AL.pl_fb_nil fb wp v;
  let res = fb_core key_k fb pkey pitems kc pin (dfst v) (AL.ady_fb_nil_val fb v);
  afb_rel_nil_eq fb pm (fst res) (snd res) v;
  rewrite each (fbr key_k fb pm res (dfst v) (AL.ady_fb_nil_val fb v)) as (afb_rel key_k [] fb pm res v);
  res
}

#push-options "--z3rlimit 64"

inline_for_extraction
fn fdisp_single (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (x: asn1_key_lit key_k) (y: Ghost.erased asn1_gen_items_lk) (fb: Ghost.erased asn1_gen_items_lk)
  (pitems: items_parser y)
  (pkey: key_parser key_k) (pfb: items_parser fb)
: fdisp key_k [(x, Ghost.reveal y)] fb
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  S.pts_to_len kc;
  AL.key_check_fl key_k (key_of_lit key_k x) (dfst v) wk;
  let mut poff = 0sz;
  let ok = In.validate_key_eq_fl key_k () x (S.len kc) kc poff;
  if ok {
    AL.pl_fb_head x y [] fb wp v;
    let r = pitems pin #pm #wp #(AL.ady_fb_head_val x y [] fb v ());
    trade_frame_l (S.pts_to kc #pm wk) (asn1_items_rel (dsnd y) pm r (AL.ady_fb_head_val x y [] fb v ())) (S.pts_to pin #pm wp);
    let res : asn1_adb_suffix_impl_t key_k [(x, Ghost.reveal y)] (Some (fbt key_k fb)) = Inl #_ #(fbt key_k fb) r;
    afb_rel_single_inl_eq x y fb pm r v ();
    rewrite each (asn1_items_rel (dsnd y) pm r (AL.ady_fb_head_val x y [] fb v ())) as (afb_rel key_k [(x, Ghost.reveal y)] fb pm res v);
    res
  } else {
    AL.pl_fb_tail x y [] fb wp v;
    AL.pl_fb_nil fb wp (AL.ady_fb_tail_val x y [] fb v ());
    dfst_fb_tail_val x y [] fb v ();
    let r = fb_core key_k fb pkey pfb kc pin (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb v ()));
    let res : asn1_adb_suffix_impl_t key_k [(x, Ghost.reveal y)] (Some (fbt key_k fb)) = Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) r;
    afb_rel_single_inr_eq x y fb pm r v ();
    rewrite each (fbr key_k fb pm r (dfst v) (AL.ady_fb_nil_val fb (AL.ady_fb_tail_val x y [] fb v ()))) as (afb_rel key_k [(x, Ghost.reveal y)] fb pm res v);
    res
  }
}

inline_for_extraction
fn fdisp_cons (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (x: asn1_key_lit key_k) (y: Ghost.erased asn1_gen_items_lk)
  (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: Ghost.erased asn1_gen_items_lk)
  (pitems: items_parser y)
  (ptail: fdisp key_k (hd2 :: tl2) fb)
: fdisp key_k ((x, Ghost.reveal y) :: hd2 :: tl2) fb
= (kc: _) (pin: _) (#pm: _) (#wk: _) (#wp: _) (#v: _)
{
  S.pts_to_len kc;
  AL.key_check_fl key_k (key_of_lit key_k x) (dfst v) wk;
  let mut poff = 0sz;
  let ok = In.validate_key_eq_fl key_k () x (S.len kc) kc poff;
  if ok {
    AL.pl_fb_head x y (hd2 :: tl2) fb wp v;
    let r = pitems pin #pm #wp #(AL.ady_fb_head_val x y (hd2 :: tl2) fb v ());
    trade_frame_l (S.pts_to kc #pm wk) (asn1_items_rel (dsnd y) pm r (AL.ady_fb_head_val x y (hd2 :: tl2) fb v ())) (S.pts_to pin #pm wp);
    let res : asn1_adb_suffix_impl_t key_k ((x, Ghost.reveal y) :: hd2 :: tl2) (Some (fbt key_k fb)) = Inl #_ #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (fbt key_k fb))) r;
    afb_rel_cons_inl_eq x y hd2 tl2 fb pm r v ();
    rewrite each (asn1_items_rel (dsnd y) pm r (AL.ady_fb_head_val x y (hd2 :: tl2) fb v ())) as (afb_rel key_k ((x, Ghost.reveal y) :: hd2 :: tl2) fb pm res v);
    res
  } else {
    AL.pl_fb_tail x y (hd2 :: tl2) fb wp v;
    dfst_fb_tail_val x y (hd2 :: tl2) fb v ();
    let r = ptail kc pin #pm #wk #wp #(AL.ady_fb_tail_val x y (hd2 :: tl2) fb v ());
    let res : asn1_adb_suffix_impl_t key_k ((x, Ghost.reveal y) :: hd2 :: tl2) (Some (fbt key_k fb)) = Inr #(asn1_items_impl_t (Mkdtuple2?._2 y)) r;
    afb_rel_cons_inr_eq x y hd2 tl2 fb pm r v ();
    rewrite each (afb_rel key_k (hd2 :: tl2) fb pm r (AL.ady_fb_tail_val x y (hd2 :: tl2) fb v ())) as (afb_rel key_k ((x, Ghost.reveal y) :: hd2 :: tl2) fb pm res v);
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
let sfx_none_aparser (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Type =
  aparser #(asn1_adb_suffix_impl_t key_k ls None) #(AL.ady key_k ls) (asn1_adb_rel key_k ls) #asn1_weak_parser_kind (Mkparsertwin?.p (sfx_none kid key_k ls))

inline_for_extraction
let sfx_some_aparser (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) : Type =
  aparser #(asn1_adb_suffix_impl_t key_k ls (Some (fbt key_k fb))) #(AL.ady_fb key_k ls fb) (afb_rel key_k ls fb) #asn1_weak_parser_kind (Mkparsertwin?.p (sfx_some kid key_k ls fb))

inline_for_extraction
fn sfx_none_parser (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k) (ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk)))
  (disp: ndisp key_k ls)
: sfx_none_aparser kid key_k ls
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  AL.sfx_none_layout kid key_k ls w v;
  let kc, pin = sfx_split key_k (dfst v) (fun wp -> AL.pl_parsed key_k ls wp v) input;
  with wk wp . assert (S.pts_to kc #pm wk ** S.pts_to pin #pm wp);
  let res = disp kc pin #pm #wk #wp #v;
  Trade.trans (asn1_adb_rel key_k ls pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp) (S.pts_to input #pm w);
  res
}

inline_for_extraction
fn sfx_some_parser (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k) (ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (fb: Ghost.erased asn1_gen_items_lk)
  (disp: fdisp key_k ls fb)
: sfx_some_aparser kid key_k ls fb
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  AL.sfx_some_layout kid key_k ls fb w v;
  let kc, pin = sfx_split key_k (dfst v) (fun wp -> AL.pl_fb_parsed key_k ls fb wp v) input;
  with wk wp . assert (S.pts_to kc #pm wk ** S.pts_to pin #pm wp);
  let res = disp kc pin #pm #wk #wp #v;
  Trade.trans (afb_rel key_k ls fb pm res v) (S.pts_to kc #pm wk ** S.pts_to pin #pm wp) (S.pts_to input #pm w);
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
  (pm: perm) (x: asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls None)) (y: asn1_sequence_any_t_core prefix (AL.ady key_k ls))
: Lemma (asn1_content_rel (adb_k_none ipd prefix kid key_k ls pf pf') pm x y == asn1_items_any_rel prefix (asn1_adb_rel key_k ls) pm x y)
= assert (asn1_content_rel (adb_k_none ipd prefix kid key_k ls pf pf') pm x y == asn1_items_any_rel prefix (asn1_adb_rel key_k ls) pm x y)
    by (T.norm [delta_only [`%adb_k_none; `%asn1_content_rel; `%crel; `%legacy_cdesc; `%asn1_items_any_rel; `%asn1_adb_rel]; zeta; iota]; T.trefl ())

let adb_rel_some_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (pm: perm) (x: asn1_items_any_impl_t prefix (asn1_adb_suffix_impl_t key_k ls (Some (fbt key_k fb)))) (y: asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb))
: Lemma (asn1_content_rel (adb_k_some ipd prefix kid key_k ls fb pf pf') pm x y == asn1_items_any_rel prefix (afb_rel key_k ls fb) pm x y)
= assert (asn1_content_rel (adb_k_some ipd prefix kid key_k ls fb pf pf') pm x y == asn1_items_any_rel prefix (afb_rel key_k ls fb) pm x y)
    by (T.norm [delta_only [`%adb_k_some; `%asn1_content_rel; `%afb_rel; `%fbt; `%fbs; `%fbr; `%crel; `%legacy_cdesc; `%asn1_items_any_rel; `%asn1_adb_fb_rel; `%asn1_items_rel]; zeta; iota]; T.trefl ())

inline_for_extraction
let adb_none_aparser (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Type
= let k = adb_k_none ipd prefix kid key_k ls pf pf' in
  aparser #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) #asn1_weak_parser_kind (asn1_content_as_parser k)

inline_for_extraction
let adb_some_aparser (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Type
= let k = adb_k_some ipd prefix kid key_k ls fb pf pf' in
  aparser #(asn1_content_impl_t k) #(asn1_content_t k) (asn1_content_rel k) #asn1_weak_parser_kind (asn1_content_as_parser k)

inline_for_extraction
fn adb_none_parser (ipd: Ghost.erased id_decs) (prefix: Ghost.erased (asn1_gen_items_l ipd)) (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k)
  (ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk)))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton (Ghost.reveal kid)) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal ls))))
  (pp: saparser prefix (asn1_adb_rel key_k ls) (sfx_none kid key_k ls))
: adb_none_aparser ipd prefix kid key_k ls pf pf'
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let v' : Ghost.erased (asn1_sequence_any_t_core prefix (AL.ady key_k ls)) = Ghost.hide #(asn1_sequence_any_t_core prefix (AL.ady key_k ls)) (Ghost.reveal v);
  adb_content_none ipd prefix kid key_k ls pf pf' w v';
  let res = pp input #pm #w #v';
  adb_rel_none_eq ipd prefix kid key_k ls pf pf' pm res v';
  rewrite each (asn1_items_any_rel prefix (asn1_adb_rel key_k ls) pm res v') as (asn1_content_rel (adb_k_none ipd prefix kid key_k ls pf pf') pm res v);
  res
}

inline_for_extraction
fn adb_some_parser (ipd: Ghost.erased id_decs) (prefix: Ghost.erased (asn1_gen_items_l ipd)) (kid: Ghost.erased asn1_id_t) (key_k: Ghost.erased asn1_terminal_k)
  (ls: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (fb: Ghost.erased asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton (Ghost.reveal kid)) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal ls))))
  (pp: saparser prefix (afb_rel key_k ls fb) (sfx_some kid key_k ls fb))
: adb_some_aparser ipd prefix kid key_k ls fb pf pf'
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  let v' : Ghost.erased (asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb)) = Ghost.hide #(asn1_sequence_any_t_core prefix (AL.ady_fb key_k ls fb)) (Ghost.reveal v);
  adb_content_some ipd prefix kid key_k ls fb pf pf' w v';
  let res = pp input #pm #w #v';
  adb_rel_some_eq ipd prefix kid key_k ls fb pf pf' pm res v';
  rewrite each (asn1_items_any_rel prefix (afb_rel key_k ls fb) pm res v') as (asn1_content_rel (adb_k_some ipd prefix kid key_k ls fb pf pf') pm res v);
  res
}
