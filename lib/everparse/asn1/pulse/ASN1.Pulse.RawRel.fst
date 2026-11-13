module ASN1.Pulse.RawRel
#lang-pulse

(* Raw Pulse representations of ASN.1 DER values: the relation
   `raw_rel k pm x w` between a Pulse representation `x: asn1_impl_t k` and
   the bytes `w` it is written as, ignoring all the semantic constraints of
   `k`. It only states the ownership of the slices, references and mixed
   lists reachable from `x`, with fraction `pm`:
   - a string, time or object identifier leaf is a slice of arbitrary bytes;
   - a big INTEGER is a slice of arbitrary bytes, a small one any `int64`;
   - a BIT STRING is an arbitrary number of unused bits and bytes;
   - an ANY is a slice of arbitrary bytes;
   - an OPTIONAL or DEFAULT component, a CHOICE alternative, a SEQUENCE or SET
     are written as their Pulse representation says, whatever the schema
     constraints on their contents (DEFAULT values, restrictions, sizes);
   - a SEQUENCE OF or SET OF is a mixed list, whose serialized chunks are
     sequences of TLVs (`p_raw`), in any order.
   The components of a SET are written sorted by tag, and the elements of a
   SET OF sorted by encoding, using the on-the-fly insertion sort of
   `ASN1.Pulse.SortedInsert`: thus neither the order of the components in
   the schema nor the order of the elements in the input matter.
   - an ANY DEFINED BY is its prefix components, then either the payload
     selected by one of the key literals, written after the TLV of that
     literal, or the fallback key (written like any terminal) and its
     payload.

   The raw writer (`ASN1.Pulse.RawWriter`) writes `w`; validating `w`
   against `k` then checks all the constraints of `k` at once. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module I64 = FStar.Int64
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module PB = LowParse.PulseParse.Base
module It = LowParse.PulseParse.Iterator
module W = LowParse.Pulse.R2L
module RS = ASN1.Pulse.RelShare
module INT = ASN1.Spec.Content.INTEGER
module Conf = ASN1.Spec.Conformance
module Ser = ASN1.Spec.Serializer
module PS = ASN1.Pulse.ParseSequence
module T = FStar.Tactics.V2
module SI = ASN1.Pulse.SortedInsert
module WA = ASN1.Pulse.WriteAdb
module PA = ASN1.Pulse.ParseAdb
module In = ASN1.Pulse.Interpreter

let bprel (t: Type0) = prel t SB.bytes

let id_enc (w: SB.bytes) : GTot SB.bytes = w

(* Combinators *)

let raw_slice : bprel (S.slice U8.t) = prel_slice_ser id_enc

let raw_pure (#t: Type0) (f: t -> GTot SB.bytes) (_: perm) (x: t) (w: SB.bytes) : slprop =
  pure (w == f x)

let raw_false (t: Type0) (_: perm) (_: t) (_: SB.bytes) : slprop = pure False

let raw_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (pm: perm) (x: t) (w: SB.bytes) : slprop =
  exists* c . r pm x c ** pure (w == enc_tlv id true c)

let raw_cat (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (x: t1 & t2) (w: SB.bytes) : slprop =
  exists* w1 w2 . r1 pm (fst x) w1 ** r2 pm (snd x) w2 ** pure (w == Seq.append w1 w2)

(* `w2` with the frame `w1` inserted at its sorted position *)
let raw_ins (lt: SI.lt_t) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (x: t1 & t2) (w: SB.bytes) : slprop =
  exists* w1 w2 . r1 pm (fst x) w1 ** r2 pm (snd x) w2 ** pure (w == SI.ins lt w1 w2)

(* SET components are sorted by tag, SEQUENCE components are not sorted *)
let raw_join (srt: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (x: t1 & t2) (w: SB.bytes) : slprop =
  if srt then raw_ins SI.lt_tag r1 r2 pm x w else raw_cat r1 r2 pm x w

let raw_opt (#t: Type0) (r: bprel t) (pm: perm) (x: option t) (w: SB.bytes) : slprop =
  match x with
  | None -> pure (w == Seq.empty)
  | Some a -> r pm a w

(* An optional value whose bytes are dropped when they are exactly `d`: a
   DEFAULT component whose value is explicitly the default one is absent *)
let raw_opt_nd (d: SB.bytes) (#t: Type0) (r: bprel t) (pm: perm) (x: option t) (w: SB.bytes) : slprop =
  match x with
  | None -> pure (w == Seq.empty)
  | Some a -> exists* c . r pm a c ** pure ((c == d ==> w == Seq.empty) /\ (~ (c == d) ==> w == c))

(* `w` preceded by the constant `e` *)
let raw_pre (e: SB.bytes) (#t: Type0) (r: bprel t) (pm: perm) (x: t) (w: SB.bytes) : slprop =
  exists* w' . r pm x w' ** pure (w == Seq.append e w')

(* A KEEP-BYTES node: the value, written as usual, and the ownership of its
   bytes (if any), which the writer ignores *)
let keep_own (pm: perm) (r: option (S.slice U8.t)) : slprop =
  match r with
  | None -> emp
  | Some sl -> exists* (b: Seq.seq U8.t) . S.pts_to sl #pm b

let raw_keep (#t: Type0) (r: bprel t) (pm: perm) (x: kept t) (w: SB.bytes) : slprop =
  r (pm /. 2.0R) x.kval w ** keep_own (pm /. 2.0R) x.kraw

let raw_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (x: either t1 t2) (w: SB.bytes) : slprop =
  match x with
  | Inl a -> r1 pm a w
  | Inr b -> r2 pm b w

(* Serialized chunks of mixed lists: sequences of TLVs, each related to its
   own bytes *)

let any_enc (v: asn1_value) : GTot SB.bytes = asn1_value_enc v

let any_enc_injective () : Lemma (SC.synth_injective any_enc) =
  Classical.forall_intro_2 (fun v1 v2 -> Classical.move_requires (asn1_value_enc_inj v1) v2)

let p_any : SB.parser asn1_strong_parser_kind asn1_value = asn1_as_parser ASN1_ANY_ILC

let p_raw : SB.parser asn1_strong_parser_kind SB.bytes =
  any_enc_injective ();
  SC.parse_synth p_any any_enc

let p_raw_consumed (w: SB.bytes) (y: SB.bytes)
: Lemma (requires (PB.pts_to_parsed_prop p_raw w y)) (ensures (id_enc y == w))
= any_enc_injective ();
  SC.parse_synth_eq p_any any_enc w;
  let Some (v, n) = SB.parse p_any w in
  Ser.asn1_as_parser_consumed ASN1_ANY_ILC w;
  assert (Seq.equal (Seq.slice w 0 n) w)

let raw_ml (#t: Type0) (r: bprel t) (pm: perm) (x: ml t) (w: SB.bytes) : slprop =
  exists* (l: list SB.bytes) .
    It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x l **
    pure (w == W.enc_list id_enc l)

let raw_ml_sorted (#t: Type0) (r: bprel t) (pm: perm) (x: ml t) (w: SB.bytes) : slprop =
  exists* (l: list SB.bytes) .
    It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x l **
    pure (w == SI.sort_list SI.lt_lex id_enc l)

(* Leaves *)

let i64_int (x: I64.t) : Tot (asn1_integer_t 8) =
  assert_norm (pow2 63 == 9223372036854775808);
  assert_norm (pow2 (8 * 8 - 1) == 9223372036854775808);
  I64.v x

let i64_enc (x: I64.t) : GTot SB.bytes = integer_enc 8 (i64_int x)

let raw_i64 : bprel I64.t = raw_pure i64_enc

let raw_int (pm: perm) (x: asn1_int_impl) (w: SB.bytes) : slprop =
  match x with
  | Small i -> pure (w == i64_enc i)
  | Big s -> raw_slice pm s w

let raw_integer (bound: pos) : Tot (bprel (integer_impl_t bound)) =
  if small_integer bound then raw_i64 else raw_int

let raw_bitstring (pm: perm) (x: asn1_bitstring_impl) (w: SB.bytes) : slprop =
  exists* b . S.pts_to x.bytes #pm b ** pure (w == Seq.append (W.enc_byte x.unused) b)

let null_enc (_: unit) : GTot SB.bytes = Seq.empty

let raw_leaf (k: leaf_k) : Tot (bprel (asn1_terminal_impl_t k)) =
  match k returns bprel (asn1_terminal_impl_t k) with
  | ASN1_BOOLEAN -> raw_pure boolean_enc
  | ASN1_NULL -> raw_pure null_enc
  | ASN1_INTEGER bound -> raw_integer bound
  | ASN1_BITSTRING -> raw_bitstring
  | ASN1_OCTETSTRING
  | ASN1_PRINTABLESTRING
  | ASN1_UTF8STRING
  | ASN1_IA5STRING
  | ASN1_VISIBLESTRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_TELETEXSTRING
  | ASN1_NUMERICSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_OID
  | ASN1_RELATIVE_OID
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME -> raw_slice

(* Terminals, with their identifier *)

let rec raw_terminal_rel (id: asn1_id_t) (k: asn1_terminal_k) (pm: perm) (x: asn1_terminal_impl_t k) (w: SB.bytes) : Tot slprop (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> let x' : asn1_terminal_impl_t k2 = coerce_eq () x in raw_tlv id (raw_terminal_rel id2 k2) pm x' w
  | _ -> raw_tlv id (raw_leaf k) pm x w

(* DEFAULT components: when the default literal can be compared at runtime
   (`In.adb_key_supported`), an explicit default value is not written, as
   in DER *)
let raw_default_rel (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k) : bprel (option (asn1_terminal_impl_t k)) =
  if In.adb_key_supported k
  then raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)
  else raw_opt (raw_terminal_rel id0 k)

let default_rel_nd (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k)
: Lemma (requires (In.adb_key_supported k))
  (ensures (raw_default_rel id0 k defl == raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)))
= ()

let default_rel_opt (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k)
: Lemma (requires (~ (In.adb_key_supported k)))
  (ensures (raw_default_rel id0 k defl == raw_opt (raw_terminal_rel id0 k)))
= ()

(* The whole schema, along an impl descriptor (`ASN1.Pulse.Rel.adesc`): a
   VIEW node relates a value through its view *)

let raw_view (#t #ty: Type0) (r: bprel t) (view: ty -> t) (pm: perm) (x: ty) (w: SB.bytes) : slprop =
  r pm (view x) w

let rec raw_crel (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (pm: perm) (x: t) (w: SB.bytes) : Tot slprop (decreases d) =
  match d with
  | CD_RESTRICTED k' _ -> raw_terminal_rel id k' pm x w
  | CD_TERMINAL k' -> raw_terminal_rel id k' pm x w
  | CD_SEQUENCE _ di -> raw_tlv id (raw_irel false di) pm x w
  | CD_SET _ _ _ di -> raw_tlv id (raw_irel true di) pm x w
  | CD_SEQUENCE_OF _ d' -> raw_tlv id (raw_ml (raw_arel d')) pm x w
  | CD_SET_OF _ d' -> raw_tlv id (raw_ml_sorted (raw_arel d')) pm x w
  | CD_PREFIXED d' -> raw_tlv id (raw_arel d') pm x w
  | CD_ADB_NONE _ _ kid _ _ _ _ dsx dpre -> raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx)) pm x w
  | CD_ADB_SOME _ _ kid key_k _ _ _ _ dfb dfx dpre ->
    raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb)))) pm x w
  | CD_VIEW d' _ view _ _ -> raw_crel id d' pm (view x) w

and raw_sxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
  (pm: perm) (x: t) (w: SB.bytes)
: Tot slprop (decreases d)
= match d with
  | SX_NIL _ -> pure False
  | SX_SINGLE _ key' _ di -> raw_pre (WA.raw_key_enc kid key_k key') (raw_irel false di) pm x w
  | SX_CONS _ key' _ di dtl -> raw_either (raw_pre (WA.raw_key_enc kid key_k key') (raw_irel false di)) (raw_sxrel kid dtl) pm x w

and raw_fxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (fbr: bprel fbt) (pm: perm) (x: t) (w: SB.bytes)
: Tot slprop (decreases d)
= match d with
  | FX_NIL _ -> fbr pm x w
  | FX_SINGLE _ key' _ di -> raw_either (raw_pre (WA.raw_key_enc kid key_k key') (raw_irel false di)) fbr pm x w
  | FX_CONS _ key' _ di dtl -> raw_either (raw_pre (WA.raw_key_enc kid key_k key') (raw_irel false di)) (raw_fxrel kid dtl fbr) pm x w

and raw_iarel (#ids: _) (#items: asn1_gen_items_l ids) (#sfx: Type0) (#t: Type0) (d: iadesc items sfx t) (sr: bprel sfx) (pm: perm) (x: t) (w: SB.bytes)
: Tot slprop (decreases d)
= match d with
  | IA_NIL -> sr pm x w
  | IA_SINGLE dd -> raw_cat (raw_drel dd) sr pm x w
  | IA_CONS dd dtl -> raw_cat (raw_drel dd) (raw_iarel dtl sr) pm x w

and raw_lcrel (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t) (pm: perm) (x: t) (w: SB.bytes) : Tot slprop (decreases d) =
  match d with
  | LC_NIL -> pure False
  | LC_SINGLE id' cd -> raw_crel id' cd pm x w
  | LC_CONS id' cd dtl -> raw_either (raw_crel id' cd) (raw_lcrel dtl) pm x w

and raw_arel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (w: SB.bytes) : Tot slprop (decreases d) =
  match d with
  | D_ILC id cd -> raw_crel id cd pm x w
  | D_CHOICE _ _ ld -> raw_lcrel ld pm x w
  | D_ANY -> raw_slice pm x w
  | D_VIEW d' _ view _ _ -> raw_arel d' pm (view x) w
  | D_KEEP #_ #_ #t' d' _ ->
    let x' : kept t' = x in
    raw_arel d' (pm /. 2.0R) x'.kval w ** keep_own (pm /. 2.0R) x'.kraw

and raw_drel (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (pm: perm) (x: t) (w: SB.bytes) : Tot slprop (decreases d) =
  match d with
  | DD_PLAIN d' -> raw_arel d' pm x w
  | DD_OPTION d' -> raw_opt (raw_arel d') pm x w
  | DD_DEFAULT id0 #k defl -> raw_default_rel id0 k defl pm x w
  | DD_DEFAULT_RESTRICTED id0 #k _ defl -> raw_default_rel id0 k defl pm x w
  | DD_VIEW d' _ view _ _ -> raw_drel d' pm (view x) w

and raw_irel (srt: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (d: idesc items t) (pm: perm) (x: t) (w: SB.bytes) : Tot slprop (decreases d) =
  match d with
  | ID_NIL -> pure (w == Seq.empty)
  | ID_SINGLE dd -> raw_drel dd pm x w
  | ID_CONS dd dtl -> raw_join srt (raw_drel dd) (raw_irel srt dtl) pm x w

(* The fallback of an ANY DEFINED BY: the key, then the payload *)

let raw_dfbr (kid: asn1_id_t) (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
: bprel (asn1_terminal_impl_t key_k & tfb)
= raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb)

(* The relations of today's representations: those of the legacy descriptors *)

let raw_content_rel (id: asn1_id_t) (k: asn1_content_k) : bprel (asn1_content_impl_t k) = raw_crel id (legacy_cdesc k)

let raw_adb_rel (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: bprel (asn1_adb_suffix_impl_t key_k ls None)
= raw_sxrel kid (legacy_sxdesc key_k ls)

let raw_adb_fb_rel (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fbt: Type0) (fbr: bprel fbt)
: bprel (asn1_adb_suffix_impl_t key_k ls (Some fbt))
= raw_fxrel kid (legacy_fxdesc key_k ls fbt) fbr

let raw_items_any_rel (#ids: _) (items: asn1_gen_items_l ids) (#sfx: Type0) (sr: bprel sfx) : bprel (asn1_items_any_impl_t items sfx) =
  raw_iarel (legacy_iadesc items sfx) sr

let raw_lc_rel (lc: list (asn1_id_t & asn1_content_k)) : bprel (asn1_lc_impl_t lc) = raw_lcrel (legacy_lcdesc lc)

let raw_rel (#s: _) (k: asn1_k s) : bprel (asn1_impl_t k) = raw_arel (legacy_adesc k)

let raw_dec_rel (#s: _) (#d: _) (dk: asn1_decorated_k s d) : bprel (asn1_decorated_impl_t dk) = raw_drel (legacy_ddesc dk)

let raw_items_rel (srt: bool) (#ids: _) (items: asn1_gen_items_l ids) : bprel (asn1_items_impl_t items) = raw_irel srt (legacy_idesc items)

let raw_fbr (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) : bprel (PA.fbt key_k fb) =
  raw_cat (raw_terminal_rel kid key_k) (raw_items_rel false (dsnd fb))

let raw_afb_rel (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: bprel (asn1_adb_suffix_impl_t key_k ls (Some (PA.fbt key_k fb)))
= raw_adb_fb_rel kid key_k ls (PA.fbt key_k fb) (raw_fbr kid key_k fb)

(* Sharing and gathering *)

let share_t (#t: Type0) (r: bprel t) : Type = RS.share_t #t #SB.bytes r
let gather_t (#t: Type0) (r: bprel t) : Type = RS.gather_t #t #SB.bytes r

ghost
fn share_raw_pure (#t: Type0) (f: t -> GTot SB.bytes)
: share_t #t (raw_pure f)
= (x: t) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_pure f p x y);
  fold (raw_pure f (p /. 2.0R) x y);
  fold (raw_pure f (p /. 2.0R) x y)
}

ghost
fn gather_raw_pure (#t: Type0) (f: t -> GTot SB.bytes)
: gather_t #t (raw_pure f)
= (x: t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_pure f p x y);
  unfold (raw_pure f p' x y');
  fold (raw_pure f (p +. p') x y)
}

ghost
fn share_raw_false (t: Type0)
: share_t #t (raw_false t)
= (x: t) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_false t p x y);
  unreachable ()
}

ghost
fn gather_raw_false (t: Type0)
: gather_t #t (raw_false t)
= (x: t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_false t p x y);
  unreachable ()
}

let id_enc_injective () : squash (RS.enc_injective id_enc) = ()

let share_raw_slice () : share_t raw_slice = RS.share_slice_ser id_enc
let gather_raw_slice () : gather_t raw_slice = RS.gather_slice_ser id_enc (id_enc_injective ())

let half_perm_pos (p: perm) : Lemma (p /. 2.0R >. 0.0R) = ()

ghost
fn share_raw_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #t (raw_tlv id r)
= (x: t) (#p: perm) (#y: SB.bytes)
{
  half_perm_pos p;
  unfold (raw_tlv id r p x y);
  with c . assert (r p x c);
  sh x #p #c;
  fold (raw_tlv id r (p /. 2.0R) x y);
  fold (raw_tlv id r (p /. 2.0R) x y)
}

ghost
fn gather_raw_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #t (raw_tlv id r)
= (x: t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_tlv id r p x y);
  with c . assert (r p x c);
  unfold (raw_tlv id r p' x y');
  with c' . assert (r p' x c');
  g x #p #c #p' #c';
  fold (raw_tlv id r (p +. p') x y)
}

ghost
fn share_raw_cat (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (sh1: share_t r1) (sh2: share_t r2)
: share_t #(t1 & t2) (raw_cat r1 r2)
= (x: t1 & t2) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_cat r1 r2 p x y);
  with w1 w2 . assert (r1 p (fst x) w1 ** r2 p (snd x) w2);
  sh1 (fst x) #p #w1;
  sh2 (snd x) #p #w2;
  fold (raw_cat r1 r2 (p /. 2.0R) x y);
  fold (raw_cat r1 r2 (p /. 2.0R) x y)
}

ghost
fn gather_raw_cat (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (g1: gather_t r1) (g2: gather_t r2)
: gather_t #(t1 & t2) (raw_cat r1 r2)
= (x: t1 & t2) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_cat r1 r2 p x y);
  with w1 w2 . assert (r1 p (fst x) w1 ** r2 p (snd x) w2);
  unfold (raw_cat r1 r2 p' x y');
  with w1' w2' . assert (r1 p' (fst x) w1' ** r2 p' (snd x) w2');
  g1 (fst x) #p #w1 #p' #w1';
  g2 (snd x) #p #w2 #p' #w2';
  fold (raw_cat r1 r2 (p +. p') x y)
}

ghost
fn share_raw_pre (e: SB.bytes) (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #t (raw_pre e r)
= (x: t) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_pre e r p x y);
  with w . assert (r p x w);
  sh x #p #w;
  fold (raw_pre e r (p /. 2.0R) x y);
  fold (raw_pre e r (p /. 2.0R) x y)
}

ghost
fn gather_raw_pre (e: SB.bytes) (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #t (raw_pre e r)
= (x: t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_pre e r p x y);
  with w . assert (r p x w);
  unfold (raw_pre e r p' x y');
  with w' . assert (r p' x w');
  g x #p #w #p' #w';
  fold (raw_pre e r (p +. p') x y)
}

ghost
fn share_raw_ins (lt: SI.lt_t) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (sh1: share_t r1) (sh2: share_t r2)
: share_t #(t1 & t2) (raw_ins lt r1 r2)
= (x: t1 & t2) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_ins lt r1 r2 p x y);
  with w1 w2 . assert (r1 p (fst x) w1 ** r2 p (snd x) w2);
  sh1 (fst x) #p #w1;
  sh2 (snd x) #p #w2;
  fold (raw_ins lt r1 r2 (p /. 2.0R) x y);
  fold (raw_ins lt r1 r2 (p /. 2.0R) x y)
}

ghost
fn gather_raw_ins (lt: SI.lt_t) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (g1: gather_t r1) (g2: gather_t r2)
: gather_t #(t1 & t2) (raw_ins lt r1 r2)
= (x: t1 & t2) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_ins lt r1 r2 p x y);
  with w1 w2 . assert (r1 p (fst x) w1 ** r2 p (snd x) w2);
  unfold (raw_ins lt r1 r2 p' x y');
  with w1' w2' . assert (r1 p' (fst x) w1' ** r2 p' (snd x) w2');
  g1 (fst x) #p #w1 #p' #w1';
  g2 (snd x) #p #w2 #p' #w2';
  fold (raw_ins lt r1 r2 (p +. p') x y)
}

ghost
fn share_raw_opt (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #(option t) (raw_opt r)
= (x: option t) (#p: perm) (#y: SB.bytes)
{
  match x {
    None -> {
      rewrite (raw_opt r p x y) as pure (y == Seq.empty);
      rewrite (pure (y == Seq.empty)) as (raw_opt r (p /. 2.0R) x y);
      rewrite (pure (y == Seq.empty)) as (raw_opt r (p /. 2.0R) x y);
    }
    Some a -> {
      rewrite (raw_opt r p x y) as (r p a y);
      sh a #p #y;
      rewrite (r (p /. 2.0R) a y) as (raw_opt r (p /. 2.0R) x y);
      rewrite (r (p /. 2.0R) a y) as (raw_opt r (p /. 2.0R) x y);
    }
  }
}

ghost
fn gather_raw_opt (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #(option t) (raw_opt r)
= (x: option t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  match x {
    None -> {
      rewrite (raw_opt r p x y) as pure (y == Seq.empty);
      rewrite (raw_opt r p' x y') as pure (y' == Seq.empty);
      rewrite (pure (y == Seq.empty)) as (raw_opt r (p +. p') x y);
    }
    Some a -> {
      rewrite (raw_opt r p x y) as (r p a y);
      rewrite (raw_opt r p' x y') as (r p' a y');
      g a #p #y #p' #y';
      rewrite (r (p +. p') a y) as (raw_opt r (p +. p') x y);
    }
  }
}

ghost
fn share_raw_opt_nd (d: SB.bytes) (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #(option t) (raw_opt_nd d r)
= (x: option t) (#p: perm) (#y: SB.bytes)
{
  match x {
    None -> {
      rewrite (raw_opt_nd d r p x y) as pure (y == Seq.empty);
      rewrite (pure (y == Seq.empty)) as (raw_opt_nd d r (p /. 2.0R) x y);
      rewrite (pure (y == Seq.empty)) as (raw_opt_nd d r (p /. 2.0R) x y);
    }
    Some a -> {
      rewrite (raw_opt_nd d r p x y) as (raw_opt_nd d r p (Some a) y);
      unfold (raw_opt_nd d r p (Some a) y);
      with c . assert (r p a c);
      sh a #p #c;
      fold (raw_opt_nd d r (p /. 2.0R) (Some a) y);
      fold (raw_opt_nd d r (p /. 2.0R) (Some a) y);
      rewrite each (Some a) as x;
    }
  }
}

ghost
fn gather_raw_opt_nd (d: SB.bytes) (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #(option t) (raw_opt_nd d r)
= (x: option t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  match x {
    None -> {
      rewrite (raw_opt_nd d r p x y) as pure (y == Seq.empty);
      rewrite (raw_opt_nd d r p' x y') as pure (y' == Seq.empty);
      rewrite (pure (y == Seq.empty)) as (raw_opt_nd d r (p +. p') x y);
    }
    Some a -> {
      rewrite (raw_opt_nd d r p x y) as (raw_opt_nd d r p (Some a) y);
      rewrite (raw_opt_nd d r p' x y') as (raw_opt_nd d r p' (Some a) y');
      unfold (raw_opt_nd d r p (Some a) y);
      unfold (raw_opt_nd d r p' (Some a) y');
      with c . assert (r p a c);
      with c' . assert (r p' a c');
      g a #p #c #p' #c';
      fold (raw_opt_nd d r (p +. p') (Some a) y);
      rewrite (raw_opt_nd d r (p +. p') (Some a) y) as (raw_opt_nd d r (p +. p') x y);
    }
  }
}

ghost
fn share_raw_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (sh1: share_t r1) (sh2: share_t r2)
: share_t #(either t1 t2) (raw_either r1 r2)
= (x: either t1 t2) (#p: perm) (#y: SB.bytes)
{
  match x {
    Inl a -> {
      rewrite (raw_either r1 r2 p x y) as (r1 p a y);
      sh1 a #p #y;
      rewrite (r1 (p /. 2.0R) a y) as (raw_either r1 r2 (p /. 2.0R) x y);
      rewrite (r1 (p /. 2.0R) a y) as (raw_either r1 r2 (p /. 2.0R) x y);
    }
    Inr b -> {
      rewrite (raw_either r1 r2 p x y) as (r2 p b y);
      sh2 b #p #y;
      rewrite (r2 (p /. 2.0R) b y) as (raw_either r1 r2 (p /. 2.0R) x y);
      rewrite (r2 (p /. 2.0R) b y) as (raw_either r1 r2 (p /. 2.0R) x y);
    }
  }
}

ghost
fn gather_raw_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (g1: gather_t r1) (g2: gather_t r2)
: gather_t #(either t1 t2) (raw_either r1 r2)
= (x: either t1 t2) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  match x {
    Inl a -> {
      rewrite (raw_either r1 r2 p x y) as (r1 p a y);
      rewrite (raw_either r1 r2 p' x y') as (r1 p' a y');
      g1 a #p #y #p' #y';
      rewrite (r1 (p +. p') a y) as (raw_either r1 r2 (p +. p') x y);
    }
    Inr b -> {
      rewrite (raw_either r1 r2 p x y) as (r2 p b y);
      rewrite (raw_either r1 r2 p' x y') as (r2 p' b y');
      g2 b #p #y #p' #y';
      rewrite (r2 (p +. p') b y) as (raw_either r1 r2 (p +. p') x y);
    }
  }
}

ghost
fn share_raw_ml (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #(ml t) (raw_ml r)
= (x: ml t) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_ml r p x y);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p x l);
  It.mixed_list_match_share r ml_ops p_raw p x l sh;
  fold (raw_ml r (p /. 2.0R) x y);
  fold (raw_ml r (p /. 2.0R) x y)
}

ghost
fn gather_raw_ml (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #(ml t) (raw_ml r)
= (x: ml t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_ml r p x y);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p x l);
  unfold (raw_ml r p' x y');
  with l' . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p' x l');
  It.mixed_list_match_gather r ml_ops p_raw p p' x l l' g;
  fold (raw_ml r (p +. p') x y)
}

ghost
fn share_raw_ml_sorted (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #(ml t) (raw_ml_sorted r)
= (x: ml t) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_ml_sorted r p x y);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p x l);
  It.mixed_list_match_share r ml_ops p_raw p x l sh;
  fold (raw_ml_sorted r (p /. 2.0R) x y);
  fold (raw_ml_sorted r (p /. 2.0R) x y)
}

ghost
fn gather_raw_ml_sorted (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #(ml t) (raw_ml_sorted r)
= (x: ml t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_ml_sorted r p x y);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p x l);
  unfold (raw_ml_sorted r p' x y');
  with l' . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw p' x l');
  It.mixed_list_match_gather r ml_ops p_raw p p' x l l' g;
  fold (raw_ml_sorted r (p +. p') x y)
}

ghost
fn share_raw_int (_: unit)
: share_t #asn1_int_impl raw_int
= (x: asn1_int_impl) (#p: perm) (#y: SB.bytes)
{
  half_perm_pos p;
  match x {
    Small i -> {
      rewrite (raw_int p x y) as (pure (y == i64_enc i));
      rewrite (pure (y == i64_enc i)) as (raw_int (p /. 2.0R) x y);
      rewrite (pure (y == i64_enc i)) as (raw_int (p /. 2.0R) x y);
    }
    Big s -> {
      rewrite (raw_int p x y) as (raw_slice p s y);
      share_raw_slice () s #p #y;
      rewrite (raw_slice (p /. 2.0R) s y) as (raw_int (p /. 2.0R) x y);
      rewrite (raw_slice (p /. 2.0R) s y) as (raw_int (p /. 2.0R) x y);
    }
  }
}

ghost
fn gather_raw_int (_: unit)
: gather_t #asn1_int_impl raw_int
= (x: asn1_int_impl) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  match x {
    Small i -> {
      rewrite (raw_int p x y) as (pure (y == i64_enc i));
      rewrite (raw_int p' x y') as (pure (y' == i64_enc i));
      rewrite (pure (y == i64_enc i)) as (raw_int (p +. p') x y);
    }
    Big s -> {
      rewrite (raw_int p x y) as (raw_slice p s y);
      rewrite (raw_int p' x y') as (raw_slice p' s y');
      gather_raw_slice () s #p #y #p' #y';
      rewrite (raw_slice (p +. p') s y) as (raw_int (p +. p') x y);
    }
  }
}

ghost
fn share_raw_bitstring (_: unit)
: share_t #asn1_bitstring_impl raw_bitstring
= (x: asn1_bitstring_impl) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_bitstring p x y);
  S.share x.bytes;
  fold (raw_bitstring (p /. 2.0R) x y);
  fold (raw_bitstring (p /. 2.0R) x y)
}

ghost
fn gather_raw_bitstring (_: unit)
: gather_t #asn1_bitstring_impl raw_bitstring
= (x: asn1_bitstring_impl) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_bitstring p x y);
  unfold (raw_bitstring p' x y');
  S.gather x.bytes;
  fold (raw_bitstring (p +. p') x y)
}

let share_raw_integer (bound: pos) : share_t (raw_integer bound) =
  if small_integer bound
  then coerce_eq () (share_raw_pure i64_enc)
  else coerce_eq () (share_raw_int ())

let gather_raw_integer (bound: pos) : gather_t (raw_integer bound) =
  if small_integer bound
  then coerce_eq () (gather_raw_pure i64_enc)
  else coerce_eq () (gather_raw_int ())

let share_raw_leaf (k: leaf_k) : share_t (raw_leaf k) =
  match k with
  | ASN1_BOOLEAN -> share_raw_pure boolean_enc
  | ASN1_NULL -> share_raw_pure null_enc
  | ASN1_INTEGER bound -> share_raw_integer bound
  | ASN1_BITSTRING -> share_raw_bitstring ()
  | _ -> coerce_eq () (share_raw_slice ())

let gather_raw_leaf (k: leaf_k) : gather_t (raw_leaf k) =
  match k with
  | ASN1_BOOLEAN -> gather_raw_pure boolean_enc
  | ASN1_NULL -> gather_raw_pure null_enc
  | ASN1_INTEGER bound -> gather_raw_integer bound
  | ASN1_BITSTRING -> gather_raw_bitstring ()
  | _ -> coerce_eq () (gather_raw_slice ())

(* Equations, so that proofs need not unfold the relation of a whole schema *)

let prel_equiv (#t: Type0) (r1 r2: bprel t) : prop = RS.prel_equiv #t #SB.bytes r1 r2

let raw_dlit (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (#y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) : bprel t =
  raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di)

let raw_lit (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) : bprel (asn1_items_impl_t (dsnd y)) =
  raw_dlit kid kx #y (legacy_idesc (dsnd y))

let solve_equiv () : T.Tac unit =
  T.norm [delta_only [`%prel_equiv; `%RS.prel_equiv]];
  let _ = T.forall_intros () in
  T.norm [delta_only [`%raw_terminal_rel; `%raw_crel; `%raw_sxrel; `%raw_fxrel; `%raw_iarel; `%raw_lcrel; `%raw_arel; `%raw_drel; `%raw_irel; `%raw_view; `%raw_dfbr; `%raw_dlit; `%legacy_adesc; `%legacy_cdesc; `%legacy_ddesc; `%legacy_idesc; `%legacy_lcdesc; `%legacy_iadesc; `%legacy_sxdesc; `%legacy_fxdesc; `%raw_content_rel; `%raw_lc_rel; `%raw_rel; `%raw_dec_rel; `%raw_items_rel; `%raw_items_any_rel; `%raw_adb_rel; `%raw_adb_fb_rel; `%raw_afb_rel; `%raw_fbr; `%PA.fbt; `%PA.adb_k_none; `%PA.adb_k_some; `%coerce_eq]; zeta; iota];
  T.trefl ()


let terminal_prefixed_t_eq (id2: asn1_id_t) (k2: asn1_terminal_k)
: Lemma (asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_impl_t k2)
= assert_norm (asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_impl_t k2)

let prefixed_down (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) : Tot (asn1_terminal_impl_t k2) =
  terminal_prefixed_t_eq id2 k2;
  coerce_eq () x

let terminal_prefixed_eq (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (pm: perm) (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (w: SB.bytes)
: Lemma (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x w == raw_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 x) w)
= assert (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x w == raw_tlv id (raw_terminal_rel id2 k2) pm (prefixed_down id2 k2 x) w)
    by (FStar.Tactics.V2.norm [delta_only [`%raw_terminal_rel; `%prefixed_down; `%coerce_eq]; zeta; iota]; FStar.Tactics.V2.trefl ())

let terminal_leaf_equiv (id: asn1_id_t) (k: leaf_k)
: Lemma (prel_equiv #(asn1_terminal_impl_t k) (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k))
= match k with
  | ASN1_BOOLEAN -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_BOOLEAN) (raw_tlv id (raw_leaf ASN1_BOOLEAN)) (raw_terminal_rel id ASN1_BOOLEAN)) by (solve_equiv ())
  | ASN1_NULL -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_NULL) (raw_tlv id (raw_leaf ASN1_NULL)) (raw_terminal_rel id ASN1_NULL)) by (solve_equiv ())
  | ASN1_INTEGER bound -> assert (prel_equiv #(asn1_terminal_impl_t (ASN1_INTEGER bound)) (raw_tlv id (raw_leaf (ASN1_INTEGER bound))) (raw_terminal_rel id (ASN1_INTEGER bound))) by (solve_equiv ())
  | ASN1_BITSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_BITSTRING) (raw_tlv id (raw_leaf ASN1_BITSTRING)) (raw_terminal_rel id ASN1_BITSTRING)) by (solve_equiv ())
  | ASN1_OCTETSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_OCTETSTRING) (raw_tlv id (raw_leaf ASN1_OCTETSTRING)) (raw_terminal_rel id ASN1_OCTETSTRING)) by (solve_equiv ())
  | ASN1_PRINTABLESTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_PRINTABLESTRING) (raw_tlv id (raw_leaf ASN1_PRINTABLESTRING)) (raw_terminal_rel id ASN1_PRINTABLESTRING)) by (solve_equiv ())
  | ASN1_UTF8STRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_UTF8STRING) (raw_tlv id (raw_leaf ASN1_UTF8STRING)) (raw_terminal_rel id ASN1_UTF8STRING)) by (solve_equiv ())
  | ASN1_IA5STRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_IA5STRING) (raw_tlv id (raw_leaf ASN1_IA5STRING)) (raw_terminal_rel id ASN1_IA5STRING)) by (solve_equiv ())
  | ASN1_VISIBLESTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_VISIBLESTRING) (raw_tlv id (raw_leaf ASN1_VISIBLESTRING)) (raw_terminal_rel id ASN1_VISIBLESTRING)) by (solve_equiv ())
  | ASN1_BMPSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_BMPSTRING) (raw_tlv id (raw_leaf ASN1_BMPSTRING)) (raw_terminal_rel id ASN1_BMPSTRING)) by (solve_equiv ())
  | ASN1_UNIVERSALSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_UNIVERSALSTRING) (raw_tlv id (raw_leaf ASN1_UNIVERSALSTRING)) (raw_terminal_rel id ASN1_UNIVERSALSTRING)) by (solve_equiv ())
  | ASN1_TELETEXSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_TELETEXSTRING) (raw_tlv id (raw_leaf ASN1_TELETEXSTRING)) (raw_terminal_rel id ASN1_TELETEXSTRING)) by (solve_equiv ())
  | ASN1_NUMERICSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_NUMERICSTRING) (raw_tlv id (raw_leaf ASN1_NUMERICSTRING)) (raw_terminal_rel id ASN1_NUMERICSTRING)) by (solve_equiv ())
  | ASN1_VIDEOTEXSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_VIDEOTEXSTRING) (raw_tlv id (raw_leaf ASN1_VIDEOTEXSTRING)) (raw_terminal_rel id ASN1_VIDEOTEXSTRING)) by (solve_equiv ())
  | ASN1_GRAPHICSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_GRAPHICSTRING) (raw_tlv id (raw_leaf ASN1_GRAPHICSTRING)) (raw_terminal_rel id ASN1_GRAPHICSTRING)) by (solve_equiv ())
  | ASN1_GENERALSTRING -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_GENERALSTRING) (raw_tlv id (raw_leaf ASN1_GENERALSTRING)) (raw_terminal_rel id ASN1_GENERALSTRING)) by (solve_equiv ())
  | ASN1_OBJECTDESCRIPTOR -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_OBJECTDESCRIPTOR) (raw_tlv id (raw_leaf ASN1_OBJECTDESCRIPTOR)) (raw_terminal_rel id ASN1_OBJECTDESCRIPTOR)) by (solve_equiv ())
  | ASN1_OID -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_OID) (raw_tlv id (raw_leaf ASN1_OID)) (raw_terminal_rel id ASN1_OID)) by (solve_equiv ())
  | ASN1_RELATIVE_OID -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_RELATIVE_OID) (raw_tlv id (raw_leaf ASN1_RELATIVE_OID)) (raw_terminal_rel id ASN1_RELATIVE_OID)) by (solve_equiv ())
  | ASN1_OID_IRI -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_OID_IRI) (raw_tlv id (raw_leaf ASN1_OID_IRI)) (raw_terminal_rel id ASN1_OID_IRI)) by (solve_equiv ())
  | ASN1_RELATIVE_OID_IRI -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_RELATIVE_OID_IRI) (raw_tlv id (raw_leaf ASN1_RELATIVE_OID_IRI)) (raw_terminal_rel id ASN1_RELATIVE_OID_IRI)) by (solve_equiv ())
  | ASN1_UTCTIME -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_UTCTIME) (raw_tlv id (raw_leaf ASN1_UTCTIME)) (raw_terminal_rel id ASN1_UTCTIME)) by (solve_equiv ())
  | ASN1_GENERALIZEDTIME -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_GENERALIZEDTIME) (raw_tlv id (raw_leaf ASN1_GENERALIZEDTIME)) (raw_terminal_rel id ASN1_GENERALIZEDTIME)) by (solve_equiv ())
  | ASN1_DATE -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_DATE) (raw_tlv id (raw_leaf ASN1_DATE)) (raw_terminal_rel id ASN1_DATE)) by (solve_equiv ())
  | ASN1_TIME_OF_DAY -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_TIME_OF_DAY) (raw_tlv id (raw_leaf ASN1_TIME_OF_DAY)) (raw_terminal_rel id ASN1_TIME_OF_DAY)) by (solve_equiv ())
  | ASN1_DATE_TIME -> assert (prel_equiv #(asn1_terminal_impl_t ASN1_DATE_TIME) (raw_tlv id (raw_leaf ASN1_DATE_TIME)) (raw_terminal_rel id ASN1_DATE_TIME)) by (solve_equiv ())

let content_terminal_equiv (id: asn1_id_t) (k: asn1_terminal_k)
: Lemma (prel_equiv #(asn1_terminal_impl_t k) (raw_terminal_rel id k) (raw_crel id (CD_TERMINAL k)))
= assert (prel_equiv #(asn1_terminal_impl_t k) (raw_terminal_rel id k) (raw_crel id (CD_TERMINAL k))) by (solve_equiv ())

let content_restricted_equiv (id: asn1_id_t) (k: asn1_terminal_k) (r: asn1_restriction k)
: Lemma (prel_equiv #(asn1_terminal_impl_t k) (raw_terminal_rel id k) (raw_crel id (CD_RESTRICTED k r)))
= assert (prel_equiv #(asn1_terminal_impl_t k) (raw_terminal_rel id k) (raw_crel id (CD_RESTRICTED k r))) by (solve_equiv ())

let content_prefixed_equiv (id: asn1_id_t) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (prel_equiv #t (raw_tlv id (raw_arel d)) (raw_crel id (CD_PREFIXED d)))
= assert (prel_equiv #t (raw_tlv id (raw_arel d)) (raw_crel id (CD_PREFIXED d))) by (solve_equiv ())

let content_sequence_equiv (id: asn1_id_t) (gitems: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd gitems) t)
: Lemma (prel_equiv #t (raw_tlv id (raw_irel false di)) (raw_crel id (CD_SEQUENCE gitems di)))
= assert (prel_equiv #t (raw_tlv id (raw_irel false di)) (raw_crel id (CD_SEQUENCE gitems di))) by (solve_equiv ())

let content_set_equiv (id: asn1_id_t) (ids: _) (items: asn1_gen_items_l ids) (pf: _) (#t: Type0) (di: idesc items t)
: Lemma (prel_equiv #t (raw_tlv id (raw_irel true di)) (raw_crel id (CD_SET ids items pf di)))
= assert (prel_equiv #t (raw_tlv id (raw_irel true di)) (raw_crel id (CD_SET ids items pf di))) by (solve_equiv ())

let content_seq_of_equiv (id: asn1_id_t) (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (prel_equiv #(ml t) (raw_tlv id (raw_ml (raw_arel d))) (raw_crel id (CD_SEQUENCE_OF ne d)))
= assert (prel_equiv #(ml t) (raw_tlv id (raw_ml (raw_arel d))) (raw_crel id (CD_SEQUENCE_OF ne d))) by (solve_equiv ())

let content_set_of_equiv (id: asn1_id_t) (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (prel_equiv #(ml t) (raw_tlv id (raw_ml_sorted (raw_arel d))) (raw_crel id (CD_SET_OF ne d)))
= assert (prel_equiv #(ml t) (raw_tlv id (raw_ml_sorted (raw_arel d))) (raw_crel id (CD_SET_OF ne d))) by (solve_equiv ())

let content_adb_none_equiv (id: asn1_id_t) (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#ts: Type0) (dsx: sxdesc key_k ls ts) (#t: Type0) (dpre: iadesc prefix ts t)
: Lemma (prel_equiv #t (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre)))
= assert (prel_equiv #t (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre))) by (solve_equiv ())

let content_adb_some_equiv (id: asn1_id_t) (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts) (#t: Type0) (dpre: iadesc prefix ts t)
: Lemma (prel_equiv #t (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre)))
= assert (prel_equiv #t (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre))) by (solve_equiv ())

let content_view_equiv (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (prel_equiv #ty (raw_view (raw_crel id d) view) (raw_crel id (CD_VIEW d ty view mk law)))
= assert (prel_equiv #ty (raw_view (raw_crel id d) view) (raw_crel id (CD_VIEW d ty view mk law))) by (solve_equiv ())

let items_any_nil_equiv (#sfx: Type0) (sr: bprel sfx)
: Lemma (prel_equiv #sfx sr (raw_iarel (IA_NIL #sfx) sr))
= assert (prel_equiv #sfx sr (raw_iarel (IA_NIL #sfx) sr)) by (solve_equiv ())

let items_any_single_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t) (#sfx: Type0) (sr: bprel sfx)
: Lemma (prel_equiv #(t & sfx) (raw_cat (raw_drel dd) sr) (raw_iarel (IA_SINGLE dd #sfx) sr))
= assert (prel_equiv #(t & sfx) (raw_cat (raw_drel dd) sr) (raw_iarel (IA_SINGLE dd #sfx) sr)) by (solve_equiv ())

let items_any_cons_equiv (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#sfx: Type0) (#t2: Type0)
  (dtl: iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfx t2) (sr: bprel sfx)
: Lemma (prel_equiv #(t1 & t2) (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel (IA_CONS dd dtl) sr))
= assert (prel_equiv #(t1 & t2) (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel (IA_CONS dd dtl) sr)) by (solve_equiv ())

(* The payload selected by the key literal `kx` *)
let adb_nil_equiv (kid: asn1_id_t) (key_k: asn1_terminal_k)
: Lemma (prel_equiv #unit (raw_false unit) (raw_sxrel kid (SX_NIL key_k)))
= assert (prel_equiv #unit (raw_false unit) (raw_sxrel kid (SX_NIL key_k))) by (solve_equiv ())

let adb_single_equiv (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t)
: Lemma (prel_equiv #t (raw_dlit kid kx #y di) (raw_sxrel kid (SX_SINGLE key_k kx y di)))
= assert (prel_equiv #t (raw_dlit kid kx #y di) (raw_sxrel kid (SX_SINGLE key_k kx y di))) by (T.norm [delta_only [`%raw_dlit]]; solve_equiv ())

let adb_cons_equiv (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
: Lemma (prel_equiv #(either t1 t2) (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid (SX_CONS key_k kx y di dtl)))
= assert (prel_equiv #(either t1 t2) (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid (SX_CONS key_k kx y di dtl))) by (T.norm [delta_only [`%raw_dlit]]; solve_equiv ())

let afb_nil_equiv (kid: asn1_id_t) (key_k: asn1_terminal_k) (#fbt: Type0) (fbr: bprel fbt)
: Lemma (prel_equiv #fbt fbr (raw_fxrel kid (FX_NIL key_k #fbt) fbr))
= assert (prel_equiv #fbt fbr (raw_fxrel kid (FX_NIL key_k #fbt) fbr)) by (solve_equiv ())

let afb_single_equiv (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t) (#fbt: Type0) (fbr: bprel fbt)
: Lemma (prel_equiv #(either t fbt) (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid (FX_SINGLE key_k kx y di #fbt) fbr))
= assert (prel_equiv #(either t fbt) (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid (FX_SINGLE key_k kx y di #fbt) fbr)) by (T.norm [delta_only [`%raw_dlit]]; solve_equiv ())

let afb_cons_equiv (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) fbt t2) (fbr: bprel fbt)
: Lemma (prel_equiv #(either t1 t2) (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid (FX_CONS key_k kx y di dtl) fbr))
= assert (prel_equiv #(either t1 t2) (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid (FX_CONS key_k kx y di dtl) fbr)) by (T.norm [delta_only [`%raw_dlit]]; solve_equiv ())

let rel_ilc_equiv (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t)
: Lemma (prel_equiv #t (raw_crel id cd) (raw_arel (D_ILC id cd)))
= assert (prel_equiv #t (raw_crel id cd) (raw_arel (D_ILC id cd))) by (solve_equiv ())

let rel_choice_equiv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (#t: Type0) (ld: lcdesc lc t)
: Lemma (prel_equiv #t (raw_lcrel ld) (raw_arel (D_CHOICE lc pf ld)))
= assert (prel_equiv #t (raw_lcrel ld) (raw_arel (D_CHOICE lc pf ld))) by (solve_equiv ())

let rel_any_equiv (_: unit)
: Lemma (prel_equiv #(S.slice U8.t) raw_slice (raw_arel D_ANY))
= assert (prel_equiv #(S.slice U8.t) raw_slice (raw_arel D_ANY)) by (solve_equiv ())

let rel_view_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (prel_equiv #ty (raw_view (raw_arel d) view) (raw_arel (D_VIEW d ty view mk law)))
= assert (prel_equiv #ty (raw_view (raw_arel d) view) (raw_arel (D_VIEW d ty view mk law))) by (solve_equiv ())

let rel_keep_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k))
: Lemma (prel_equiv #(kept t) (raw_keep (raw_arel d)) (raw_arel (D_KEEP d wf)))
= assert (prel_equiv #(kept t) (raw_keep (raw_arel d)) (raw_arel (D_KEEP d wf))) by (T.norm [delta_only [`%raw_keep]]; solve_equiv ())

let lc_nil_equiv (_: unit)
: Lemma (prel_equiv #unit (raw_false unit) (raw_lcrel LC_NIL))
= assert (prel_equiv #unit (raw_false unit) (raw_lcrel LC_NIL)) by (solve_equiv ())

let lc_single_equiv (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t)
: Lemma (prel_equiv #t (raw_crel id' cd) (raw_lcrel (LC_SINGLE id' cd)))
= assert (prel_equiv #t (raw_crel id' cd) (raw_lcrel (LC_SINGLE id' cd))) by (solve_equiv ())

let lc_cons_equiv (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
: Lemma (prel_equiv #(either t1 t2) (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel (LC_CONS id' cd dtl)))
= assert (prel_equiv #(either t1 t2) (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel (LC_CONS id' cd dtl))) by (solve_equiv ())

let dec_plain_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (prel_equiv #t (raw_arel d) (raw_drel (DD_PLAIN d)))
= assert (prel_equiv #t (raw_arel d) (raw_drel (DD_PLAIN d))) by (solve_equiv ())

let dec_option_equiv (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Lemma (prel_equiv #(option t) (raw_opt (raw_arel d)) (raw_drel (DD_OPTION d)))
= assert (prel_equiv #(option t) (raw_opt (raw_arel d)) (raw_drel (DD_OPTION d))) by (solve_equiv ())

let dec_default_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k)
: Lemma (prel_equiv #(option (asn1_terminal_impl_t k)) (raw_default_rel id0 k defv) (raw_drel (DD_DEFAULT id0 #k defv)))
= assert (prel_equiv #(option (asn1_terminal_impl_t k)) (raw_default_rel id0 k defv) (raw_drel (DD_DEFAULT id0 #k defv))) by (solve_equiv ())

let dec_default_restricted_equiv (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) })
: Lemma (prel_equiv #(option (asn1_terminal_impl_t k)) (raw_default_rel id0 k defv) (raw_drel (DD_DEFAULT_RESTRICTED id0 #k r defv)))
= assert (prel_equiv #(option (asn1_terminal_impl_t k)) (raw_default_rel id0 k defv) (raw_drel (DD_DEFAULT_RESTRICTED id0 #k r defv))) by (solve_equiv ())

let dec_view_equiv (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (ty: Type0) (view: ty -> t) (mk: t -> ty) (law: squash (view_law view mk))
: Lemma (prel_equiv #ty (raw_view (raw_drel d) view) (raw_drel (DD_VIEW d ty view mk law)))
= assert (prel_equiv #ty (raw_view (raw_drel d) view) (raw_drel (DD_VIEW d ty view mk law))) by (solve_equiv ())

let default_nd_equiv (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k)
: Lemma (requires (In.adb_key_supported k))
  (ensures (prel_equiv #(option (asn1_terminal_impl_t k)) (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl)))
= default_rel_nd id0 k defl

let default_opt_equiv (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k)
: Lemma (requires (~ (In.adb_key_supported k)))
  (ensures (prel_equiv #(option (asn1_terminal_impl_t k)) (raw_opt (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl)))
= default_rel_opt id0 k defl

let items_nil_equiv (srt: bool)
: Lemma (prel_equiv #unit (raw_pure null_enc) (raw_irel srt ID_NIL))
= assert (prel_equiv #unit (raw_pure null_enc) (raw_irel srt ID_NIL)) by (solve_equiv ())

let items_single_equiv (srt: bool) (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t: Type0) (dd: ddesc dk t)
: Lemma (prel_equiv #t (raw_drel dd) (raw_irel srt (ID_SINGLE dd)))
= assert (prel_equiv #t (raw_drel dd) (raw_irel srt (ID_SINGLE dd))) by (solve_equiv ())

let items_cons_equiv (srt: bool) (#s: _) (#d: _) (#dk: asn1_decorated_k s d) (#t1: Type0) (dd: ddesc dk t1)
  (#s2: _) (#d2: _) (#dk2: asn1_decorated_k s2 d2) (#ids2: _) (#tl2: asn1_gen_items_l ids2) (#t2: Type0)
  (dtl: idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) t2)
: Lemma (prel_equiv #(t1 & t2) (raw_join srt (raw_drel dd) (raw_irel srt dtl)) (raw_irel srt (ID_CONS dd dtl)))
= assert (prel_equiv #(t1 & t2) (raw_join srt (raw_drel dd) (raw_irel srt dtl)) (raw_irel srt (ID_CONS dd dtl))) by (solve_equiv ())

let join_ins_equiv (srt: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2)
: Lemma (requires srt == true) (ensures prel_equiv (raw_ins SI.lt_tag r1 r2) (raw_join srt r1 r2))
= ()

let join_cat_equiv (srt: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2)
: Lemma (requires srt == false) (ensures prel_equiv (raw_cat r1 r2) (raw_join srt r1 r2))
= ()

(* The shares and gathers of a whole schema *)

let share_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (sh: share_t r1) : share_t r2 =
  RS.share_ext r1 r2 sq sh

let gather_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (g: gather_t r1) : gather_t r2 =
  RS.gather_ext r1 r2 sq g

let share_raw_join (srt: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (sh1: share_t r1) (sh2: share_t r2)
: share_t (raw_join srt r1 r2)
= if srt
  then (join_ins_equiv srt r1 r2; share_ext (raw_ins SI.lt_tag r1 r2) (raw_join srt r1 r2) () (share_raw_ins SI.lt_tag r1 r2 sh1 sh2))
  else (join_cat_equiv srt r1 r2; share_ext (raw_cat r1 r2) (raw_join srt r1 r2) () (share_raw_cat r1 r2 sh1 sh2))

let gather_raw_join (srt: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (g1: gather_t r1) (g2: gather_t r2)
: gather_t (raw_join srt r1 r2)
= if srt
  then (join_ins_equiv srt r1 r2; gather_ext (raw_ins SI.lt_tag r1 r2) (raw_join srt r1 r2) () (gather_raw_ins SI.lt_tag r1 r2 g1 g2))
  else (join_cat_equiv srt r1 r2; gather_ext (raw_cat r1 r2) (raw_join srt r1 r2) () (gather_raw_cat r1 r2 g1 g2))

ghost
fn share_terminal_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (sh: share_t (raw_terminal_rel id2 k2))
: share_t #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2))
= (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (#p: perm) (#y: SB.bytes)
{
  terminal_prefixed_eq id id2 k2 p x y;
  terminal_prefixed_eq id id2 k2 (p /. 2.0R) x y;
  let x' = prefixed_down id2 k2 x;
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) p x y) as (raw_tlv id (raw_terminal_rel id2 k2) p x' y);
  share_raw_tlv id (raw_terminal_rel id2 k2) sh x' #p #y;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) (p /. 2.0R) x' y ** raw_tlv id (raw_terminal_rel id2 k2) (p /. 2.0R) x' y)
    as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) (p /. 2.0R) x y ** raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) (p /. 2.0R) x y)
}

ghost
fn gather_terminal_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (g: gather_t (raw_terminal_rel id2 k2))
: gather_t #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2))
= (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  terminal_prefixed_eq id id2 k2 p x y;
  terminal_prefixed_eq id id2 k2 p' x y';
  terminal_prefixed_eq id id2 k2 (p +. p') x y;
  let x' = prefixed_down id2 k2 x;
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) p x y ** raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) p' x y')
    as (raw_tlv id (raw_terminal_rel id2 k2) p x' y ** raw_tlv id (raw_terminal_rel id2 k2) p' x' y');
  gather_raw_tlv id (raw_terminal_rel id2 k2) g x' #p #y #p' #y';
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) (p +. p') x' y) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) (p +. p') x y)
}

let rec share_terminal (id: asn1_id_t) (k: asn1_terminal_k) : Tot (share_t (raw_terminal_rel id k)) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> share_terminal_prefixed id id2 k2 (share_terminal id2 k2)
  | _ ->
    terminal_leaf_equiv id k;
    share_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) () (share_raw_tlv id (raw_leaf k) (share_raw_leaf k))

let rec gather_terminal (id: asn1_id_t) (k: asn1_terminal_k) : Tot (gather_t (raw_terminal_rel id k)) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 -> gather_terminal_prefixed id id2 k2 (gather_terminal id2 k2)
  | _ ->
    terminal_leaf_equiv id k;
    gather_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) () (gather_raw_tlv id (raw_leaf k) (gather_raw_leaf k))

let share_default (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k) : Tot (share_t (raw_default_rel id0 k defl)) =
  if In.adb_key_supported k
  then (default_nd_equiv id0 k defl; share_ext (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () (share_raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) (share_terminal id0 k)))
  else (default_opt_equiv id0 k defl; share_ext (raw_opt (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () (share_raw_opt (raw_terminal_rel id0 k) (share_terminal id0 k)))

let gather_default (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k) : Tot (gather_t (raw_default_rel id0 k defl)) =
  if In.adb_key_supported k
  then (default_nd_equiv id0 k defl; gather_ext (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () (gather_raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) (gather_terminal id0 k)))
  else (default_opt_equiv id0 k defl; gather_ext (raw_opt (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () (gather_raw_opt (raw_terminal_rel id0 k) (gather_terminal id0 k)))

ghost
fn share_raw_view (#t #ty: Type0) (r: bprel t) (view: ty -> t) (sh: share_t r)
: share_t #ty (raw_view r view)
= (x: ty) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_view r view p x y);
  sh (view x) #p #y;
  fold (raw_view r view (p /. 2.0R) x y);
  fold (raw_view r view (p /. 2.0R) x y)
}

ghost
fn gather_raw_view (#t #ty: Type0) (r: bprel t) (view: ty -> t) (g: gather_t r)
: gather_t #ty (raw_view r view)
= (x: ty) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_view r view p x y);
  unfold (raw_view r view p' x y');
  g (view x) #p #y #p' #y';
  fold (raw_view r view (p +. p') x y)
}

ghost
fn share_keep_own (pm: perm) (r: option (S.slice U8.t))
requires keep_own pm r
ensures keep_own (pm /. 2.0R) r ** keep_own (pm /. 2.0R) r
{
  match r {
    None -> {
      unfold (keep_own pm None);
      fold (keep_own (pm /. 2.0R) None);
      fold (keep_own (pm /. 2.0R) None)
    }
    Some sl -> {
      unfold (keep_own pm (Some sl));
      S.share sl;
      fold (keep_own (pm /. 2.0R) (Some sl));
      fold (keep_own (pm /. 2.0R) (Some sl))
    }
  }
}

ghost
fn gather_keep_own (pm pm': perm) (r: option (S.slice U8.t))
requires keep_own pm r ** keep_own pm' r
ensures keep_own (pm +. pm') r
{
  match r {
    None -> {
      unfold (keep_own pm None);
      unfold (keep_own pm' None);
      fold (keep_own (pm +. pm') None)
    }
    Some sl -> {
      unfold (keep_own pm (Some sl));
      unfold (keep_own pm' (Some sl));
      S.gather sl;
      fold (keep_own (pm +. pm') (Some sl))
    }
  }
}

ghost
fn share_raw_keep (#t: Type0) (r: bprel t) (sh: share_t r)
: share_t #(kept t) (raw_keep r)
= (x: kept t) (#p: perm) (#y: SB.bytes)
{
  unfold (raw_keep r p x y);
  sh x.kval #(p /. 2.0R) #y;
  share_keep_own (p /. 2.0R) x.kraw;
  fold (raw_keep r (p /. 2.0R) x y);
  fold (raw_keep r (p /. 2.0R) x y)
}

ghost
fn gather_raw_keep (#t: Type0) (r: bprel t) (g: gather_t r)
: gather_t #(kept t) (raw_keep r)
= (x: kept t) (#p: perm) (#y: SB.bytes) (#p': perm) (#y': SB.bytes)
{
  unfold (raw_keep r p x y);
  unfold (raw_keep r p' x y');
  g x.kval #(p /. 2.0R) #y #(p' /. 2.0R) #y';
  gather_keep_own (p /. 2.0R) (p' /. 2.0R) x.kraw;
  assert (pure (p /. 2.0R +. p' /. 2.0R == (p +. p') /. 2.0R));
  rewrite each (p /. 2.0R +. p' /. 2.0R) as ((p +. p') /. 2.0R);
  fold (raw_keep r (p +. p') x y)
}

let rec share_crel (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (d: cdesc k t)
: Tot (share_t (raw_crel id d)) (decreases d)
= match d with
  | CD_TERMINAL k' ->
    content_terminal_equiv id k';
    share_ext (raw_terminal_rel id k') (raw_crel id d) () (share_terminal id k')
  | CD_RESTRICTED k' r ->
    content_restricted_equiv id k' r;
    share_ext (raw_terminal_rel id k') (raw_crel id d) () (share_terminal id k')
  | CD_PREFIXED d' ->
    content_prefixed_equiv id d';
    share_ext (raw_tlv id (raw_arel d')) (raw_crel id d) () (share_raw_tlv id (raw_arel d') (share_arel d'))
  | CD_SEQUENCE gitems di ->
    content_sequence_equiv id gitems di;
    share_ext (raw_tlv id (raw_irel false di)) (raw_crel id d) () (share_raw_tlv id (raw_irel false di) (share_irel false di))
  | CD_SET ids items pf di ->
    content_set_equiv id ids items pf di;
    share_ext (raw_tlv id (raw_irel true di)) (raw_crel id d) () (share_raw_tlv id (raw_irel true di) (share_irel true di))
  | CD_SEQUENCE_OF ne d' ->
    content_seq_of_equiv id ne d';
    share_ext (raw_tlv id (raw_ml (raw_arel d'))) (raw_crel id d) () (share_raw_tlv id (raw_ml (raw_arel d')) (share_raw_ml (raw_arel d') (share_arel d')))
  | CD_SET_OF ne d' ->
    content_set_of_equiv id ne d';
    share_ext (raw_tlv id (raw_ml_sorted (raw_arel d'))) (raw_crel id d) () (share_raw_tlv id (raw_ml_sorted (raw_arel d')) (share_raw_ml_sorted (raw_arel d') (share_arel d')))
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    content_adb_none_equiv id ipd prefix kid key_k ls pf pf' dsx dpre;
    share_ext (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id d) ()
      (share_raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx)) (share_iarel dpre (raw_sxrel kid dsx) (share_sxrel kid dsx)))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    share_ext (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id d) ()
      (share_raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))
        (share_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))
          (share_fxrel kid dfx (raw_dfbr kid key_k #fb dfb) (share_raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) (share_terminal kid key_k) (share_irel false dfb)))))
  | CD_VIEW d' ty view mk law ->
    content_view_equiv id d' ty view mk law;
    share_ext (raw_view (raw_crel id d') view) (raw_crel id d) () (share_raw_view (raw_crel id d') view (share_crel id d'))

and share_lcrel (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t)
: Tot (share_t (raw_lcrel d)) (decreases d)
= match d with
  | LC_NIL -> lc_nil_equiv (); share_ext (raw_false unit) (raw_lcrel d) () (share_raw_false unit)
  | LC_SINGLE id' cd -> lc_single_equiv id' cd; share_ext (raw_crel id' cd) (raw_lcrel d) () (share_crel id' cd)
  | LC_CONS id' cd dtl ->
    lc_cons_equiv id' cd dtl;
    share_ext (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel d) ()
      (share_raw_either (raw_crel id' cd) (raw_lcrel dtl) (share_crel id' cd) (share_lcrel dtl))

and share_arel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Tot (share_t (raw_arel d)) (decreases d)
= match d with
  | D_ILC id cd ->
    rel_ilc_equiv id cd;
    share_ext (raw_crel id cd) (raw_arel d) () (share_crel id cd)
  | D_CHOICE lc pf ld ->
    rel_choice_equiv lc pf ld;
    share_ext (raw_lcrel ld) (raw_arel d) () (share_lcrel ld)
  | D_ANY ->
    rel_any_equiv ();
    share_ext raw_slice (raw_arel d) () (share_raw_slice ())
  | D_VIEW d' ty view mk law ->
    rel_view_equiv d' ty view mk law;
    share_ext (raw_view (raw_arel d') view) (raw_arel d) () (share_raw_view (raw_arel d') view (share_arel d'))
  | D_KEEP d' wf ->
    rel_keep_equiv d' wf;
    share_ext (raw_keep (raw_arel d')) (raw_arel d) () (share_raw_keep (raw_arel d') (share_arel d'))

and share_drel (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t)
: Tot (share_t (raw_drel d)) (decreases d)
= match d with
  | DD_PLAIN d' ->
    dec_plain_equiv d';
    share_ext (raw_arel d') (raw_drel d) () (share_arel d')
  | DD_OPTION d' ->
    dec_option_equiv d';
    share_ext (raw_opt (raw_arel d')) (raw_drel d) () (share_raw_opt (raw_arel d') (share_arel d'))
  | DD_DEFAULT id0 #k defv ->
    dec_default_equiv id0 defv;
    share_ext (raw_default_rel id0 k defv) (raw_drel d) () (share_default id0 k defv)
  | DD_DEFAULT_RESTRICTED id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    share_ext (raw_default_rel id0 k defv) (raw_drel d) () (share_default id0 k defv)
  | DD_VIEW d' ty view mk law ->
    dec_view_equiv d' ty view mk law;
    share_ext (raw_view (raw_drel d') view) (raw_drel d) () (share_raw_view (raw_drel d') view (share_drel d'))

and share_irel (srt: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (d: idesc items t)
: Tot (share_t (raw_irel srt d)) (decreases d)
= match d with
  | ID_NIL ->
    items_nil_equiv srt;
    share_ext (raw_pure null_enc) (raw_irel srt d) () (share_raw_pure null_enc)
  | ID_SINGLE dd ->
    items_single_equiv srt dd;
    share_ext (raw_drel dd) (raw_irel srt d) () (share_drel dd)
  | ID_CONS dd dtl ->
    items_cons_equiv srt dd dtl;
    share_ext (raw_join srt (raw_drel dd) (raw_irel srt dtl)) (raw_irel srt d) ()
      (share_raw_join srt (raw_drel dd) (raw_irel srt dtl) (share_drel dd) (share_irel srt dtl))

and share_sxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
: Tot (share_t (raw_sxrel kid d)) (decreases d)
= match d with
  | SX_NIL _ -> adb_nil_equiv kid key_k; share_ext (raw_false unit) (raw_sxrel kid d) () (share_raw_false unit)
  | SX_SINGLE _ kx y di ->
    adb_single_equiv kid kx y di;
    share_ext (raw_dlit kid kx #y di) (raw_sxrel kid d) ()
      (share_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (share_irel false di))
  | SX_CONS _ kx y di dtl ->
    adb_cons_equiv kid kx y di dtl;
    share_ext (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid d) ()
      (share_raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)
        (share_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (share_irel false di))
        (share_sxrel kid dtl))

and share_fxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (fbr: bprel fbt) (xf: share_t fbr)
: Tot (share_t (raw_fxrel kid d fbr)) (decreases d)
= match d with
  | FX_NIL _ -> afb_nil_equiv kid key_k fbr; share_ext fbr (raw_fxrel kid d fbr) () xf
  | FX_SINGLE _ kx y di ->
    afb_single_equiv kid kx y di fbr;
    share_ext (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid d fbr) ()
      (share_raw_either (raw_dlit kid kx #y di) fbr
        (share_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (share_irel false di))
        xf)
  | FX_CONS _ kx y di dtl ->
    afb_cons_equiv kid kx y di dtl fbr;
    share_ext (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid d fbr) ()
      (share_raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)
        (share_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (share_irel false di))
        (share_fxrel kid dtl fbr xf))

and share_iarel (#ids: _) (#items: asn1_gen_items_l ids) (#sfx: Type0) (#t: Type0) (d: iadesc items sfx t) (sr: bprel sfx) (xs: share_t sr)
: Tot (share_t (raw_iarel d sr)) (decreases d)
= match d with
  | IA_NIL ->
    items_any_nil_equiv sr;
    share_ext sr (raw_iarel d sr) () xs
  | IA_SINGLE dd ->
    items_any_single_equiv dd sr;
    share_ext (raw_cat (raw_drel dd) sr) (raw_iarel d sr) ()
      (share_raw_cat (raw_drel dd) sr (share_drel dd) xs)
  | IA_CONS dd dtl ->
    items_any_cons_equiv dd dtl sr;
    share_ext (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) ()
      (share_raw_cat (raw_drel dd) (raw_iarel dtl sr) (share_drel dd) (share_iarel dtl sr xs))

let rec gather_crel (id: asn1_id_t) (#k: asn1_content_k) (#t: Type0) (d: cdesc k t)
: Tot (gather_t (raw_crel id d)) (decreases d)
= match d with
  | CD_TERMINAL k' ->
    content_terminal_equiv id k';
    gather_ext (raw_terminal_rel id k') (raw_crel id d) () (gather_terminal id k')
  | CD_RESTRICTED k' r ->
    content_restricted_equiv id k' r;
    gather_ext (raw_terminal_rel id k') (raw_crel id d) () (gather_terminal id k')
  | CD_PREFIXED d' ->
    content_prefixed_equiv id d';
    gather_ext (raw_tlv id (raw_arel d')) (raw_crel id d) () (gather_raw_tlv id (raw_arel d') (gather_arel d'))
  | CD_SEQUENCE gitems di ->
    content_sequence_equiv id gitems di;
    gather_ext (raw_tlv id (raw_irel false di)) (raw_crel id d) () (gather_raw_tlv id (raw_irel false di) (gather_irel false di))
  | CD_SET ids items pf di ->
    content_set_equiv id ids items pf di;
    gather_ext (raw_tlv id (raw_irel true di)) (raw_crel id d) () (gather_raw_tlv id (raw_irel true di) (gather_irel true di))
  | CD_SEQUENCE_OF ne d' ->
    content_seq_of_equiv id ne d';
    gather_ext (raw_tlv id (raw_ml (raw_arel d'))) (raw_crel id d) () (gather_raw_tlv id (raw_ml (raw_arel d')) (gather_raw_ml (raw_arel d') (gather_arel d')))
  | CD_SET_OF ne d' ->
    content_set_of_equiv id ne d';
    gather_ext (raw_tlv id (raw_ml_sorted (raw_arel d'))) (raw_crel id d) () (gather_raw_tlv id (raw_ml_sorted (raw_arel d')) (gather_raw_ml_sorted (raw_arel d') (gather_arel d')))
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    content_adb_none_equiv id ipd prefix kid key_k ls pf pf' dsx dpre;
    gather_ext (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id d) ()
      (gather_raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx)) (gather_iarel dpre (raw_sxrel kid dsx) (gather_sxrel kid dsx)))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    gather_ext (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id d) ()
      (gather_raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))
        (gather_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))
          (gather_fxrel kid dfx (raw_dfbr kid key_k #fb dfb) (gather_raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) (gather_terminal kid key_k) (gather_irel false dfb)))))
  | CD_VIEW d' ty view mk law ->
    content_view_equiv id d' ty view mk law;
    gather_ext (raw_view (raw_crel id d') view) (raw_crel id d) () (gather_raw_view (raw_crel id d') view (gather_crel id d'))

and gather_lcrel (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t)
: Tot (gather_t (raw_lcrel d)) (decreases d)
= match d with
  | LC_NIL -> lc_nil_equiv (); gather_ext (raw_false unit) (raw_lcrel d) () (gather_raw_false unit)
  | LC_SINGLE id' cd -> lc_single_equiv id' cd; gather_ext (raw_crel id' cd) (raw_lcrel d) () (gather_crel id' cd)
  | LC_CONS id' cd dtl ->
    lc_cons_equiv id' cd dtl;
    gather_ext (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel d) ()
      (gather_raw_either (raw_crel id' cd) (raw_lcrel dtl) (gather_crel id' cd) (gather_lcrel dtl))

and gather_arel (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Tot (gather_t (raw_arel d)) (decreases d)
= match d with
  | D_ILC id cd ->
    rel_ilc_equiv id cd;
    gather_ext (raw_crel id cd) (raw_arel d) () (gather_crel id cd)
  | D_CHOICE lc pf ld ->
    rel_choice_equiv lc pf ld;
    gather_ext (raw_lcrel ld) (raw_arel d) () (gather_lcrel ld)
  | D_ANY ->
    rel_any_equiv ();
    gather_ext raw_slice (raw_arel d) () (gather_raw_slice ())
  | D_VIEW d' ty view mk law ->
    rel_view_equiv d' ty view mk law;
    gather_ext (raw_view (raw_arel d') view) (raw_arel d) () (gather_raw_view (raw_arel d') view (gather_arel d'))
  | D_KEEP d' wf ->
    rel_keep_equiv d' wf;
    gather_ext (raw_keep (raw_arel d')) (raw_arel d) () (gather_raw_keep (raw_arel d') (gather_arel d'))

and gather_drel (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t)
: Tot (gather_t (raw_drel d)) (decreases d)
= match d with
  | DD_PLAIN d' ->
    dec_plain_equiv d';
    gather_ext (raw_arel d') (raw_drel d) () (gather_arel d')
  | DD_OPTION d' ->
    dec_option_equiv d';
    gather_ext (raw_opt (raw_arel d')) (raw_drel d) () (gather_raw_opt (raw_arel d') (gather_arel d'))
  | DD_DEFAULT id0 #k defv ->
    dec_default_equiv id0 defv;
    gather_ext (raw_default_rel id0 k defv) (raw_drel d) () (gather_default id0 k defv)
  | DD_DEFAULT_RESTRICTED id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    gather_ext (raw_default_rel id0 k defv) (raw_drel d) () (gather_default id0 k defv)
  | DD_VIEW d' ty view mk law ->
    dec_view_equiv d' ty view mk law;
    gather_ext (raw_view (raw_drel d') view) (raw_drel d) () (gather_raw_view (raw_drel d') view (gather_drel d'))

and gather_irel (srt: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (d: idesc items t)
: Tot (gather_t (raw_irel srt d)) (decreases d)
= match d with
  | ID_NIL ->
    items_nil_equiv srt;
    gather_ext (raw_pure null_enc) (raw_irel srt d) () (gather_raw_pure null_enc)
  | ID_SINGLE dd ->
    items_single_equiv srt dd;
    gather_ext (raw_drel dd) (raw_irel srt d) () (gather_drel dd)
  | ID_CONS dd dtl ->
    items_cons_equiv srt dd dtl;
    gather_ext (raw_join srt (raw_drel dd) (raw_irel srt dtl)) (raw_irel srt d) ()
      (gather_raw_join srt (raw_drel dd) (raw_irel srt dtl) (gather_drel dd) (gather_irel srt dtl))

and gather_sxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
: Tot (gather_t (raw_sxrel kid d)) (decreases d)
= match d with
  | SX_NIL _ -> adb_nil_equiv kid key_k; gather_ext (raw_false unit) (raw_sxrel kid d) () (gather_raw_false unit)
  | SX_SINGLE _ kx y di ->
    adb_single_equiv kid kx y di;
    gather_ext (raw_dlit kid kx #y di) (raw_sxrel kid d) ()
      (gather_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (gather_irel false di))
  | SX_CONS _ kx y di dtl ->
    adb_cons_equiv kid kx y di dtl;
    gather_ext (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid d) ()
      (gather_raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)
        (gather_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (gather_irel false di))
        (gather_sxrel kid dtl))

and gather_fxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (fbr: bprel fbt) (xf: gather_t fbr)
: Tot (gather_t (raw_fxrel kid d fbr)) (decreases d)
= match d with
  | FX_NIL _ -> afb_nil_equiv kid key_k fbr; gather_ext fbr (raw_fxrel kid d fbr) () xf
  | FX_SINGLE _ kx y di ->
    afb_single_equiv kid kx y di fbr;
    gather_ext (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid d fbr) ()
      (gather_raw_either (raw_dlit kid kx #y di) fbr
        (gather_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (gather_irel false di))
        xf)
  | FX_CONS _ kx y di dtl ->
    afb_cons_equiv kid kx y di dtl fbr;
    gather_ext (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid d fbr) ()
      (gather_raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)
        (gather_raw_pre (WA.raw_key_enc kid key_k kx) (raw_irel false di) (gather_irel false di))
        (gather_fxrel kid dtl fbr xf))

and gather_iarel (#ids: _) (#items: asn1_gen_items_l ids) (#sfx: Type0) (#t: Type0) (d: iadesc items sfx t) (sr: bprel sfx) (xs: gather_t sr)
: Tot (gather_t (raw_iarel d sr)) (decreases d)
= match d with
  | IA_NIL ->
    items_any_nil_equiv sr;
    gather_ext sr (raw_iarel d sr) () xs
  | IA_SINGLE dd ->
    items_any_single_equiv dd sr;
    gather_ext (raw_cat (raw_drel dd) sr) (raw_iarel d sr) ()
      (gather_raw_cat (raw_drel dd) sr (gather_drel dd) xs)
  | IA_CONS dd dtl ->
    items_any_cons_equiv dd dtl sr;
    gather_ext (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) ()
      (gather_raw_cat (raw_drel dd) (raw_iarel dtl sr) (gather_drel dd) (gather_iarel dtl sr xs))

(* The shares and gathers of the legacy relations *)

let share_k (#s: _) (k: asn1_k s) : share_t (raw_rel k) = share_arel (legacy_adesc k)
let gather_k (#s: _) (k: asn1_k s) : gather_t (raw_rel k) = gather_arel (legacy_adesc k)
let share_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : share_t (raw_dec_rel dk) = share_drel (legacy_ddesc dk)
let gather_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : gather_t (raw_dec_rel dk) = gather_drel (legacy_ddesc dk)
let share_items (srt: bool) (#i: _) (ls: asn1_gen_items_l i) : share_t (raw_items_rel srt ls) = share_irel srt (legacy_idesc ls)
let gather_items (srt: bool) (#i: _) (ls: asn1_gen_items_l i) : gather_t (raw_items_rel srt ls) = gather_irel srt (legacy_idesc ls)
