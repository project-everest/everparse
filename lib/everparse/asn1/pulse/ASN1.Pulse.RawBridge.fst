module ASN1.Pulse.RawBridge
#lang-pulse

(* Bridging the raw value relation `asn1_raw_rel k` (the Pulse
   representation `x` of a raw value `y: asn1_raw_t k`) and the raw byte
   relation `raw_rel k` (the bytes `w` the raw writer writes for `x`):
   - `split`: `asn1_raw_rel k pm x y` can be split into
     `asn1_raw_rel k (pm / 2) x y ** raw_rel k (pm / 2) x (rb k y)`;
   - `absorb`: `asn1_raw_rel k p1 x y ** raw_rel k p2 x w` can be absorbed
     back into `asn1_raw_rel k (p1 + p2) x y`, whatever `w`.
   Thus the raw JIT writer, which preserves `raw_rel k pm x w`, can be run
   on a raw value, and writes `rb k y` (`ASN1.Pulse.RawBytes`.) *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Spec.Raw
open ASN1.Spec.Raw.Props
open ASN1.Pulse.RawValueRel
open ASN1.Pulse.RawRel
open ASN1.Pulse.RawBytes
open ASN1.Spec.ToValue

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module I64 = FStar.Int64
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module It = LowParse.PulseParse.Iterator
module Het = LowParse.PulseParse.Iterator.Het
module W = LowParse.Pulse.R2L
module SI = ASN1.Pulse.SortedInsert
module Ser = ASN1.Spec.Serializer
module L = ASN1.Pulse.JitWriter.Lemmas
module PS = ASN1.Pulse.ParseSequence
module PA = ASN1.Pulse.ParseAdb
module WA = ASN1.Pulse.WriteAdb
module In = ASN1.Pulse.Interpreter
module RVR = ASN1.Pulse.RawValueRel
module RR = ASN1.Pulse.RawRel
module RB = ASN1.Pulse.RawBytes
module Can = ASN1.Spec.Raw.Canonical
module Conf = ASN1.Spec.Conformance

(* The element parsers of SEQUENCE OF / SET OF: whatever the raw element
   parser accepts, the TLV parser `p_raw` accepts too, as its bytes `rb` *)

let rb_r (#s: _) (k: asn1_k s) (a: asn1_raw_t k) (w: SB.bytes) : prop = w == rb k a

let p_any_eq (_: unit) : Lemma (p_any == asn1_as_parser ASN1_ANY_ILC) = ()

let to_value_any (v: asn1_value) : Lemma (to_value ASN1_ANY_ILC v == v) =
  assert (to_value ASN1_ANY_ILC v == v) by (FStar.Tactics.V2.trefl ())

#push-options "--z3rlimit 32"
let any_acc (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma (requires (ASN1.Spec.Conformance.wf k /\ Ser.encodable k x))
  (ensures (match SB.parse p_any (Ser.asn1_enc k x) with
    | Some (v', n) -> v' == to_value k x /\ n == Seq.length (Ser.asn1_enc k x)
    | None -> False))
= let e = Ser.asn1_enc k x in
  ASN1.Spec.Conformance.conformance_correct k e;
  p_any_eq ();
  Ser.asn1_as_parser_consumed ASN1_ANY_ILC e;
  let Some (v', n) = SB.parse p_any e in
  assert (Seq.equal (Seq.slice e 0 n) e);
  to_value_any v';
  asn1_value_enc_inj v' (to_value k x)
#pop-options

#push-options "--z3rlimit 64"
let rb_parse_raw (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (b: SB.bytes)
: Lemma (match SB.parse (parse_raw k) b with
    | None -> True
    | Some (v1, c1) ->
      begin match SB.parse p_raw b with
      | Some (v2, c2) -> rb_r k v1 v2 /\ c1 == c2
      | None -> False
      end)
= parse_raw_eq k b;
  match SB.parse (asn1_as_parser k) b with
  | None -> ()
  | Some (x, n) ->
    Ser.parsed_spec_correct k b;
    Can.encodable_canonical k () x;
    check_ser_forget k () x;
    rb_check_ser k u (forget k x);
    let e = Ser.asn1_enc k x in
    let v = to_value k x in
    any_acc k x;
    SB.parse_strong_prefix p_any e b;
    any_enc_injective ();
    SC.parse_synth_eq p_any any_enc b
#pop-options

let rb_parsers_fwd (#s: _) (k: asn1_k s) (u: squash (raw_ok k))
: Lemma (Het.parsers_fwd #asn1_strong_parser_kind (parse_raw k) p_raw (rb_r k))
= Classical.forall_intro (rb_parse_raw k u)

let rb_r_functional (#s: _) (k: asn1_k s)
: Lemma (Het.rel_functional (rb_r k))
= ()

let rec rb_list_rel (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k))
: Lemma (ensures (Het.list_rel (rb_r k) l (rb_list k l))) (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> rb_list_rel k q

(* Bridges *)

let split_t (#t: Type0) (#u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) : Type =
  (pm: perm) -> (x: t) -> (y: u) ->
  stt_ghost unit emp_inames (a pm x y) (fun _ -> a (pm /. 2.0R) x y ** r (pm /. 2.0R) x (f y))

let absorb_t (#t: Type0) (#u: Type0) (a: prel t u) (r: bprel t) : Type =
  (p1: perm) -> (p2: perm) -> (x: t) -> (y: u) -> (w: SB.bytes) ->
  stt_ghost unit emp_inames (a p1 x y ** r p2 x w) (fun _ -> a (p1 +. p2) x y)

noeq
type br_t (#t: Type0) (#u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) = {
  sp: split_t a r f;
  ab: absorb_t a r;
}

ghost
fn split_ext (#t: Type0) (#u: Type0) (a a': prel t u) (r r': bprel t) (f f': u -> GTot SB.bytes)
  (sq: squash (pequiv a a' /\ RR.prel_equiv r r' /\ (forall y . f y == f' y)))
  (c: split_t a r f)
: split_t a' r' f'
= (pm: perm) (x: t) (y: u)
{
  rewrite (a' pm x y) as (a pm x y);
  c pm x y;
  rewrite (a (pm /. 2.0R) x y) as (a' (pm /. 2.0R) x y);
  rewrite (r (pm /. 2.0R) x (f y)) as (r' (pm /. 2.0R) x (f' y))
}

ghost
fn absorb_ext (#t: Type0) (#u: Type0) (a a': prel t u) (r r': bprel t)
  (sq: squash (pequiv a a' /\ RR.prel_equiv r r'))
  (c: absorb_t a r)
: absorb_t a' r'
= (p1: perm) (p2: perm) (x: t) (y: u) (w: SB.bytes)
{
  rewrite (a' p1 x y) as (a p1 x y);
  rewrite (r' p2 x w) as (r p2 x w);
  c p1 p2 x y w;
  rewrite (a (p1 +. p2) x y) as (a' (p1 +. p2) x y)
}

let br_ext (#t: Type0) (#u: Type0) (a a': prel t u) (r r': bprel t) (f f': u -> GTot SB.bytes)
  (sq: squash (pequiv a a' /\ RR.prel_equiv r r' /\ (forall y . f y == f' y)))
  (c: br_t a r f)
: br_t a' r' f'
= { sp = split_ext a a' r r' f f' sq c.sp; ab = absorb_ext a a' r r' sq c.ab }

(* Leaves *)

ghost
fn split_slice (#u: Type0) (e: u -> GTot SB.bytes)
: split_t #(S.slice U8.t) #u (prel_slice_ser e) raw_slice e
= (pm: perm) (x: S.slice U8.t) (y: u)
{
  unfold (prel_slice_ser e pm x y);
  S.share x;
  fold (prel_slice_ser e (pm /. 2.0R) x y);
  fold (prel_slice_ser id_enc (pm /. 2.0R) x (e y));
  fold (raw_slice (pm /. 2.0R) x (e y))
}

ghost
fn absorb_slice (#u: Type0) (e: u -> GTot SB.bytes)
: absorb_t #(S.slice U8.t) #u (prel_slice_ser e) raw_slice
= (p1: perm) (p2: perm) (x: S.slice U8.t) (y: u) (w: SB.bytes)
{
  unfold (prel_slice_ser e p1 x y);
  unfold (raw_slice p2 x w);
  unfold (prel_slice_ser id_enc p2 x w);
  S.gather x;
  fold (prel_slice_ser e (p1 +. p2) x y)
}

let br_slice (#u: Type0) (e: u -> GTot SB.bytes) : br_t #(S.slice U8.t) #u (prel_slice_ser e) raw_slice e =
  { sp = split_slice e; ab = absorb_slice e }

(* Pure relations, on both sides *)

ghost
fn split_pure (#t: Type0) (#u: Type0) (a: prel t u) (g: t -> GTot SB.bytes) (f: u -> GTot SB.bytes)
  (dup: (pm: perm) -> (pm': perm) -> (x: t) -> (y: u) -> stt_ghost unit emp_inames (a pm x y) (fun _ -> a pm' x y ** pure (g x == f y)))
: split_t a (raw_pure g) f
= (pm: perm) (x: t) (y: u)
{
  dup pm (pm /. 2.0R) x y;
  fold (raw_pure g (pm /. 2.0R) x (f y))
}

ghost
fn absorb_pure (#t: Type0) (#u: Type0) (a: prel t u) (g: t -> GTot SB.bytes) (f: u -> GTot SB.bytes)
  (dup: (pm: perm) -> (pm': perm) -> (x: t) -> (y: u) -> stt_ghost unit emp_inames (a pm x y) (fun _ -> a pm' x y ** pure (g x == f y)))
: absorb_t a (raw_pure g)
= (p1: perm) (p2: perm) (x: t) (y: u) (w: SB.bytes)
{
  unfold (raw_pure g p2 x w);
  dup p1 (p1 +. p2) x y;
  ()
}

let br_pure (#t: Type0) (#u: Type0) (a: prel t u) (g: t -> GTot SB.bytes) (f: u -> GTot SB.bytes)
  (dup: (pm: perm) -> (pm': perm) -> (x: t) -> (y: u) -> stt_ghost unit emp_inames (a pm x y) (fun _ -> a pm' x y ** pure (g x == f y)))
: br_t a (raw_pure g) f
= { sp = split_pure a g f dup; ab = absorb_pure a g f dup }

ghost
fn dup_bool (pm pm': perm) (x: bool) (y: bool)
requires prel_eq bool pm x y
ensures prel_eq bool pm' x y ** pure (boolean_enc x == raw_leaf_enc ASN1_BOOLEAN y)
{
  unfold (prel_eq bool pm x y);
  fold (prel_eq bool pm' x y)
}

ghost
fn dup_null (pm pm': perm) (x: unit) (y: unit)
requires prel_emp unit unit pm x y
ensures prel_emp unit unit pm' x y ** pure (null_enc x == raw_leaf_enc ASN1_NULL y)
{
  unfold (prel_emp unit unit pm x y);
  fold (prel_emp unit unit pm' x y);
  assert (pure (Seq.equal (null_enc x) (raw_leaf_enc ASN1_NULL y)))
}

ghost
fn dup_small (bound: pos) (pm pm': perm) (x: I64.t) (y: int)
requires raw_small_int_rel pm x y
ensures raw_small_int_rel pm' x y ** pure (i64_enc x == raw_leaf_enc (ASN1_INTEGER bound) y)
{
  unfold (raw_small_int_rel pm x y);
  fold (raw_small_int_rel pm' x y)
}

ghost
fn split_int (bound: pos)
: split_t #asn1_int_impl #int (raw_int_rel bound) raw_int (raw_leaf_enc (ASN1_INTEGER bound))
= (pm: perm) (x: asn1_int_impl) (y: int)
{
  half_perm_pos pm;
  match x {
    Small i -> {
      rewrite (raw_int_rel bound pm x y) as (pure (I64.v i == y));
      assert (pure (i64_enc i == raw_leaf_enc (ASN1_INTEGER bound) y));
      rewrite (pure (I64.v i == y)) as (raw_int_rel bound (pm /. 2.0R) x y);
      rewrite (pure (raw_leaf_enc (ASN1_INTEGER bound) y == i64_enc i)) as (raw_int (pm /. 2.0R) x (raw_leaf_enc (ASN1_INTEGER bound) y))
    }
    Big s -> {
      rewrite (raw_int_rel bound pm x y) as (prel_slice_ser (raw_leaf_enc (ASN1_INTEGER bound)) pm s y ** pure (~ (fits_i64 y)));
      split_slice (raw_leaf_enc (ASN1_INTEGER bound)) pm s y;
      rewrite (prel_slice_ser (raw_leaf_enc (ASN1_INTEGER bound)) (pm /. 2.0R) s y ** pure (~ (fits_i64 y))) as (raw_int_rel bound (pm /. 2.0R) x y);
      rewrite (raw_slice (pm /. 2.0R) s (raw_leaf_enc (ASN1_INTEGER bound) y)) as (raw_int (pm /. 2.0R) x (raw_leaf_enc (ASN1_INTEGER bound) y))
    }
  }
}

ghost
fn absorb_int (bound: pos)
: absorb_t #asn1_int_impl #int (raw_int_rel bound) raw_int
= (p1: perm) (p2: perm) (x: asn1_int_impl) (y: int) (w: SB.bytes)
{
  match x {
    Small i -> {
      rewrite (raw_int_rel bound p1 x y) as (pure (I64.v i == y));
      rewrite (raw_int p2 x w) as (pure (w == i64_enc i));
      rewrite (pure (I64.v i == y)) as (raw_int_rel bound (p1 +. p2) x y)
    }
    Big s -> {
      rewrite (raw_int_rel bound p1 x y) as (prel_slice_ser (raw_leaf_enc (ASN1_INTEGER bound)) p1 s y ** pure (~ (fits_i64 y)));
      rewrite (raw_int p2 x w) as (raw_slice p2 s w);
      absorb_slice (raw_leaf_enc (ASN1_INTEGER bound)) p1 p2 s y w;
      rewrite (prel_slice_ser (raw_leaf_enc (ASN1_INTEGER bound)) (p1 +. p2) s y ** pure (~ (fits_i64 y))) as (raw_int_rel bound (p1 +. p2) x y)
    }
  }
}

ghost
fn split_bitstring (_: unit)
: split_t #asn1_bitstring_impl #(U8.t & ASN1.Bytes.asn1_bytes) raw_bitstring_rel raw_bitstring (raw_leaf_enc ASN1_BITSTRING)
= (pm: perm) (x: asn1_bitstring_impl) (y: (U8.t & ASN1.Bytes.asn1_bytes))
{
  unfold (raw_bitstring_rel pm x y);
  S.share x.bytes;
  fold (raw_bitstring_rel (pm /. 2.0R) x y);
  assert (pure (Seq.equal (raw_leaf_enc ASN1_BITSTRING y) (Seq.append (W.enc_byte x.unused) (snd y))));
  fold (raw_bitstring (pm /. 2.0R) x (raw_leaf_enc ASN1_BITSTRING y))
}

ghost
fn absorb_bitstring (_: unit)
: absorb_t #asn1_bitstring_impl #(U8.t & ASN1.Bytes.asn1_bytes) raw_bitstring_rel raw_bitstring
= (p1: perm) (p2: perm) (x: asn1_bitstring_impl) (y: (U8.t & ASN1.Bytes.asn1_bytes)) (w: SB.bytes)
{
  unfold (raw_bitstring_rel p1 x y);
  unfold (raw_bitstring p2 x w);
  S.gather x.bytes;
  fold (raw_bitstring_rel (p1 +. p2) x y)
}

let br_integer (bound: pos) : br_t (asn1_raw_terminal_rel (ASN1_INTEGER bound)) (raw_leaf (ASN1_INTEGER bound)) (raw_leaf_enc (ASN1_INTEGER bound)) =
  if small_integer bound
  then coerce_eq () (br_pure raw_small_int_rel i64_enc (raw_leaf_enc (ASN1_INTEGER bound)) (dup_small bound))
  else coerce_eq () ({ sp = split_int bound; ab = absorb_int bound })

let br_leaf (k: leaf_k) : br_t (asn1_raw_terminal_rel k) (raw_leaf k) (raw_leaf_enc k) =
  match k with
  | ASN1_BOOLEAN -> coerce_eq () (br_pure (prel_eq bool) boolean_enc (raw_leaf_enc ASN1_BOOLEAN) dup_bool)
  | ASN1_NULL -> coerce_eq () (br_pure (prel_emp unit unit) null_enc (raw_leaf_enc ASN1_NULL) dup_null)
  | ASN1_INTEGER bound -> br_integer bound
  | ASN1_BITSTRING -> coerce_eq () ({ sp = split_bitstring (); ab = absorb_bitstring () })
  | _ -> coerce_eq () (br_slice (raw_leaf_enc k))

(* TLV *)

let f_tlv (id: asn1_id_t) (#u: Type0) (f: u -> GTot SB.bytes) (y: u) : GTot SB.bytes = enc_tlv id true (f y)

ghost
fn split_tlv (id: asn1_id_t) (#t: Type0) (#u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) (c: split_t a r f)
: split_t a (raw_tlv id r) (f_tlv id f)
= (pm: perm) (x: t) (y: u)
{
  c pm x y;
  fold (raw_tlv id r (pm /. 2.0R) x (f_tlv id f y))
}

ghost
fn absorb_tlv (id: asn1_id_t) (#t: Type0) (#u: Type0) (a: prel t u) (r: bprel t) (c: absorb_t a r)
: absorb_t a (raw_tlv id r)
= (p1: perm) (p2: perm) (x: t) (y: u) (w: SB.bytes)
{
  unfold (raw_tlv id r p2 x w);
  with w' . assert (r p2 x w');
  c p1 p2 x y w'
}

let br_tlv (id: asn1_id_t) (#t: Type0) (#u: Type0) (#a: prel t u) (#r: bprel t) (#f: u -> GTot SB.bytes) (c: br_t a r f)
: br_t a (raw_tlv id r) (f_tlv id f)
= { sp = split_tlv id a r f c.sp; ab = absorb_tlv id a r c.ab }

(* Terminals *)

let raw_down (id2: asn1_id_t) (k2: asn1_terminal_k) (y: asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) : Tot (asn1_raw_terminal_t k2) =
  assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_raw_terminal_t k2);
  coerce_eq () y

let raw_terminal_prefixed_eq (id2: asn1_id_t) (k2: asn1_terminal_k) (pm: perm) (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (y: asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2))
: Lemma (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) pm x y == asn1_raw_terminal_rel k2 pm (prefixed_down id2 k2 x) (raw_down id2 k2 y))
= assert (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) pm x y == asn1_raw_terminal_rel k2 pm (prefixed_down id2 k2 x) (raw_down id2 k2 y))
    by (FStar.Tactics.V2.norm [delta_only [`%asn1_raw_terminal_rel; `%prefixed_down; `%raw_down; `%coerce_eq]; zeta; iota]; FStar.Tactics.V2.trefl ())

let rb_term_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (y: asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2))
: Lemma (rb_term id (ASN1_PREFIXED_TERMINAL id2 k2) y == f_tlv id (rb_term id2 k2) (raw_down id2 k2 y))
= assert_norm (rb_term id (ASN1_PREFIXED_TERMINAL id2 k2) y == enc_tlv id true (rb_term id2 k2 (raw_down id2 k2 y)))

ghost
fn split_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (c: split_t (asn1_raw_terminal_rel k2) (raw_terminal_rel id2 k2) (rb_term id2 k2))
: split_t #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) #(asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2))
    (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2)) (rb_term id (ASN1_PREFIXED_TERMINAL id2 k2))
= (pm: perm) (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (y: asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2))
{
  raw_terminal_prefixed_eq id2 k2 pm x y;
  raw_terminal_prefixed_eq id2 k2 (pm /. 2.0R) x y;
  terminal_prefixed_eq id id2 k2 (pm /. 2.0R) x (rb_term id (ASN1_PREFIXED_TERMINAL id2 k2) y);
  rb_term_prefixed id id2 k2 y;
  let x' = prefixed_down id2 k2 x;
  rewrite (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) pm x y) as (asn1_raw_terminal_rel k2 pm x' (raw_down id2 k2 y));
  split_tlv id (asn1_raw_terminal_rel k2) (raw_terminal_rel id2 k2) (rb_term id2 k2) c pm x' (raw_down id2 k2 y);
  rewrite (asn1_raw_terminal_rel k2 (pm /. 2.0R) x' (raw_down id2 k2 y)) as (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) (pm /. 2.0R) x y);
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) (pm /. 2.0R) x' (f_tlv id (rb_term id2 k2) (raw_down id2 k2 y)))
    as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) (pm /. 2.0R) x (rb_term id (ASN1_PREFIXED_TERMINAL id2 k2) y))
}

ghost
fn absorb_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (c: absorb_t (asn1_raw_terminal_rel k2) (raw_terminal_rel id2 k2))
: absorb_t #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) #(asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2))
    (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2))
= (p1: perm) (p2: perm) (x: asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (y: asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) (w: SB.bytes)
{
  raw_terminal_prefixed_eq id2 k2 p1 x y;
  raw_terminal_prefixed_eq id2 k2 (p1 +. p2) x y;
  terminal_prefixed_eq id id2 k2 p2 x w;
  let x' = prefixed_down id2 k2 x;
  rewrite (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) p1 x y) as (asn1_raw_terminal_rel k2 p1 x' (raw_down id2 k2 y));
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) p2 x w) as (raw_tlv id (raw_terminal_rel id2 k2) p2 x' w);
  absorb_tlv id (asn1_raw_terminal_rel k2) (raw_terminal_rel id2 k2) c p1 p2 x' (raw_down id2 k2 y) w;
  rewrite (asn1_raw_terminal_rel k2 (p1 +. p2) x' (raw_down id2 k2 y)) as (asn1_raw_terminal_rel (ASN1_PREFIXED_TERMINAL id2 k2) (p1 +. p2) x y)
}

let rb_term_leaf (id: asn1_id_t) (k: leaf_k)
: Lemma (forall y . f_tlv id (raw_leaf_enc k) y == rb_term id k y)
= ()

let rec br_term (id: asn1_id_t) (k: asn1_terminal_k) : Tot (br_t (asn1_raw_terminal_rel k) (raw_terminal_rel id k) (rb_term id k)) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    let c = br_term id2 k2 in
    { sp = split_prefixed id id2 k2 c.sp; ab = absorb_prefixed id id2 k2 c.ab }
  | _ ->
    terminal_leaf_equiv id k;
    rb_term_leaf id k;
    br_ext (asn1_raw_terminal_rel k) (asn1_raw_terminal_rel k) (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) (f_tlv id (raw_leaf_enc k)) (rb_term id k) ()
      (br_tlv id (br_leaf k))

(* Pairs *)

let f_cat (#u1 #u2: Type0) (f1: u1 -> GTot SB.bytes) (f2: u2 -> GTot SB.bytes) (y: u1 & u2) : GTot SB.bytes =
  Seq.append (f1 (fst y)) (f2 (snd y))

let f_ins (lt: SI.lt_t) (#u1 #u2: Type0) (f1: u1 -> GTot SB.bytes) (f2: u2 -> GTot SB.bytes) (y: u1 & u2) : GTot SB.bytes =
  SI.ins lt (f1 (fst y)) (f2 (snd y))

let f_join (srt: bool) (#u1 #u2: Type0) (f1: u1 -> GTot SB.bytes) (f2: u2 -> GTot SB.bytes) (y: u1 & u2) : GTot SB.bytes =
  if srt then f_ins SI.lt_tag f1 f2 y else f_cat f1 f2 y

ghost
fn split_cat (#t1 #t2 #u1 #u2: Type0) (a1: prel t1 u1) (a2: prel t2 u2) (r1: bprel t1) (r2: bprel t2) (f1: u1 -> GTot SB.bytes) (f2: u2 -> GTot SB.bytes)
  (c1: split_t a1 r1 f1) (c2: split_t a2 r2 f2)
: split_t (prel_pair a1 a2) (raw_cat r1 r2) (f_cat f1 f2)
= (pm: perm) (x: (t1 & t2)) (y: (u1 & u2))
{
  unfold (prel_pair a1 a2 pm x y);
  c1 pm (fst x) (fst y);
  c2 pm (snd x) (snd y);
  fold (prel_pair a1 a2 (pm /. 2.0R) x y);
  fold (raw_cat r1 r2 (pm /. 2.0R) x (f_cat f1 f2 y))
}

ghost
fn absorb_cat (#t1 #t2 #u1 #u2: Type0) (a1: prel t1 u1) (a2: prel t2 u2) (r1: bprel t1) (r2: bprel t2)
  (c1: absorb_t a1 r1) (c2: absorb_t a2 r2)
: absorb_t (prel_pair a1 a2) (raw_cat r1 r2)
= (p1: perm) (p2: perm) (x: (t1 & t2)) (y: (u1 & u2)) (w: SB.bytes)
{
  unfold (prel_pair a1 a2 p1 x y);
  unfold (raw_cat r1 r2 p2 x w);
  with w1 w2 . assert (r1 p2 (fst x) w1 ** r2 p2 (snd x) w2);
  c1 p1 p2 (fst x) (fst y) w1;
  c2 p1 p2 (snd x) (snd y) w2;
  fold (prel_pair a1 a2 (p1 +. p2) x y)
}

ghost
fn split_ins (lt: SI.lt_t) (#t1 #t2 #u1 #u2: Type0) (a1: prel t1 u1) (a2: prel t2 u2) (r1: bprel t1) (r2: bprel t2) (f1: u1 -> GTot SB.bytes) (f2: u2 -> GTot SB.bytes)
  (c1: split_t a1 r1 f1) (c2: split_t a2 r2 f2)
: split_t (prel_pair a1 a2) (raw_ins lt r1 r2) (f_ins lt f1 f2)
= (pm: perm) (x: (t1 & t2)) (y: (u1 & u2))
{
  unfold (prel_pair a1 a2 pm x y);
  c1 pm (fst x) (fst y);
  c2 pm (snd x) (snd y);
  fold (prel_pair a1 a2 (pm /. 2.0R) x y);
  fold (raw_ins lt r1 r2 (pm /. 2.0R) x (f_ins lt f1 f2 y))
}

ghost
fn absorb_ins (lt: SI.lt_t) (#t1 #t2 #u1 #u2: Type0) (a1: prel t1 u1) (a2: prel t2 u2) (r1: bprel t1) (r2: bprel t2)
  (c1: absorb_t a1 r1) (c2: absorb_t a2 r2)
: absorb_t (prel_pair a1 a2) (raw_ins lt r1 r2)
= (p1: perm) (p2: perm) (x: (t1 & t2)) (y: (u1 & u2)) (w: SB.bytes)
{
  unfold (prel_pair a1 a2 p1 x y);
  unfold (raw_ins lt r1 r2 p2 x w);
  with w1 w2 . assert (r1 p2 (fst x) w1 ** r2 p2 (snd x) w2);
  c1 p1 p2 (fst x) (fst y) w1;
  c2 p1 p2 (snd x) (snd y) w2;
  fold (prel_pair a1 a2 (p1 +. p2) x y)
}

let br_cat (#t1 #t2 #u1 #u2: Type0) (#a1: prel t1 u1) (#a2: prel t2 u2) (#r1: bprel t1) (#r2: bprel t2) (#f1: u1 -> GTot SB.bytes) (#f2: u2 -> GTot SB.bytes)
  (c1: br_t a1 r1 f1) (c2: br_t a2 r2 f2)
: br_t (prel_pair a1 a2) (raw_cat r1 r2) (f_cat f1 f2)
= { sp = split_cat a1 a2 r1 r2 f1 f2 c1.sp c2.sp; ab = absorb_cat a1 a2 r1 r2 c1.ab c2.ab }

let br_ins (lt: SI.lt_t) (#t1 #t2 #u1 #u2: Type0) (#a1: prel t1 u1) (#a2: prel t2 u2) (#r1: bprel t1) (#r2: bprel t2) (#f1: u1 -> GTot SB.bytes) (#f2: u2 -> GTot SB.bytes)
  (c1: br_t a1 r1 f1) (c2: br_t a2 r2 f2)
: br_t (prel_pair a1 a2) (raw_ins lt r1 r2) (f_ins lt f1 f2)
= { sp = split_ins lt a1 a2 r1 r2 f1 f2 c1.sp c2.sp; ab = absorb_ins lt a1 a2 r1 r2 c1.ab c2.ab }

let br_join (srt: bool) (#t1 #t2 #u1 #u2: Type0) (#a1: prel t1 u1) (#a2: prel t2 u2) (#r1: bprel t1) (#r2: bprel t2) (#f1: u1 -> GTot SB.bytes) (#f2: u2 -> GTot SB.bytes)
  (c1: br_t a1 r1 f1) (c2: br_t a2 r2 f2)
: br_t (prel_pair a1 a2) (raw_join srt r1 r2) (f_join srt f1 f2)
= if srt
  then (join_ins_equiv srt r1 r2; br_ext _ _ _ _ _ _ () (br_ins SI.lt_tag c1 c2))
  else (join_cat_equiv srt r1 r2; br_ext _ _ _ _ _ _ () (br_cat c1 c2))

(* Options *)

let f_opt (#u: Type0) (f: u -> GTot SB.bytes) (y: option u) : GTot SB.bytes =
  match y with None -> Seq.empty | Some z -> f z

let f_opt_nd (d: SB.bytes) (#u: Type0) (f: u -> GTot SB.bytes) (y: option u) : GTot SB.bytes =
  match y with
  | None -> Seq.empty
  | Some z -> if FStar.IndefiniteDescription.strong_excluded_middle (f z == d) then Seq.empty else f z

ghost
fn split_opt (#t #u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) (c: split_t a r f)
: split_t (prel_option a) (raw_opt r) (f_opt f)
= (pm: perm) (x: option t) (y: option u)
{
  match x {
    None -> {
      match y {
        None -> {
          rewrite (prel_option a pm x y) as (prel_option a (pm /. 2.0R) x y);
          rewrite (pure (f_opt f y == Seq.empty)) as (raw_opt r (pm /. 2.0R) x (f_opt f y))
        }
        Some _ -> {
          rewrite (prel_option a pm x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some x1 -> {
      match y {
        None -> {
          rewrite (prel_option a pm x y) as (pure False);
          unreachable ()
        }
        Some y1 -> {
          rewrite (prel_option a pm x y) as (a pm x1 y1);
          c pm x1 y1;
          rewrite (a (pm /. 2.0R) x1 y1) as (prel_option a (pm /. 2.0R) x y);
          rewrite (r (pm /. 2.0R) x1 (f y1)) as (raw_opt r (pm /. 2.0R) x (f_opt f y))
        }
      }
    }
  }
}

ghost
fn absorb_opt (#t #u: Type0) (a: prel t u) (r: bprel t) (c: absorb_t a r)
: absorb_t (prel_option a) (raw_opt r)
= (p1: perm) (p2: perm) (x: option t) (y: option u) (w: SB.bytes)
{
  match x {
    None -> {
      rewrite (raw_opt r p2 x w) as (pure (w == Seq.empty));
      match y {
        None -> {
          rewrite (prel_option a p1 x y) as (prel_option a (p1 +. p2) x y)
        }
        Some _ -> {
          rewrite (prel_option a p1 x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some x1 -> {
      rewrite (raw_opt r p2 x w) as (r p2 x1 w);
      match y {
        None -> {
          rewrite (prel_option a p1 x y) as (pure False);
          unreachable ()
        }
        Some y1 -> {
          rewrite (prel_option a p1 x y) as (a p1 x1 y1);
          c p1 p2 x1 y1 w;
          rewrite (a (p1 +. p2) x1 y1) as (prel_option a (p1 +. p2) x y)
        }
      }
    }
  }
}

let br_opt (#t #u: Type0) (#a: prel t u) (#r: bprel t) (#f: u -> GTot SB.bytes) (c: br_t a r f)
: br_t (prel_option a) (raw_opt r) (f_opt f)
= { sp = split_opt a r f c.sp; ab = absorb_opt a r c.ab }

ghost
fn split_opt_nd (d: SB.bytes) (#t #u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) (c: split_t a r f)
: split_t (prel_option a) (raw_opt_nd d r) (f_opt_nd d f)
= (pm: perm) (x: option t) (y: option u)
{
  match x {
    None -> {
      match y {
        None -> {
          rewrite (prel_option a pm x y) as (prel_option a (pm /. 2.0R) x y);
          rewrite (pure (f_opt_nd d f y == Seq.empty)) as (raw_opt_nd d r (pm /. 2.0R) x (f_opt_nd d f y))
        }
        Some _ -> {
          rewrite (prel_option a pm x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some x1 -> {
      match y {
        None -> {
          rewrite (prel_option a pm x y) as (pure False);
          unreachable ()
        }
        Some y1 -> {
          rewrite (prel_option a pm x y) as (a pm x1 y1);
          c pm x1 y1;
          rewrite (a (pm /. 2.0R) x1 y1) as (prel_option a (pm /. 2.0R) x y);
          let w = f_opt_nd d f y;
          assert (pure ((f y1 == d ==> w == Seq.empty) /\ (~ (f y1 == d) ==> w == f y1)));
          fold (raw_opt_nd d r (pm /. 2.0R) (Some x1) w);
          rewrite (raw_opt_nd d r (pm /. 2.0R) (Some x1) w) as (raw_opt_nd d r (pm /. 2.0R) x (f_opt_nd d f y))
        }
      }
    }
  }
}

ghost
fn absorb_opt_nd (d: SB.bytes) (#t #u: Type0) (a: prel t u) (r: bprel t) (c: absorb_t a r)
: absorb_t (prel_option a) (raw_opt_nd d r)
= (p1: perm) (p2: perm) (x: option t) (y: option u) (w: SB.bytes)
{
  match x {
    None -> {
      rewrite (raw_opt_nd d r p2 x w) as (pure (w == Seq.empty));
      match y {
        None -> {
          rewrite (prel_option a p1 x y) as (prel_option a (p1 +. p2) x y)
        }
        Some _ -> {
          rewrite (prel_option a p1 x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some x1 -> {
      rewrite (raw_opt_nd d r p2 x w) as (raw_opt_nd d r p2 (Some x1) w);
      unfold (raw_opt_nd d r p2 (Some x1) w);
      with cc . assert (r p2 x1 cc);
      match y {
        None -> {
          rewrite (prel_option a p1 x y) as (pure False);
          unreachable ()
        }
        Some y1 -> {
          rewrite (prel_option a p1 x y) as (a p1 x1 y1);
          c p1 p2 x1 y1 cc;
          rewrite (a (p1 +. p2) x1 y1) as (prel_option a (p1 +. p2) x y)
        }
      }
    }
  }
}

let br_opt_nd (d: SB.bytes) (#t #u: Type0) (#a: prel t u) (#r: bprel t) (#f: u -> GTot SB.bytes) (c: br_t a r f)
: br_t (prel_option a) (raw_opt_nd d r) (f_opt_nd d f)
= { sp = split_opt_nd d a r f c.sp; ab = absorb_opt_nd d a r c.ab }

(* Constant prefixes *)

let f_pre (e: SB.bytes) (#u: Type0) (f: u -> GTot SB.bytes) (y: u) : GTot SB.bytes = Seq.append e (f y)

ghost
fn split_pre (e: SB.bytes) (#t #u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) (c: split_t a r f)
: split_t a (raw_pre e r) (f_pre e f)
= (pm: perm) (x: t) (y: u)
{
  c pm x y;
  fold (raw_pre e r (pm /. 2.0R) x (f_pre e f y))
}

ghost
fn absorb_pre (e: SB.bytes) (#t #u: Type0) (a: prel t u) (r: bprel t) (c: absorb_t a r)
: absorb_t a (raw_pre e r)
= (p1: perm) (p2: perm) (x: t) (y: u) (w: SB.bytes)
{
  unfold (raw_pre e r p2 x w);
  with w' . assert (r p2 x w');
  c p1 p2 x y w'
}

let br_pre (e: SB.bytes) (#t #u: Type0) (#a: prel t u) (#r: bprel t) (#f: u -> GTot SB.bytes) (c: br_t a r f)
: br_t a (raw_pre e r) (f_pre e f)
= { sp = split_pre e a r f c.sp; ab = absorb_pre e a r c.ab }

(* Reindexing the value *)

ghost
fn split_map (#t #u #u': Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes) (c: split_t a r f)
  (a': prel t u') (f': u' -> GTot SB.bytes) (g: u' -> GTot u)
  (sq: squash ((forall pm x y . a' pm x y == a pm x (g y)) /\ (forall y . f' y == f (g y))))
: split_t a' r f'
= (pm: perm) (x: t) (y: u')
{
  rewrite (a' pm x y) as (a pm x (g y));
  c pm x (g y);
  rewrite (a (pm /. 2.0R) x (g y)) as (a' (pm /. 2.0R) x y);
  rewrite (r (pm /. 2.0R) x (f (g y))) as (r (pm /. 2.0R) x (f' y))
}

ghost
fn absorb_map (#t #u #u': Type0) (a: prel t u) (r: bprel t) (c: absorb_t a r)
  (a': prel t u') (g: u' -> GTot u)
  (sq: squash (forall pm x y . a' pm x y == a pm x (g y)))
: absorb_t a' r
= (p1: perm) (p2: perm) (x: t) (y: u') (w: SB.bytes)
{
  rewrite (a' p1 x y) as (a p1 x (g y));
  c p1 p2 x (g y) w;
  rewrite (a (p1 +. p2) x (g y)) as (a' (p1 +. p2) x y)
}

let br_map (#t #u #u': Type0) (#a: prel t u) (#r: bprel t) (#f: u -> GTot SB.bytes) (c: br_t a r f)
  (a': prel t u') (f': u' -> GTot SB.bytes) (g: u' -> GTot u)
  (sq: squash ((forall pm x y . a' pm x y == a pm x (g y)) /\ (forall y . f' y == f (g y))))
: br_t a' r f'
= { sp = split_map a r f c.sp a' f' g sq; ab = absorb_map a r c.ab a' g () }

(* Dependent choices: the raw value selects the alternative *)

ghost
fn split_false (#t #u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (a pm x y == pure False))
: split_t a r f
= (pm: perm) (x: t) (y: u)
{
  eq pm x y;
  rewrite (a pm x y) as (pure False);
  unreachable ()
}

ghost
fn absorb_false (#t #u: Type0) (a: prel t u) (r: bprel t)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (a pm x y == pure False))
: absorb_t a r
= (p1: perm) (p2: perm) (x: t) (y: u) (w: SB.bytes)
{
  eq p1 x y;
  rewrite (a p1 x y) as (pure False);
  unreachable ()
}

let br_false (#t #u: Type0) (a: prel t u) (r: bprel t) (f: u -> GTot SB.bytes)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (a pm x y == pure False))
: br_t a r f
= { sp = split_false a r f eq; ab = absorb_false a r eq }

ghost
fn split_cond (#t #u #v: Type0) (ah: prel t u) (r: bprel t) (fh: u -> GTot SB.bytes) (c: split_t ah r fh)
  (a: prel t v) (f: v -> GTot SB.bytes) (p: v -> GTot bool) (hv: (y: v) -> squash (p y == true) -> GTot u)
  (eq: (pm: perm) -> (x: t) -> (y: v) -> Lemma (a pm x y == (if p y then ah pm x (hv y ()) else pure False)))
  (eqf: (y: v) -> Lemma (requires (p y == true)) (ensures (f y == fh (hv y ()))))
: split_t a r f
= (pm: perm) (x: t) (y: v)
{
  eq pm x y;
  let b : bool = p y;
  if b {
    eq (pm /. 2.0R) x y;
    eqf y;
    rewrite (a pm x y) as (ah pm x (hv y ()));
    c pm x (hv y ());
    rewrite (ah (pm /. 2.0R) x (hv y ())) as (a (pm /. 2.0R) x y);
    rewrite (r (pm /. 2.0R) x (fh (hv y ()))) as (r (pm /. 2.0R) x (f y))
  } else {
    rewrite (a pm x y) as (pure False);
    unreachable ()
  }
}

ghost
fn absorb_cond (#t #u #v: Type0) (ah: prel t u) (r: bprel t) (c: absorb_t ah r)
  (a: prel t v) (p: v -> GTot bool) (hv: (y: v) -> squash (p y == true) -> GTot u)
  (eq: (pm: perm) -> (x: t) -> (y: v) -> Lemma (a pm x y == (if p y then ah pm x (hv y ()) else pure False)))
: absorb_t a r
= (p1: perm) (p2: perm) (x: t) (y: v) (w: SB.bytes)
{
  eq p1 x y;
  let b : bool = p y;
  if b {
    eq (p1 +. p2) x y;
    rewrite (a p1 x y) as (ah p1 x (hv y ()));
    c p1 p2 x (hv y ()) w;
    rewrite (ah (p1 +. p2) x (hv y ())) as (a (p1 +. p2) x y)
  } else {
    rewrite (a p1 x y) as (pure False);
    unreachable ()
  }
}

let br_cond (#t #u #v: Type0) (#ah: prel t u) (#r: bprel t) (#fh: u -> GTot SB.bytes) (c: br_t ah r fh)
  (a: prel t v) (f: v -> GTot SB.bytes) (p: v -> GTot bool) (hv: (y: v) -> squash (p y == true) -> GTot u)
  (eq: (pm: perm) -> (x: t) -> (y: v) -> Lemma (a pm x y == (if p y then ah pm x (hv y ()) else pure False)))
  (eqf: (y: v) -> Lemma (requires (p y == true)) (ensures (f y == fh (hv y ()))))
: br_t a r f
= { sp = split_cond ah r fh c.sp a f p hv eq eqf; ab = absorb_cond ah r c.ab a p hv eq }

ghost
fn split_either (#th #tt #uh #ut #v: Type0)
  (ah: prel th uh) (rh: bprel th) (fh: uh -> GTot SB.bytes) (ch: split_t ah rh fh)
  (atl: prel tt ut) (rt: bprel tt) (ft: ut -> GTot SB.bytes) (ct: split_t atl rt ft)
  (a: prel (either th tt) v) (f: v -> GTot SB.bytes) (p: v -> GTot bool)
  (hv: (y: v) -> squash (p y == true) -> GTot uh) (tv: (y: v) -> squash (p y == false) -> GTot ut)
  (eql: (pm: perm) -> (x: th) -> (y: v) -> Lemma (a pm (Inl x) y == (if p y then ah pm x (hv y ()) else pure False)))
  (eqr: (pm: perm) -> (x: tt) -> (y: v) -> Lemma (a pm (Inr x) y == (if p y then pure False else atl pm x (tv y ()))))
  (eqf: (y: v) -> Lemma (f y == (if p y then fh (hv y ()) else ft (tv y ()))))
: split_t a (raw_either rh rt) f
= (pm: perm) (x: either th tt) (y: v)
{
  eqf y;
  match x {
    Inl xh -> {
      eql pm xh y;
      eql (pm /. 2.0R) xh y;
      let b : bool = p y;
  if b {
        rewrite (a pm x y) as (ah pm xh (hv y ()));
        ch pm xh (hv y ());
        rewrite (ah (pm /. 2.0R) xh (hv y ())) as (a (pm /. 2.0R) x y);
        rewrite (rh (pm /. 2.0R) xh (fh (hv y ()))) as (raw_either rh rt (pm /. 2.0R) x (f y))
      } else {
        rewrite (a pm x y) as (pure False);
        unreachable ()
      }
    }
    Inr xt -> {
      eqr pm xt y;
      eqr (pm /. 2.0R) xt y;
      let b : bool = p y;
  if b {
        rewrite (a pm x y) as (pure False);
        unreachable ()
      } else {
        rewrite (a pm x y) as (atl pm xt (tv y ()));
        ct pm xt (tv y ());
        rewrite (atl (pm /. 2.0R) xt (tv y ())) as (a (pm /. 2.0R) x y);
        rewrite (rt (pm /. 2.0R) xt (ft (tv y ()))) as (raw_either rh rt (pm /. 2.0R) x (f y))
      }
    }
  }
}

ghost
fn absorb_either (#th #tt #uh #ut #v: Type0)
  (ah: prel th uh) (rh: bprel th) (ch: absorb_t ah rh)
  (atl: prel tt ut) (rt: bprel tt) (ct: absorb_t atl rt)
  (a: prel (either th tt) v) (p: v -> GTot bool)
  (hv: (y: v) -> squash (p y == true) -> GTot uh) (tv: (y: v) -> squash (p y == false) -> GTot ut)
  (eql: (pm: perm) -> (x: th) -> (y: v) -> Lemma (a pm (Inl x) y == (if p y then ah pm x (hv y ()) else pure False)))
  (eqr: (pm: perm) -> (x: tt) -> (y: v) -> Lemma (a pm (Inr x) y == (if p y then pure False else atl pm x (tv y ()))))
: absorb_t a (raw_either rh rt)
= (p1: perm) (p2: perm) (x: either th tt) (y: v) (w: SB.bytes)
{
  match x {
    Inl xh -> {
      eql p1 xh y;
      eql (p1 +. p2) xh y;
      let b : bool = p y;
  if b {
        rewrite (a p1 x y) as (ah p1 xh (hv y ()));
        rewrite (raw_either rh rt p2 x w) as (rh p2 xh w);
        ch p1 p2 xh (hv y ()) w;
        rewrite (ah (p1 +. p2) xh (hv y ())) as (a (p1 +. p2) x y)
      } else {
        rewrite (a p1 x y) as (pure False);
        unreachable ()
      }
    }
    Inr xt -> {
      eqr p1 xt y;
      eqr (p1 +. p2) xt y;
      let b : bool = p y;
  if b {
        rewrite (a p1 x y) as (pure False);
        unreachable ()
      } else {
        rewrite (a p1 x y) as (atl p1 xt (tv y ()));
        rewrite (raw_either rh rt p2 x w) as (rt p2 xt w);
        ct p1 p2 xt (tv y ()) w;
        rewrite (atl (p1 +. p2) xt (tv y ())) as (a (p1 +. p2) x y)
      }
    }
  }
}

let br_either (#th #tt #uh #ut #v: Type0)
  (#ah: prel th uh) (#rh: bprel th) (#fh: uh -> GTot SB.bytes) (ch: br_t ah rh fh)
  (#atl: prel tt ut) (#rt: bprel tt) (#ft: ut -> GTot SB.bytes) (ct: br_t atl rt ft)
  (a: prel (either th tt) v) (f: v -> GTot SB.bytes) (p: v -> GTot bool)
  (hv: (y: v) -> squash (p y == true) -> GTot uh) (tv: (y: v) -> squash (p y == false) -> GTot ut)
  (eql: (pm: perm) -> (x: th) -> (y: v) -> Lemma (a pm (Inl x) y == (if p y then ah pm x (hv y ()) else pure False)))
  (eqr: (pm: perm) -> (x: tt) -> (y: v) -> Lemma (a pm (Inr x) y == (if p y then pure False else atl pm x (tv y ()))))
  (eqf: (y: v) -> Lemma (f y == (if p y then fh (hv y ()) else ft (tv y ()))))
: br_t a (raw_either rh rt) f
= { sp = split_either ah rh fh ch.sp atl rt ft ct.sp a f p hv tv eql eqr eqf;
    ab = absorb_either ah rh ch.ab atl rt ct.ab a p hv tv eql eqr }

(* SEQUENCE OF / SET OF *)

ghost
fn het_split (#s: _) (k: asn1_k s) (c: split_t (asn1_raw_rel k) (raw_rel k) (rb k))
: Het.split_t #(asn1_impl_t k) #(asn1_raw_t k) #SB.bytes (asn1_raw_rel k) (raw_rel k) (rb_r k)
= (x: asn1_impl_t k) (pm0: perm) (y1: asn1_raw_t k) (y2: SB.bytes { rb_r k y1 y2 })
{
  c pm0 x y1;
  rewrite (raw_rel k (pm0 /. 2.0R) x (rb k y1)) as (raw_rel k (pm0 /. 2.0R) x y2)
}

ghost
fn het_absorb (#s: _) (k: asn1_k s) (c: absorb_t (asn1_raw_rel k) (raw_rel k))
: Het.absorb_t #(asn1_impl_t k) #(asn1_raw_t k) #SB.bytes (asn1_raw_rel k) (raw_rel k)
= (x: asn1_impl_t k) (pm1: perm) (pm2: perm) (y1: asn1_raw_t k) (y2: SB.bytes)
{
  c pm1 pm2 x y1 y2
}

let ml_rel (#s: _) (k: asn1_k s) : prel (ml (asn1_impl_t k)) (list (asn1_raw_t k)) =
  It.mixed_list_match (asn1_raw_rel k) ml_ops #asn1_strong_parser_kind (parse_raw k)

let f_ml (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) : GTot SB.bytes = W.enc_list id_enc (rb_list k l)

let f_ml_sorted (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) : GTot SB.bytes = SI.sort_list SI.lt_lex id_enc (rb_list k l)

ghost
fn split_ml_gen (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (c: split_t (asn1_raw_rel k) (raw_rel k) (rb k))
  (pm: perm) (x: ml (asn1_impl_t k)) (y: list (asn1_raw_t k))
requires ml_rel k pm x y
ensures ml_rel k (pm /. 2.0R) x y ** It.mixed_list_match (raw_rel k) ml_ops #asn1_strong_parser_kind p_raw (pm /. 2.0R) x (rb_list k y)
{
  half_perm_pos pm;
  rb_parsers_fwd k u;
  rb_r_functional k;
  rb_list_rel k y;
  unfold (ml_rel k pm x y);
  Het.mixed_list_match_split (asn1_raw_rel k) (raw_rel k) ml_ops (parse_raw k) p_raw (rb_r k) () pm x y (rb_list k y) (het_split k c);
  fold (ml_rel k (pm /. 2.0R) x y)
}

ghost
fn split_ml (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (c: split_t (asn1_raw_rel k) (raw_rel k) (rb k))
: split_t (ml_rel k) (raw_ml (raw_rel k)) (f_ml k)
= (pm: perm) (x: ml (asn1_impl_t k)) (y: list (asn1_raw_t k))
{
  split_ml_gen k u c pm x y;
  fold (raw_ml (raw_rel k) (pm /. 2.0R) x (f_ml k y))
}

ghost
fn split_ml_sorted (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (c: split_t (asn1_raw_rel k) (raw_rel k) (rb k))
: split_t (ml_rel k) (raw_ml_sorted (raw_rel k)) (f_ml_sorted k)
= (pm: perm) (x: ml (asn1_impl_t k)) (y: list (asn1_raw_t k))
{
  split_ml_gen k u c pm x y;
  fold (raw_ml_sorted (raw_rel k) (pm /. 2.0R) x (f_ml_sorted k y))
}

ghost
fn absorb_ml (#s: _) (k: asn1_k s) (c: absorb_t (asn1_raw_rel k) (raw_rel k))
: absorb_t (ml_rel k) (raw_ml (raw_rel k))
= (p1: perm) (p2: perm) (x: ml (asn1_impl_t k)) (y: list (asn1_raw_t k)) (w: SB.bytes)
{
  unfold (ml_rel k p1 x y);
  unfold (raw_ml (raw_rel k) p2 x w);
  with l . assert (It.mixed_list_match (raw_rel k) ml_ops #asn1_strong_parser_kind p_raw p2 x l);
  Het.mixed_list_match_absorb (asn1_raw_rel k) (raw_rel k) ml_ops (parse_raw k) p_raw p1 p2 x y l (het_absorb k c);
  fold (ml_rel k (p1 +. p2) x y)
}

ghost
fn absorb_ml_sorted (#s: _) (k: asn1_k s) (c: absorb_t (asn1_raw_rel k) (raw_rel k))
: absorb_t (ml_rel k) (raw_ml_sorted (raw_rel k))
= (p1: perm) (p2: perm) (x: ml (asn1_impl_t k)) (y: list (asn1_raw_t k)) (w: SB.bytes)
{
  unfold (ml_rel k p1 x y);
  unfold (raw_ml_sorted (raw_rel k) p2 x w);
  with l . assert (It.mixed_list_match (raw_rel k) ml_ops #asn1_strong_parser_kind p_raw p2 x l);
  Het.mixed_list_match_absorb (asn1_raw_rel k) (raw_rel k) ml_ops (parse_raw k) p_raw p1 p2 x y l (het_absorb k c);
  fold (ml_rel k (p1 +. p2) x y)
}

let br_ml (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (c: br_t (asn1_raw_rel k) (raw_rel k) (rb k))
: br_t (ml_rel k) (raw_ml (raw_rel k)) (f_ml k)
= { sp = split_ml k u c.sp; ab = absorb_ml k c.ab }

let br_ml_sorted (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (c: br_t (asn1_raw_rel k) (raw_rel k) (rb k))
: br_t (ml_rel k) (raw_ml_sorted (raw_rel k)) (f_ml_sorted k)
= { sp = split_ml_sorted k u c.sp; ab = absorb_ml_sorted k c.ab }

(* Empty items *)

let emp_enc (_: unit) : GTot SB.bytes = Seq.empty

ghost
fn dup_emp (pm pm': perm) (x: unit) (y: unit)
requires prel_emp unit unit pm x y
ensures prel_emp unit unit pm' x y ** pure (null_enc x == emp_enc y)
{
  unfold (prel_emp unit unit pm x y);
  fold (prel_emp unit unit pm' x y)
}

let br_emp : br_t (prel_emp unit unit) (raw_pure null_enc) emp_enc =
  br_pure (prel_emp unit unit) null_enc emp_enc dup_emp

(* CHOICE alternatives *)

let f_lc (lc: list (asn1_id_t & asn1_content_k)) (y: make_gen_choice_type (raw_lc_t lc)) : GTot SB.bytes =
  let (| id, z |) = y in
  rb_choice lc id z

let content_br_t (id: asn1_id_t) (c: asn1_content_k) : Type =
  br_t (asn1_raw_content_rel c) (raw_content_rel id c) (rb_content id c)

let lc_br_t (lc: list (asn1_id_t & asn1_content_k)) : Type =
  br_t (asn1_raw_lc_rel lc) (raw_lc_rel lc) (f_lc lc)

let lc_nil_eq (pm: perm) (x: asn1_lc_impl_t []) (y: make_gen_choice_type (raw_lc_t []))
: Lemma (asn1_raw_lc_rel [] pm x y == pure False)
= assert_norm (asn1_raw_lc_rel [] pm x y == pure False)

let br_lc_nil : lc_br_t [] =
  br_false (asn1_raw_lc_rel []) (raw_lc_rel []) (f_lc []) lc_nil_eq

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let lc_single_f (id': asn1_id_t) (c: asn1_content_k) (y: make_gen_choice_type (raw_lc_t [(id', c)]))
: Lemma (requires ((dfst y = id') == true)) (ensures (f_lc [(id', c)] y == rb_content id' c (raw_lc_head_val id' c [] y ())))
= ()

let lc_cons_f (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (y: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (f_lc ((id', c) :: hd2 :: tl2) y == (if dfst y = id' then rb_content id' c (raw_lc_head_val id' c (hd2 :: tl2) y ()) else f_lc (hd2 :: tl2) (raw_lc_tail_val (id', c) (hd2 :: tl2) y ())))
= ()
#pop-options

let br_lc_single (id': asn1_id_t) (c: asn1_content_k) (cc: content_br_t id' c) : lc_br_t [(id', c)] =
  lc_single_equiv id' (legacy_cdesc c);
  br_ext (asn1_raw_lc_rel [(id', c)]) (asn1_raw_lc_rel [(id', c)]) (raw_content_rel id' c) (raw_lc_rel [(id', c)]) (f_lc [(id', c)]) (f_lc [(id', c)]) ()
    (br_cond cc (asn1_raw_lc_rel [(id', c)]) (f_lc [(id', c)]) (fun y -> dfst y = id') (fun y _ -> raw_lc_head_val id' c [] y ())
      (raw_lc_single_eq id' c) (lc_single_f id' c))

let lc_cons_inl (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (a: asn1_content_impl_t c) (v: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm (Inl #(asn1_content_impl_t c) #(asn1_lc_impl_t (hd2 :: tl2)) a) v ==
    (if dfst v = id' then asn1_raw_content_rel c pm a (raw_lc_head_val id' c (hd2 :: tl2) v ()) else pure False))
= raw_lc_cons_inl_eq id' c hd2 tl2 pm a v

let lc_cons_inr (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (b: asn1_lc_impl_t (hd2 :: tl2)) (v: make_gen_choice_type (raw_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2) pm (Inr #(asn1_content_impl_t c) #(asn1_lc_impl_t (hd2 :: tl2)) b) v ==
    (if dfst v = id' then pure False else asn1_raw_lc_rel (hd2 :: tl2) pm b (raw_lc_tail_val (id', c) (hd2 :: tl2) v ())))
= raw_lc_cons_inr_eq id' c hd2 tl2 pm b v

let br_lc_cons (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (cc: content_br_t id' c) (ct: lc_br_t (hd2 :: tl2))
: lc_br_t ((id', c) :: hd2 :: tl2)
= lc_cons_equiv id' (legacy_cdesc c) (legacy_lcdesc (hd2 :: tl2));
  br_ext (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2)) (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2))
    (raw_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2))) (raw_lc_rel ((id', c) :: hd2 :: tl2))
    (f_lc ((id', c) :: hd2 :: tl2)) (f_lc ((id', c) :: hd2 :: tl2)) ()
    (br_either #(asn1_content_impl_t c) #(asn1_lc_impl_t (hd2 :: tl2)) cc ct
      (asn1_raw_lc_rel ((id', c) :: hd2 :: tl2)) (f_lc ((id', c) :: hd2 :: tl2)) (fun y -> dfst y = id')
      (fun y _ -> raw_lc_head_val id' c (hd2 :: tl2) y ()) (fun y _ -> raw_lc_tail_val (id', c) (hd2 :: tl2) y ())
      (lc_cons_inl id' c hd2 tl2) (lc_cons_inr id' c hd2 tl2) (lc_cons_f id' c hd2 tl2))

(* ANY DEFINED BY, without a fallback *)

let items_br_t (srt: bool) (#ids: _) (items: asn1_gen_items_l ids) : Type =
  br_t (asn1_raw_items_rel items) (raw_items_rel srt items) (rb_items srt items)

let f_adb (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (s: rady key_k ls) : GTot SB.bytes =
  let (| key, y |) = s in
  rb_ls kid key_k ls key y

let adb_br_t (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Type =
  br_t (asn1_raw_adb_rel key_k ls) (raw_adb_rel kid key_k ls) (f_adb kid key_k ls)

let br_lit (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (ci: items_br_t false (dsnd y))
: br_t (asn1_raw_items_rel (dsnd y)) (raw_lit kid kx y) (f_pre (WA.raw_key_enc kid key_k kx) (rb_items false (dsnd y)))
= br_pre (WA.raw_key_enc kid key_k kx) ci

let adb_nil_eq (key_k: asn1_terminal_k) (pm: perm) (x: asn1_adb_suffix_impl_t key_k [] None) (y: rady key_k [])
: Lemma (asn1_raw_adb_rel key_k [] pm x y == pure False)
= assert_norm (asn1_raw_adb_rel key_k [] pm x y == pure False)

let br_adb_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) : adb_br_t kid key_k [] =
  br_false (asn1_raw_adb_rel key_k []) (raw_adb_rel kid key_k []) (f_adb kid key_k []) (adb_nil_eq key_k)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let adb_single_f (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (v: rady key_k [(kx, y)])
: Lemma (requires ((dfst v = raw_key_of_lit key_k kx) == true))
  (ensures (f_adb kid key_k [(kx, y)] v == f_pre (WA.raw_key_enc kid key_k kx) (rb_items false (dsnd y)) (rady_head_val kx y [] v ())))
= ()

let adb_cons_f (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (v: rady key_k ((kx, y) :: hd2 :: tl2))
: Lemma (f_adb kid key_k ((kx, y) :: hd2 :: tl2) v == (if dfst v = raw_key_of_lit key_k kx
    then f_pre (WA.raw_key_enc kid key_k kx) (rb_items false (dsnd y)) (rady_head_val kx y (hd2 :: tl2) v ())
    else f_adb kid key_k (hd2 :: tl2) (rady_tail_val kx y (hd2 :: tl2) v ())))
= ()
#pop-options

let br_adb_single (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (ci: items_br_t false (dsnd y))
: adb_br_t kid key_k [(kx, y)]
= adb_single_equiv kid kx y (legacy_idesc (dsnd y));
  br_ext (asn1_raw_adb_rel key_k [(kx, y)]) (asn1_raw_adb_rel key_k [(kx, y)]) (raw_lit kid kx y) (raw_adb_rel kid key_k [(kx, y)])
    (f_adb kid key_k [(kx, y)]) (f_adb kid key_k [(kx, y)]) ()
    (br_cond (br_lit kid kx y ci) (asn1_raw_adb_rel key_k [(kx, y)]) (f_adb kid key_k [(kx, y)])
      (fun v -> dfst v = raw_key_of_lit key_k kx) (fun v _ -> rady_head_val kx y [] v ())
      (raw_adb_single_eq kx y) (adb_single_f kid kx y))

let br_adb_cons (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (ci: items_br_t false (dsnd y)) (ct: adb_br_t kid key_k (hd2 :: tl2))
: adb_br_t kid key_k ((kx, y) :: hd2 :: tl2)
= adb_cons_equiv kid kx y (legacy_idesc (dsnd y)) (legacy_sxdesc key_k (hd2 :: tl2));
  br_ext (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2)) (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2))
    (raw_either (raw_lit kid kx y) (raw_adb_rel kid key_k (hd2 :: tl2))) (raw_adb_rel kid key_k ((kx, y) :: hd2 :: tl2))
    (f_adb kid key_k ((kx, y) :: hd2 :: tl2)) (f_adb kid key_k ((kx, y) :: hd2 :: tl2)) ()
    (br_either #(asn1_items_impl_t (dsnd y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) None) (br_lit kid kx y ci) ct
      (asn1_raw_adb_rel key_k ((kx, y) :: hd2 :: tl2)) (f_adb kid key_k ((kx, y) :: hd2 :: tl2))
      (fun v -> dfst v = raw_key_of_lit key_k kx)
      (fun v _ -> rady_head_val kx y (hd2 :: tl2) v ()) (fun v _ -> rady_tail_val kx y (hd2 :: tl2) v ())
      (raw_adb_cons_inl_eq kx y hd2 tl2) (raw_adb_cons_inr_eq kx y hd2 tl2) (adb_cons_f kid kx y hd2 tl2))

(* ANY DEFINED BY, with a fallback *)

let f_afb (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (s: rady_fb key_k ls fb) : GTot SB.bytes =
  let (| key, y |) = s in
  rb_ls_fb kid key_k ls (raw_items_t (dsnd fb)) (fun (z: raw_items_t (dsnd fb)) -> rb_items false (dsnd fb) z) key y

let afb_br_t (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) : Type =
  br_t (RVR.raw_afb_rel key_k ls fb) (RR.raw_afb_rel kid key_k ls fb) (f_afb kid key_k ls fb)

let afb_nil_g (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (v: rady_fb key_k [] fb) : GTot (asn1_raw_terminal_t key_k & raw_items_t (dsnd fb)) =
  (dfst v, rady_fb_nil_val fb v)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let afb_nil_sq (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk)
: Lemma ((forall pm x y . RVR.raw_afb_rel key_k [] fb pm x y == prel_pair (asn1_raw_terminal_rel key_k) (asn1_raw_items_rel (dsnd fb)) pm x (afb_nil_g fb y)) /\
    (forall y . f_afb kid key_k [] fb y == f_cat (rb_term kid key_k) (rb_items false (dsnd fb)) (afb_nil_g fb y)))
= Classical.forall_intro_3 (raw_afb_nil_eq #key_k fb)

let afb_single_f (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk) (v: rady_fb key_k [(kx, y)] fb)
: Lemma (f_afb kid key_k [(kx, y)] fb v == (if dfst v = raw_key_of_lit key_k kx
    then f_pre (WA.raw_key_enc kid key_k kx) (rb_items false (dsnd y)) (rady_fb_head_val kx y [] fb v ())
    else f_afb kid key_k [] fb (rady_fb_tail_val kx y [] fb v ())))
= ()

let afb_cons_f (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: rady_fb key_k ((kx, y) :: hd2 :: tl2) fb)
: Lemma (f_afb kid key_k ((kx, y) :: hd2 :: tl2) fb v == (if dfst v = raw_key_of_lit key_k kx
    then f_pre (WA.raw_key_enc kid key_k kx) (rb_items false (dsnd y)) (rady_fb_head_val kx y (hd2 :: tl2) fb v ())
    else f_afb kid key_k (hd2 :: tl2) fb (rady_fb_tail_val kx y (hd2 :: tl2) fb v ())))
= ()
#pop-options

let br_fbr (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (ci: items_br_t false (dsnd fb))
: br_t (RVR.raw_afb_rel key_k [] fb) (RR.raw_fbr kid key_k fb) (f_afb kid key_k [] fb)
= afb_nil_sq kid key_k fb;
  br_map (br_cat (br_term kid key_k) ci) (RVR.raw_afb_rel key_k [] fb) (f_afb kid key_k [] fb) (afb_nil_g fb) ()

let br_afb_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (ci: items_br_t false (dsnd fb))
: afb_br_t kid key_k [] fb
= afb_nil_equiv kid key_k (RR.raw_fbr kid key_k fb);
  br_ext _ _ _ _ _ _ () (br_fbr kid key_k fb ci)

let br_afb_single (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (fb: asn1_gen_items_lk)
  (ci: items_br_t false (dsnd y)) (cf: items_br_t false (dsnd fb))
: afb_br_t kid key_k [(kx, y)] fb
= afb_single_equiv kid kx y (legacy_idesc (dsnd y)) (RR.raw_fbr kid key_k fb);
  br_ext (RVR.raw_afb_rel key_k [(kx, y)] fb) (RVR.raw_afb_rel key_k [(kx, y)] fb)
    (raw_either (raw_lit kid kx y) (RR.raw_fbr kid key_k fb)) (RR.raw_afb_rel kid key_k [(kx, y)] fb)
    (f_afb kid key_k [(kx, y)] fb) (f_afb kid key_k [(kx, y)] fb) ()
    (br_either #(asn1_items_impl_t (dsnd y)) #(PA.fbt key_k fb) (br_lit kid kx y ci) (br_fbr kid key_k fb cf)
      (RVR.raw_afb_rel key_k [(kx, y)] fb) (f_afb kid key_k [(kx, y)] fb)
      (fun v -> dfst v = raw_key_of_lit key_k kx)
      (fun v _ -> rady_fb_head_val kx y [] fb v ()) (fun v _ -> rady_fb_tail_val kx y [] fb v ())
      (raw_afb_single_inl_eq kx y fb) (raw_afb_single_inr_eq kx y fb) (afb_single_f kid kx y fb))

let br_afb_cons (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (hd2: asn1_key_lit key_k & asn1_gen_items_lk) (tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (ci: items_br_t false (dsnd y)) (ct: afb_br_t kid key_k (hd2 :: tl2) fb)
: afb_br_t kid key_k ((kx, y) :: hd2 :: tl2) fb
= afb_cons_equiv kid kx y (legacy_idesc (dsnd y)) (legacy_fxdesc key_k (hd2 :: tl2) (PA.fbt key_k fb)) (RR.raw_fbr kid key_k fb);
  br_ext (RVR.raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb) (RVR.raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb)
    (raw_either (raw_lit kid kx y) (RR.raw_afb_rel kid key_k (hd2 :: tl2) fb)) (RR.raw_afb_rel kid key_k ((kx, y) :: hd2 :: tl2) fb)
    (f_afb kid key_k ((kx, y) :: hd2 :: tl2) fb) (f_afb kid key_k ((kx, y) :: hd2 :: tl2) fb) ()
    (br_either #(asn1_items_impl_t (dsnd y)) #(asn1_adb_suffix_impl_t key_k (hd2 :: tl2) (Some (PA.fbt key_k fb))) (br_lit kid kx y ci) ct
      (RVR.raw_afb_rel key_k ((kx, y) :: hd2 :: tl2) fb) (f_afb kid key_k ((kx, y) :: hd2 :: tl2) fb)
      (fun v -> dfst v = raw_key_of_lit key_k kx)
      (fun v _ -> rady_fb_head_val kx y (hd2 :: tl2) fb v ()) (fun v _ -> rady_fb_tail_val kx y (hd2 :: tl2) fb v ())
      (raw_afb_cons_inl_eq kx y hd2 tl2 fb) (raw_afb_cons_inr_eq kx y hd2 tl2 fb) (afb_cons_f kid kx y hd2 tl2 fb))

(* The byte function of a suffix of items is extensional *)

let rec rb_items_any_ext (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (f1 f2: sfx_t -> GTot SB.bytes) (y: raw_items_any_t items sfx_t)
: Lemma (requires (forall s . f1 s == f2 s)) (ensures (rb_items_any items f1 y == rb_items_any items f2 y)) (decreases items)
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let y' : raw_dec_t dk & raw_items_any_t tl sfx_t = y in
    let (a, c) = y' in
    rb_items_any_ext tl f1 f2 c

let rb_content_adb_none (id: asn1_id_t) (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pf: _) (pf': _)
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf'))
: Lemma (rb_content id (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf') y == f_tlv id (rb_items_any prefix (f_adb kid key_k ls)) y)
= assert (rb_content id (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf') y == enc_tlv id true (rb_items_any prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, y |) = s in rb_ls kid key_k ls key y) <: GTot SB.bytes) y))
    by (FStar.Tactics.norm [delta_only [`%rb_content]; zeta; iota]; FStar.Tactics.trefl ());
  rb_items_any_ext prefix (fun (s: make_gen_choice_type (raw_any_t_core key_k ls)) -> (let (| key, y |) = s in rb_ls kid key_k ls key y) <: GTot SB.bytes) (f_adb kid key_k ls) y

let rb_content_adb_some (id: asn1_id_t) (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fbids: id_decs { asn1_sequence_k_wf fbids }) (fbitems: asn1_gen_items_l fbids) (pf: _) (pf': _)
  (y: asn1_raw_content_t (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf'))
: Lemma (rb_content id (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == f_tlv id (rb_items_any prefix (f_afb kid key_k ls (| fbids, fbitems |))) y)
= assert (rb_content id (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some (| fbids, fbitems |)) pf pf') y == enc_tlv id true (rb_items_any prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, y |) = s in rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y) <: GTot SB.bytes) y))
    by (FStar.Tactics.norm [delta_only [`%rb_content]; zeta; iota]; FStar.Tactics.trefl ());
  let prf (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems))
  : Lemma (((let (| key, y |) = s in rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y) <: GTot SB.bytes) == f_afb kid key_k ls (| fbids, fbitems |) s)
  = assert (((let (| key, y |) = s in rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y) <: GTot SB.bytes) == f_afb kid key_k ls (| fbids, fbitems |) s)
      by (FStar.Tactics.norm [delta_only [`%f_afb; `%dsnd; `%Mkdtuple2?._2]; zeta; iota]; FStar.Tactics.trefl ())
  in
  Classical.forall_intro prf;
  rb_items_any_ext prefix (fun (s: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) -> (let (| key, y |) = s in rb_ls_fb kid key_k ls (raw_items_t fbitems) (fun (z: raw_items_t fbitems) -> rb_items false fbitems z) key y) <: GTot SB.bytes) (f_afb kid key_k ls (| fbids, fbitems |)) y

(* The whole bridge, by mutual recursion on the schema *)

let ok_content (id: asn1_id_t) (k: asn1_content_k) : prop = Conf.wf_content id k /\ In.supported_content k
let ok_lc (lc: list (asn1_id_t & asn1_content_k)) : prop = Conf.wf_lc lc /\ In.supported_lc lc
let ok_ls (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : prop = Conf.wf_ls ls /\ In.supported_ls ls
let ok_items (#i: _) (ls: asn1_gen_items_l i) : prop = Conf.wf_items ls /\ In.supported_items ls
let ok_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : prop = Conf.wf_dec dk /\ In.supported_dec dk

let k_br_t (#s: _) (k: asn1_k s) : Type = br_t (asn1_raw_rel k) (raw_rel k) (rb k)
let dec_br_t (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Type = br_t (asn1_raw_decorated_rel dk) (raw_dec_rel dk) (rb_dec dk)
let items_any_br_t (#i: _) (ls: asn1_gen_items_l i) (#sfxi #sfxs: Type0) (sfxr: prel sfxi sfxs) (rsfx: bprel sfxi) (fs: sfxs -> GTot SB.bytes) : Type =
  br_t (asn1_raw_items_any_rel ls sfxr) (raw_items_any_rel ls rsfx) (rb_items_any ls fs)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec br_content (id: asn1_id_t) (k: asn1_content_k) (u: squash (ok_content id k))
: Tot (content_br_t id k) (decreases k)
= match k with
  | ASN1_TERMINAL k' ->
    content_terminal_equiv id k';
    raw_content_terminal_equiv k';
    br_ext _ _ _ _ _ _ () (br_term id k')
  | ASN1_RESTRICTED_TERMINAL k' r ->
    content_restricted_equiv id k' r;
    raw_content_restricted_equiv k' r;
    br_ext _ _ _ _ _ _ () (br_term id k')
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv id (legacy_adesc k');
    raw_content_prefixed_equiv k';
    br_ext _ _ _ _ _ _ () (br_tlv id (br_k k' ()))
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv id gitems (legacy_idesc (dsnd gitems));
    raw_content_sequence_equiv gitems;
    br_ext _ _ _ _ _ _ () (br_tlv id (br_items false (dsnd gitems) ()))
  | ASN1_SET ids items pf ->
    content_set_equiv id ids items pf (legacy_idesc items);
    raw_content_set_equiv ids items pf;
    br_ext _ _ _ _ _ _ () (br_tlv id (br_items true items ()))
  | ASN1_SEQUENCE_OF ne k' ->
    content_seq_of_equiv id ne (legacy_adesc k');
    Classical.forall_intro_3 (raw_seq_of_eq ne k');
    br_ext _ _ _ _ _ _ () (br_tlv id (br_ml k' () (br_k k' ())))
  | ASN1_SET_OF ne k' ->
    content_set_of_equiv id ne (legacy_adesc k');
    Classical.forall_intro_3 (raw_set_of_eq ne k');
    br_ext _ _ _ _ _ _ () (br_tlv id (br_ml_sorted k' () (br_k k' ())))
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match ofb with
    | None ->
      content_adb_none_equiv id ipd prefix kid key_k ls pf pf' (legacy_sxdesc key_k ls) (legacy_iadesc prefix (asn1_adb_suffix_impl_t key_k ls None));
      raw_adb_none_equiv ipd prefix kid key_k ls pf pf';
      Classical.forall_intro (rb_content_adb_none id ipd prefix kid key_k ls pf pf');
      br_ext _ _ _ _ _ _ ()
        (br_tlv id (br_items_any prefix () (asn1_raw_adb_rel key_k ls) (raw_adb_rel kid key_k ls) (f_adb kid key_k ls) (br_adb kid key_k ls ())))
    | Some (| fbids, fbitems |) ->
      fb_precedes k;
      content_adb_some_equiv id ipd prefix kid key_k ls (| fbids, fbitems |) pf pf' (legacy_idesc fbitems) (legacy_fxdesc key_k ls (asn1_terminal_impl_t key_k & asn1_items_impl_t fbitems)) (legacy_iadesc prefix (asn1_adb_suffix_impl_t key_k ls (Some (asn1_terminal_impl_t key_k & asn1_items_impl_t fbitems))));
      raw_adb_some_equiv ipd prefix kid key_k ls (| fbids, fbitems |) pf pf';
      Classical.forall_intro (rb_content_adb_some id ipd prefix kid key_k ls fbids fbitems pf pf');
      br_ext _ _ _ _ _ _ ()
        (br_tlv id (br_items_any prefix ()
          (RVR.raw_afb_rel key_k ls (| fbids, fbitems |)) (RR.raw_afb_rel kid key_k ls (| fbids, fbitems |)) (f_afb kid key_k ls (| fbids, fbitems |))
          (br_afb kid key_k ls (| fbids, fbitems |) () (br_items false fbitems ()))))
    end

and br_adb (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u: squash (ok_ls ls))
: Tot (adb_br_t kid key_k ls) (decreases ls)
= match ls with
  | [] -> br_adb_nil kid key_k
  | [(kx, y)] -> br_adb_single kid kx y (br_items false (dsnd y) ())
  | (kx, y) :: hd2 :: tl2 -> br_adb_cons kid kx y hd2 tl2 (br_items false (dsnd y) ()) (br_adb kid key_k (hd2 :: tl2) ())

and br_afb (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (u: squash (ok_ls ls))
  (cf: items_br_t false (dsnd fb))
: Tot (afb_br_t kid key_k ls fb) (decreases ls)
= match ls with
  | [] -> br_afb_nil kid key_k fb cf
  | [(kx, y)] -> br_afb_single kid kx y fb (br_items false (dsnd y) ()) cf
  | (kx, y) :: hd2 :: tl2 -> br_afb_cons kid kx y hd2 tl2 fb (br_items false (dsnd y) ()) (br_afb kid key_k (hd2 :: tl2) fb () cf)

and br_items_any (#i: _) (ls: asn1_gen_items_l i) (u: squash (ok_items ls)) (#sfxi #sfxs: Type0) (sfxr: prel sfxi sfxs) (rsfx: bprel sfxi) (fs: sfxs -> GTot SB.bytes)
  (cs: br_t sfxr rsfx fs)
: Tot (items_any_br_t ls sfxr rsfx fs) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_any_nil_equiv rsfx;
    raw_items_any_nil_equiv sfxr;
    br_ext _ _ _ _ _ _ () cs
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_any_single_equiv (legacy_ddesc dk) rsfx;
    raw_items_any_single_equiv dk sfxr;
    br_ext _ _ _ _ _ _ () (br_cat (br_dec dk ()) cs)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_any_cons_equiv (legacy_ddesc dk) (legacy_iadesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) sfxi) rsfx;
    raw_items_any_cons_equiv dk dk2 tl2 sfxr;
    br_ext _ _ _ _ _ _ () (br_cat (br_dec dk ()) (br_items_any (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () sfxr rsfx fs cs))

and br_lc (lc: list (asn1_id_t & asn1_content_k)) (u: squash (ok_lc lc))
: Tot (lc_br_t lc) (decreases lc)
= match lc with
  | [] -> br_lc_nil
  | [(id', c)] -> br_lc_single id' c (br_content id' c ())
  | (id', c) :: hd2 :: tl2 -> br_lc_cons id' c hd2 tl2 (br_content id' c ()) (br_lc (hd2 :: tl2) ())

and br_k (#s: _) (k: asn1_k s) (u: squash (raw_ok k))
: Tot (k_br_t k) (decreases k)
= match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id (legacy_cdesc k');
    raw_rel_ilc_equiv id k';
    br_ext _ _ _ _ _ _ () (br_content id k' ())
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf (legacy_lcdesc lc);
    raw_rel_choice_equiv lc pf;
    br_ext _ _ _ _ _ _ () (br_lc lc ())
  | ASN1_ANY_ILC ->
    rel_any_equiv ();
    raw_rel_any_equiv ();
    br_ext _ _ _ _ _ _ () (br_slice asn1_value_enc)

and br_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (ok_dec dk))
: Tot (dec_br_t dk) (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k ->
    dec_plain_equiv (legacy_adesc k);
    raw_dec_plain_equiv k;
    br_ext _ _ _ _ _ _ () (br_k k ())
  | ASN1_OPTION_ILC k ->
    dec_option_equiv (legacy_adesc k);
    raw_dec_option_equiv k;
    br_ext _ _ _ _ _ _ () (br_opt (br_k k ()))
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    dec_default_equiv id0 defv;
    raw_dec_default_equiv id0 defv;
    if In.adb_key_supported k
    then (default_nd_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt_nd (WA.raw_key_enc id0 k defv) (br_term id0 k)))
    else (default_opt_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt (br_term id0 k)))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    raw_dec_default_restricted_equiv id0 r defv;
    if In.adb_key_supported k
    then (default_nd_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt_nd (WA.raw_key_enc id0 k defv) (br_term id0 k)))
    else (default_opt_equiv id0 k defv; br_ext _ _ _ _ _ _ () (br_opt (br_term id0 k)))

and br_items (srt: bool) (#i: _) (ls: asn1_gen_items_l i) (u: squash (ok_items ls))
: Tot (items_br_t srt ls) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv srt;
    raw_items_nil_equiv ();
    br_ext _ _ _ _ _ _ () br_emp
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv srt (legacy_ddesc dk);
    raw_items_single_equiv dk;
    br_ext _ _ _ _ _ _ () (br_dec dk ())
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv srt (legacy_ddesc dk) (legacy_idesc (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2));
    raw_items_cons_equiv dk dk2 tl2;
    br_ext _ _ _ _ _ _ () (br_join srt (br_dec dk ()) (br_items srt (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ()))
#pop-options
