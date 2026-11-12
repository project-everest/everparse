module ASN1.Pulse.SortedInsert
#lang-pulse

(* On-the-fly insertion sort for right-to-left writers, in the style of the
   CDDL "table" map groups.

   An R2L writer produces the components of a SET (resp. the elements of a
   SET OF) one after the other, each to the left of the previous ones. Right
   after writing a new component `e` at `out[p2..p1)`, the region
   `out[p1..p0)` holds the components written so far, already sorted. We
   then scan that region frame by frame (a frame being an identifier, a
   length and that many bytes), skipping the frames that are smaller than
   `e`, and finally rotate `e` past them, in place.

   The insertion is total: if the region does not start with a well-formed
   frame (which can only happen with invalid raw input, e.g. a garbage ANY),
   the scan just stops there. Thus the writers need no new failure mode:
   the final validation of the whole output decides whether the input was
   valid. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open LowParse.PulseParse.Iterator.Type
open LowParse.PulseParse.Iterator.R2L
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module SU = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module SDER = LowParse.Spec.DER
module IdU = ASN1.Spec.IdentifierU32
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module SCmp = LowParse.Pulse.SizeComparison
module IO = LowParse.PulseParse.Iterator.IntOps
module LPS = LowParse.Pulse.Base
module SetOf = ASN1.Pulse.SetOf
module SetComp = ASN1.Pulse.SetComp
module Set = ASN1.Spec.Set
module VR = LowParse.PulseParse.VReader

(* Specification *)

(* The length of the frame at the beginning of `r`, or 0 if there is none *)
let frame_len (r: SB.bytes) : GTot nat =
  match SB.parse IdU.parse_asn1_identifier_U32 r with
  | None -> 0
  | Some (_, n1) ->
    match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice r n1 (Seq.length r)) with
    | None -> 0
    | Some (len, n2) ->
      if n1 + n2 + U32.v len <= Seq.length r then n1 + n2 + U32.v len else 0

let frame_len_le (r: SB.bytes) : Lemma (frame_len r <= Seq.length r) = ()

let lt_t = SB.bytes -> SB.bytes -> GTot bool

(* Insert `e` into `r`, after all the leading frames of `r` smaller than `e` *)
#push-options "--fuel 0 --ifuel 1"
let rec ins (lt: lt_t) (e r: SB.bytes) : GTot SB.bytes (decreases (Seq.length r)) =
  let n = frame_len r in
  if n = 0 then Seq.append e r
  else if lt (Seq.slice r 0 n) e then Seq.append (Seq.slice r 0 n) (ins lt e (Seq.slice r n (Seq.length r)))
  else Seq.append e r
#pop-options

#push-options "--fuel 2 --ifuel 1"

let ins_unfold (lt: lt_t) (e r: SB.bytes)
: Lemma (ins lt e r == (
    let n = frame_len r in
    if n = 0 then Seq.append e r
    else if lt (Seq.slice r 0 n) e then Seq.append (Seq.slice r 0 n) (ins lt e (Seq.slice r n (Seq.length r)))
    else Seq.append e r))
= assert_norm (ins lt e r == (
    let n = frame_len r in
    if n = 0 then Seq.append e r
    else if lt (Seq.slice r 0 n) e then Seq.append (Seq.slice r 0 n) (ins lt e (Seq.slice r n (Seq.length r)))
    else Seq.append e r))

let slice_split (v: SB.bytes) (a b c: nat)
: Lemma (requires a <= b /\ b <= c /\ c <= Seq.length v)
  (ensures Seq.slice v a c == Seq.append (Seq.slice v a b) (Seq.slice v b c))
= assert (Seq.equal (Seq.slice v a c) (Seq.append (Seq.slice v a b) (Seq.slice v b c)))

let ins_step (lt: lt_t) (e r: SB.bytes)
: Lemma (requires frame_len r > 0 /\ lt (Seq.slice r 0 (frame_len r)) e)
  (ensures ins lt e r == Seq.append (Seq.slice r 0 (frame_len r)) (ins lt e (Seq.slice r (frame_len r) (Seq.length r))))
= ins_unfold lt e r

let ins_nostep (lt: lt_t) (e r: SB.bytes)
: Lemma (requires frame_len r == 0 \/ (frame_len_le r; not (lt (Seq.slice r 0 (frame_len r)) e)))
  (ensures ins lt e r == Seq.append e r)
= ins_unfold lt e r

#push-options "--fuel 0 --ifuel 0 --using_facts_from '* -ASN1.Pulse.SortedInsert.frame_len'"

let rec ins_length (lt: lt_t) (e r: SB.bytes)
: Lemma (ensures Seq.length (ins lt e r) == Seq.length e + Seq.length r) (decreases (Seq.length r))
= frame_len_le r;
  let n = frame_len r in
  if n > 0 && lt (Seq.slice r 0 n) e then begin
    let r' = Seq.slice r n (Seq.length r) in
    ins_step lt e r;
    ins_length lt e r';
    Seq.lemma_len_append (Seq.slice r 0 n) (ins lt e r')
  end
  else begin
    ins_nostep lt e r;
    Seq.lemma_len_append e r
  end

#pop-options

(* Inserting the elements of a list one by one, first to last *)
let rec sort_acc (#u: Type) (lt: lt_t) (enc: u -> GTot SB.bytes) (acc: SB.bytes) (l: list u)
: GTot SB.bytes (decreases l)
= match l with
  | [] -> acc
  | a :: q -> sort_acc lt enc (ins lt (enc a) acc) q

let sort_list (#u: Type) (lt: lt_t) (enc: u -> GTot SB.bytes) (l: list u) : GTot SB.bytes =
  sort_acc lt enc Seq.empty l

let rec sort_acc_snoc (#u: Type) (lt: lt_t) (enc: u -> GTot SB.bytes) (acc: SB.bytes) (l: list u) (y: u)
: Lemma (ensures sort_acc lt enc acc (List.Tot.append l [y]) == ins lt (enc y) (sort_acc lt enc acc l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q -> sort_acc_snoc lt enc (ins lt (enc a) acc) q y

let rec sort_acc_length (#u: Type) (lt: lt_t) (enc: u -> GTot SB.bytes) (acc: SB.bytes) (l: list u)
: Lemma (ensures Seq.length (sort_acc lt enc acc l) == Seq.length acc + Seq.length (enc_list enc l)) (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    ins_length lt (enc a) acc;
    sort_acc_length lt enc (ins lt (enc a) acc) q;
    Seq.lemma_len_append (enc a) (enc_list enc q)

let sort_list_length (#u: Type) (lt: lt_t) (enc: u -> GTot SB.bytes) (l: list u)
: Lemma (Seq.length (sort_list lt enc l) == Seq.length (enc_list enc l))
= sort_acc_length lt enc Seq.empty l

#pop-options

(* The orders: `lt w e` is true if the frame `w` must come before `e` *)

(* SET OF (X.690 11.6): by encoding, lexicographically *)
let lt_lex : lt_t = fun w e -> not (Set.lex_byte_order e w)

(* SET (X.690 10.3): by tag *)
let parse_id (w: SB.bytes) : GTot (option asn1_id_t) =
  match SB.parse IdU.parse_asn1_identifier_U32 w with
  | Some (a, _) -> Some a
  | None -> None

let lt_tag : lt_t = fun w e ->
  match parse_id w, parse_id e with
  | Some a, Some b -> asn1_tag_lt a b
  | _ -> false

(* Implementation *)

let slice_full (w: SB.bytes) : Lemma (Seq.slice w 0 (Seq.length w) == w) =
  assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

inline_for_extraction
let lt_impl_t (lt: lt_t) =
  (out: S.slice U8.t) -> (#pm: perm) -> (#v: Ghost.erased SB.bytes) -> (ws: SZ.t) -> (we: SZ.t) -> (es: SZ.t) -> (ee: SZ.t) ->
  stt bool
    (S.pts_to out #pm v ** pure (SZ.v ws <= SZ.v we /\ SZ.v we <= Seq.length v /\ SZ.v es <= SZ.v ee /\ SZ.v ee <= Seq.length v))
    (fun res -> S.pts_to out #pm v ** pure (
      SZ.v ws <= SZ.v we /\ SZ.v we <= Seq.length v /\ SZ.v es <= SZ.v ee /\ SZ.v ee <= Seq.length v /\
      res == lt (Seq.slice v (SZ.v ws) (SZ.v we)) (Seq.slice v (SZ.v es) (SZ.v ee))))

inline_for_extraction
fn lt_lex_impl (_: unit)
: lt_impl_t lt_lex
= (out: S.slice U8.t) (#pm: perm) (#v: Ghost.erased SB.bytes) (ws: SZ.t) (we: SZ.t) (es: SZ.t) (ee: SZ.t)
{
  let c = SetOf.compare_ranges out es ee ws we;
  not c
}

inline_for_extraction
fn read_id (out: S.slice U8.t) (#pm: perm) (#v: Ghost.erased SB.bytes) (s e: SZ.t)
requires S.pts_to out #pm v ** pure (SZ.v s <= SZ.v e /\ SZ.v e <= Seq.length v)
returns res: option asn1_id_t
ensures S.pts_to out #pm v ** pure (SZ.v s <= SZ.v e /\ SZ.v e <= Seq.length v /\ res == parse_id (Seq.slice v (SZ.v s) (SZ.v e)))
{
  let sub = SU.subslice_trade out #pm s e;
  S.pts_to_len sub;
  slice_full (Seq.slice v (SZ.v s) (SZ.v e));
  let mut poff = 0sz;
  let r = I.vread_identifier sub poff;
  Trade.elim _ _;
  r
}

inline_for_extraction
fn lt_tag_impl (_: unit)
: lt_impl_t lt_tag
= (out: S.slice U8.t) (#pm: perm) (#v: Ghost.erased SB.bytes) (ws: SZ.t) (we: SZ.t) (es: SZ.t) (ee: SZ.t)
{
  let a = read_id out ws we;
  match a {
    None -> { false }
    Some ia -> {
      let b = read_id out es ee;
      match b {
        None -> { false }
        Some ib -> { SetComp.tag_lt ia ib }
      }
    }
  }
}

let frame_len_id_none (r: SB.bytes) (off1: SZ.t)
: Lemma (requires VR.vreader_postcond #asn1_strong_parser_kind IdU.parse_asn1_identifier_U32 0sz r off1 None)
  (ensures frame_len r == 0)
= slice_full r

let frame_len_read_len (r: SB.bytes) (off1: SZ.t) (id: asn1_id_t) (off2: SZ.t)
  (ol: option (LowParse.Spec.BoundedInt.bounded_int32 0 ILC.asn1_length_max))
: Lemma (requires VR.vreader_postcond #asn1_strong_parser_kind IdU.parse_asn1_identifier_U32 0sz r off1 (Some id) /\
    VR.vreader_postcond (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 r off2 ol)
  (ensures (match ol with
    | None -> frame_len r == 0
    | Some len -> frame_len r == (if SZ.v off2 + U32.v len <= Seq.length r then SZ.v off2 + U32.v len else 0)))
= slice_full r

(* The length of the frame at `out[q..p0)` *)
fn read_frame (out: S.slice U8.t) (#v: Ghost.erased SB.bytes) (q p0: SZ.t)
requires S.pts_to out v ** pure (SZ.v q <= SZ.v p0 /\ SZ.v p0 <= Seq.length v)
returns n: SZ.t
ensures S.pts_to out v ** pure (SZ.v q <= SZ.v p0 /\ SZ.v p0 <= Seq.length v /\ SZ.v n == frame_len (Seq.slice v (SZ.v q) (SZ.v p0)))
{
  let sub = SU.subslice_trade out q p0;
  S.pts_to_len sub;
  slice_full (Seq.slice v (SZ.v q) (SZ.v p0));
  let mut poff = 0sz;
  let oid = I.vread_identifier sub poff;
  with off1 . assert (pts_to poff off1);
  match oid {
    None -> {
      frame_len_id_none (Seq.slice v (SZ.v q) (SZ.v p0)) off1;
      Trade.elim _ _;
      0sz
    }
    Some id -> {
      let ol = ILC.vread_length sub poff;
      with off2 . assert (pts_to poff off2);
      frame_len_read_len (Seq.slice v (SZ.v q) (SZ.v p0)) off1 id off2 ol;
      match ol {
        None -> {
          Trade.elim _ _;
          0sz
        }
        Some len -> {
          let n2 = !poff;
          let rem = SZ.sub (S.len sub) n2;
          let ok = SCmp.u32_lte_sizet len rem;
          Trade.elim _ _;
          if ok {
            SZ.fits_lte (U32.v len) (SZ.v rem);
            SZ.add n2 (SZ.uint32_to_sizet len)
          } else {
            0sz
          }
        }
      }
    }
  }
}

(* In-place rotation: out[lo..mid) ++ out[mid..hi) becomes
   out[mid..hi) ++ out[lo..mid), by three reversals *)

#push-options "--z3rlimit 64"

let rotate_lemma (v v1 v2 v3: SB.bytes) (lo mid hi k: nat)
: Lemma
  (requires
    lo <= mid /\ mid <= hi /\ hi <= Seq.length v /\ k == lo + (hi - mid) /\
    reverse_range_post v lo hi v1 /\
    reverse_range_post v1 lo k v2 /\
    reverse_range_post v2 k hi v3)
  (ensures
    Seq.length v3 == Seq.length v /\
    Seq.slice v3 hi (Seq.length v) == Seq.slice v hi (Seq.length v) /\
    Seq.slice v3 lo hi == Seq.append (Seq.slice v mid hi) (Seq.slice v lo mid))
= let n = Seq.length v in
  let a = Seq.slice v lo mid in
  let b = Seq.slice v mid hi in
  assert (Seq.equal (Seq.slice v lo hi) (Seq.append a b));
  seq_rev_append a b;
  assert (Seq.equal (Seq.slice v1 lo k) (Seq.slice (Seq.slice v1 lo hi) 0 (k - lo)));
  assert (Seq.equal (Seq.slice v1 lo k) (seq_rev b));
  assert (Seq.equal (Seq.slice v1 k hi) (Seq.slice (Seq.slice v1 lo hi) (k - lo) (hi - lo)));
  assert (Seq.equal (Seq.slice v1 k hi) (seq_rev a));
  seq_rev_rev a;
  seq_rev_rev b;
  assert (Seq.equal (Seq.slice v2 k hi) (Seq.slice (Seq.slice v2 k n) 0 (hi - k)));
  assert (Seq.equal (Seq.slice v1 k hi) (Seq.slice (Seq.slice v1 k n) 0 (hi - k)));
  assert (Seq.equal (Seq.slice v2 hi n) (Seq.slice (Seq.slice v2 k n) (hi - k) (n - k)));
  assert (Seq.equal (Seq.slice v1 hi n) (Seq.slice (Seq.slice v1 lo n) (hi - lo) (n - lo)));
  assert (Seq.equal (Seq.slice v3 lo k) (Seq.slice (Seq.slice v3 0 k) lo k));
  assert (Seq.equal (Seq.slice v2 lo k) (Seq.slice (Seq.slice v2 0 k) lo k));
  assert (Seq.equal (Seq.slice v3 lo hi) (Seq.append (Seq.slice v3 lo k) (Seq.slice v3 k hi)))

#pop-options

inline_for_extraction
fn rotate (out: S.slice U8.t) (#v: Ghost.erased SB.bytes) (lo mid hi: SZ.t)
requires S.pts_to out v ** pure (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ SZ.v hi <= Seq.length v)
ensures exists* v' . S.pts_to out v' ** pure (
  SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi /\ SZ.v hi <= Seq.length v /\
  Seq.length v' == Seq.length v /\
  Seq.slice v' (SZ.v hi) (Seq.length v) == Seq.slice v (SZ.v hi) (Seq.length v) /\
  Seq.slice v' (SZ.v lo) (SZ.v hi) == Seq.append (Seq.slice v (SZ.v mid) (SZ.v hi)) (Seq.slice v (SZ.v lo) (SZ.v mid)))
{
  r2l_reverse_range out lo hi;
  with v1 . assert (S.pts_to out v1);
  let k = SZ.add lo (SZ.sub hi mid);
  r2l_reverse_range out lo k;
  with v2 . assert (S.pts_to out v2);
  r2l_reverse_range out k hi;
  with v3 . assert (S.pts_to out v3);
  rotate_lemma v v1 v2 v3 (SZ.v lo) (SZ.v mid) (SZ.v hi) (SZ.v k);
  assert (pure (Seq.length v3 == Seq.length v));
  assert (pure (Seq.slice v3 (SZ.v hi) (Seq.length v) == Seq.slice v (SZ.v hi) (Seq.length v)));
  ()
}

(* The insertion step *)

let insert_post (lt: lt_t) (v: SB.bytes) (p2 p1 p0: nat) (v': SB.bytes) : prop =
  p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v /\
  Seq.length v' == Seq.length v /\
  Seq.slice v' p0 (Seq.length v) == Seq.slice v p0 (Seq.length v) /\
  Seq.slice v' p2 p0 == ins lt (Seq.slice v p2 p1) (Seq.slice v p1 p0)

let ins_inv (lt: lt_t) (v: SB.bytes) (p2 p1 p0 q: nat) (cont: bool) : prop =
  p2 <= p1 /\ p1 <= q /\ q <= p0 /\ p0 <= Seq.length v /\
  ins lt (Seq.slice v p2 p1) (Seq.slice v p1 p0) == Seq.append (Seq.slice v p1 q) (ins lt (Seq.slice v p2 p1) (Seq.slice v q p0)) /\
  (cont == false ==> ins lt (Seq.slice v p2 p1) (Seq.slice v q p0) == Seq.append (Seq.slice v p2 p1) (Seq.slice v q p0))

let ins_inv_init (lt: lt_t) (v: SB.bytes) (p2 p1 p0: nat)
: Lemma (requires p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v)
  (ensures ins_inv lt v p2 p1 p0 p1 true)
= let x = ins lt (Seq.slice v p2 p1) (Seq.slice v p1 p0) in
  assert (Seq.equal (Seq.append (Seq.slice v p1 p1) x) x)

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"

let ins_inv_step (lt: lt_t) (v: SB.bytes) (p2 p1 p0 q n: nat)
: Lemma (requires ins_inv lt v p2 p1 p0 q true /\ n == frame_len (Seq.slice v q p0) /\ n > 0 /\
    lt (Seq.slice v q (q + n)) (Seq.slice v p2 p1))
  (ensures q + n <= p0 /\ ins_inv lt v p2 p1 p0 (q + n) true)
= frame_len_le (Seq.slice v q p0);
  let e = Seq.slice v p2 p1 in
  Seq.slice_slice v q p0 0 n;
  Seq.slice_slice v q p0 n (p0 - q);
  let r = Seq.slice v q p0 in
  assert (Seq.slice r 0 n == Seq.slice v q (q + n));
  assert (Seq.slice r n (Seq.length r) == Seq.slice v (q + n) p0);
  ins_step lt e r;
  assert (ins lt e (Seq.slice v q p0) == Seq.append (Seq.slice v q (q + n)) (ins lt e (Seq.slice v (q + n) p0)));
  Seq.append_assoc (Seq.slice v p1 q) (Seq.slice v q (q + n)) (ins lt e (Seq.slice v (q + n) p0));
  slice_split v p1 q (q + n)

let ins_inv_stop (lt: lt_t) (v: SB.bytes) (p2 p1 p0 q n: nat)
: Lemma (requires ins_inv lt v p2 p1 p0 q true /\ n == frame_len (Seq.slice v q p0) /\
    (n == 0 \/ (q + n <= p0 /\ not (lt (Seq.slice v q (q + n)) (Seq.slice v p2 p1)))))
  (ensures ins_inv lt v p2 p1 p0 q false)
= frame_len_le (Seq.slice v q p0);
  Seq.slice_slice v q p0 0 n

let ins_inv_end (lt: lt_t) (v: SB.bytes) (p2 p1 p0 q: nat) (v': SB.bytes)
: Lemma (requires ins_inv lt v p2 p1 p0 q false /\
    Seq.length v' == Seq.length v /\
    Seq.slice v' q (Seq.length v) == Seq.slice v q (Seq.length v) /\
    Seq.slice v' p2 q == Seq.append (Seq.slice v p1 q) (Seq.slice v p2 p1))
  (ensures insert_post lt v p2 p1 p0 v')
= let n = Seq.length v in
  Seq.slice_slice v' q n (p0 - q) (n - q);
  Seq.slice_slice v q n (p0 - q) (n - q);
  Seq.slice_slice v' q n 0 (p0 - q);
  Seq.slice_slice v q n 0 (p0 - q);
  assert (Seq.equal (Seq.slice v' p2 p0) (Seq.append (Seq.slice v' p2 q) (Seq.slice v' q p0)));
  Seq.append_assoc (Seq.slice v p1 q) (Seq.slice v p2 p1) (Seq.slice v q p0)

#pop-options

(* Given out[p2..p1) == e and out[p1..p0) == r, make out[p2..p0) == ins lt e r *)
inline_for_extraction
fn r2l_insert (lt: lt_t) (lt_impl: lt_impl_t lt) (out: S.slice U8.t) (#v: Ghost.erased SB.bytes) (p2 p1 p0: SZ.t)
requires S.pts_to out v ** pure (SZ.v p2 <= SZ.v p1 /\ SZ.v p1 <= SZ.v p0 /\ SZ.v p0 <= Seq.length v)
ensures exists* v' . S.pts_to out v' ** pure (insert_post lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) v')
{
  S.pts_to_len out;
  ins_inv_init lt v (SZ.v p2) (SZ.v p1) (SZ.v p0);
  let mut pq = p1;
  let mut pcont = true;
  while (
    !pcont
  ) invariant exists* q c .
    R.pts_to pq q ** R.pts_to pcont c ** S.pts_to out v **
    pure (ins_inv lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) (SZ.v q) c)
  decreases %[(if !pcont then 1 else 0); SZ.v p0 - SZ.v (!pq)]
  {
    let q = !pq;
    let n = read_frame out q p0;
    frame_len_le (Seq.slice v (SZ.v q) (SZ.v p0));
    if (SZ.eq n 0sz) {
      ins_inv_stop lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) (SZ.v q) (SZ.v n);
      pcont := false
    } else {
      let qn = SZ.add q n;
      let b = lt_impl out q qn p2 p1;
      if b {
        ins_inv_step lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) (SZ.v q) (SZ.v n);
        pq := qn
      } else {
        ins_inv_stop lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) (SZ.v q) (SZ.v n);
        pcont := false
      }
    }
  };
  let q = !pq;
  rotate out p2 p1 q;
  with v' . assert (S.pts_to out v');
  ins_inv_end lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) (SZ.v q) v';
  ()
}

(* Inserting right after an R2L write *)

let slice_eq_sub (a b: SB.bytes) (i k j1 j2: nat)
: Lemma (requires i <= j1 /\ j1 <= j2 /\ j2 <= k /\ k <= Seq.length a /\ Seq.length b == Seq.length a /\
    Seq.slice a i k == Seq.slice b i k)
  (ensures Seq.slice a j1 j2 == Seq.slice b j1 j2)
= Seq.slice_slice a i k (j1 - i) (j2 - i);
  Seq.slice_slice b i k (j1 - i) (j2 - i)

#push-options "--fuel 0 --ifuel 0"

let r2l_post_ins
  (lt: lt_t) (enc1 enc2: SB.bytes) (p: nat) (v: SB.bytes) (p1: nat) (v1: SB.bytes) (p2: nat) (v2: SB.bytes) (v3: SB.bytes)
: Lemma
  (requires r2l_post enc2 p v true p1 v1 /\ r2l_post enc1 p1 v1 true p2 v2 /\ insert_post lt v2 p2 p1 p v3)
  (ensures r2l_post (ins lt enc1 enc2) p v true p2 v3)
= let n = Seq.length v in
  ins_length lt enc1 enc2;
  slice_eq_sub v2 v1 p1 n p1 p;
  slice_eq_sub v2 v1 p1 n p n

#pop-options

(* Sorted mixed lists *)

let r2l_mls_inv
  (#t: Type) (lt: lt_t) (enc: t -> GTot SB.bytes) (l: list t)
  (p0: nat) (v0: SB.bytes)
  (ld: list t) (ok: bool) (pc: nat) (vc: SB.bytes)
: Tot prop
= Seq.length vc == Seq.length v0 /\
  p0 <= Seq.length v0 /\
  Seq.slice vc p0 (Seq.length v0) == Seq.slice v0 p0 (Seq.length v0) /\
  (ok == true ==> (
    pc + Seq.length (sort_list lt enc ld) == p0 /\
    Seq.slice vc pc p0 == sort_list lt enc ld
  )) /\
  (ok == false ==> Seq.length (enc_list enc l) > p0)

let r2l_mls_inv_init (#t: Type) (lt: lt_t) (enc: t -> GTot SB.bytes) (l: list t) (p0: nat) (v0: SB.bytes)
: Lemma
  (requires p0 <= Seq.length v0)
  (ensures r2l_mls_inv lt enc l p0 v0 [] true p0 v0)
= assert (Seq.equal (Seq.slice v0 p0 p0) (sort_list lt enc []))

#push-options "--z3rlimit 64"

let r2l_mls_inv_fail
  (#t: Type) (lt: lt_t) (enc: t -> GTot SB.bytes) (l: list t)
  (p0: nat) (v0: SB.bytes)
  (ld: list t) (y: t) (tl: list t) (pc: nat) (vc: SB.bytes)
  (p2: nat) (v2: SB.bytes)
: Lemma
  (requires
    r2l_mls_inv lt enc l p0 v0 ld true pc vc /\
    l == List.Tot.append ld (y :: tl) /\
    r2l_post (enc y) pc vc false p2 v2)
  (ensures r2l_mls_inv lt enc l p0 v0 (List.Tot.append ld [y]) false p2 v2)
= enc_list_append enc ld (y :: tl);
  sort_list_length lt enc ld;
  Seq.slice_slice v2 pc (Seq.length v0) (p0 - pc) (Seq.length v0 - pc);
  Seq.slice_slice vc pc (Seq.length v0) (p0 - pc) (Seq.length v0 - pc)

let r2l_mls_inv_step
  (#t: Type) (lt: lt_t) (enc: t -> GTot SB.bytes) (l: list t)
  (p0: nat) (v0: SB.bytes)
  (ld: list t) (y: t) (pc: nat) (vc: SB.bytes)
  (p2: nat) (v2: SB.bytes) (v3: SB.bytes)
: Lemma
  (requires
    r2l_mls_inv lt enc l p0 v0 ld true pc vc /\
    r2l_post (enc y) pc vc true p2 v2 /\
    insert_post lt v2 p2 pc p0 v3)
  (ensures r2l_mls_inv lt enc l p0 v0 (List.Tot.append ld [y]) true p2 v3)
= let n = Seq.length v0 in
  sort_acc_snoc lt enc Seq.empty ld y;
  ins_length lt (enc y) (sort_list lt enc ld);
  Seq.slice_slice v2 pc n (p0 - pc) (n - pc);
  Seq.slice_slice vc pc n (p0 - pc) (n - pc);
  Seq.slice_slice v2 pc n 0 (p0 - pc);
  Seq.slice_slice vc pc n 0 (p0 - pc);
  Seq.slice_slice v3 p0 n 0 (n - p0);
  Seq.slice_slice v2 p0 n 0 (n - p0)

#pop-options

let r2l_mls_inv_end
  (#t: Type) (lt: lt_t) (enc: t -> GTot SB.bytes) (l: list t)
  (p0: nat) (v0: SB.bytes)
  (pc: nat) (vc: SB.bytes)
: Lemma
  (requires r2l_mls_inv lt enc l p0 v0 l true pc vc)
  (ensures r2l_post (sort_list lt enc l) p0 v0 true pc vc)
= ()

let r2l_mls_inv_end_fail
  (#t: Type) (lt: lt_t) (enc: t -> GTot SB.bytes) (l: list t)
  (p0: nat) (v0: SB.bytes)
  (ld: list t) (pc: nat) (vc: SB.bytes)
: Lemma
  (requires r2l_mls_inv lt enc l p0 v0 ld false pc vc)
  (ensures r2l_post (sort_list lt enc l) p0 v0 false pc vc)
= sort_list_length lt enc l

(* The sorted mixed list writer: like `r2l_write_mixed_list_gen`, but
   each element is inserted into the sorted region instead of being
   reversed *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn r2l_write_mixed_list_sorted_gen
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop) (#i: Type0) (io: IO.int_ops i)
  (#k: Ghost.erased parser_kind) (#p: parser k u) (enc: u -> GTot SB.bytes)
  (enc_ok: enc_consumed p enc)
  (j: LPS.jumper p)
  (w: (pm: perm) -> r2l_writer_f (vmatch pm) enc)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (lt: lt_t) (lt_impl: lt_impl_t lt)
  (pm: perm)
: r2l_writer_f #(mixed_list i t) #(list u) (mixed_list_match vmatch io p pm) (sort_list lt enc)
= (ml: mixed_list i t)
  (#l: Ghost.erased (list u))
  (out: S.slice byte)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p0: Ghost.erased SZ.t)
{
  mixed_list_match_length vmatch io p pm ml l;
  let n0 = mixed_list_length io ml;
  let it0 = iterator_start vmatch io p j pm ml l vmatch_share vmatch_gather;
  with pm0 . assert (iterator_match vmatch io p pm0 it0 l);
  let mut pit = it0;
  let mut pn = n0;
  let mut pok = true;
  r2l_mls_inv_init lt enc l (SZ.v p0) v;
  let p0r = !pos;
  let mut pld : Ghost.erased (list u) = Ghost.hide [];
  while (
    let ok = !pok;
    let n = !pn;
    (ok && not (io.eq n io.zero))
  ) invariant exists* (it: iterator i t) (pmi: perm) (ld: Ghost.erased (list u)) (lr: list u) (n: i) (ok: bool) (vc: SB.bytes) (pc: SZ.t) .
    R.pts_to pit it ** R.pts_to pld ld **
    iterator_match vmatch io p pmi it lr **
    trade (iterator_match vmatch io p pmi it lr) (mixed_list_match vmatch io p pm ml l) **
    R.pts_to pn n ** R.pts_to pok ok **
    S.pts_to out vc ** R.pts_to pos pc **
    pure (
      Ghost.reveal l == List.Tot.append (Ghost.reveal ld) lr /\
      io.v n == List.Tot.length lr /\
      SZ.v p0r == SZ.v p0 /\
      r2l_mls_inv lt enc l (SZ.v p0) v (Ghost.reveal ld) ok (SZ.v pc) vc
    )
  decreases %[(if !pok then 1 else 0); io.v (!pn)]
  {
    with it pmi lr . assert (R.pts_to pit it ** iterator_match vmatch io p pmi it lr);
    with vc pc . assert (S.pts_to out vc ** R.pts_to pos pc);
    let ld = !pld;
    let n = !pn;
    let pcur = !pos;
    let x = iterator_next_eos vmatch io p j pmi pit it lr vmatch_share vmatch_gather;
    unfold (iterator_next_eos_post vmatch io p pmi pit it lr x);
    with pm_v y tl it' pm' . assert (
      elt_or_serialized_match vmatch io p pm_v x y **
      R.pts_to pit it' **
      iterator_match vmatch io p pm' it' tl);
    let res = r2l_write_elt_or_serialized_gen vmatch io enc enc_ok w pm_v x #y out pos;
    Trade.elim_hyp_l (elt_or_serialized_match vmatch io p pm_v x y) (iterator_match vmatch io p pm' it' tl) (iterator_match vmatch io p pmi it lr);
    Trade.trans (iterator_match vmatch io p pm' it' tl) (iterator_match vmatch io p pmi it lr) (mixed_list_match vmatch io p pm ml l);
    append_assoc_singleton #u (Ghost.reveal ld) y tl;
    pn := io.sub n io.one;
    pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
    with v2 p2 . assert (S.pts_to out v2 ** R.pts_to pos p2);
    if (res) {
      let pnew = !pos;
      r2l_insert lt lt_impl out pnew pcur p0r;
      with v3 . assert (S.pts_to out v3);
      with ok0 . assert (R.pts_to pok ok0);
      r2l_mls_inv_step lt enc l (SZ.v p0) v (Ghost.reveal ld) y (SZ.v pc) vc (SZ.v p2) v2 v3;
      assert (pure (r2l_mls_inv lt enc l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) ok0 (SZ.v p2) v3));
    } else {
      r2l_mls_inv_fail lt enc l (SZ.v p0) v (Ghost.reveal ld) y tl (SZ.v pc) vc (SZ.v p2) v2;
      pok := false;
    }
  };
  with it pmi lr . assert (R.pts_to pit it ** iterator_match vmatch io p pmi it lr);
  with vc pc . assert (S.pts_to out vc ** R.pts_to pos pc);
  let ld = !pld;
  Trade.elim (iterator_match vmatch io p pmi it lr) (mixed_list_match vmatch io p pm ml l);
  let ok = !pok;
  if (ok) {
    List.Tot.append_l_nil (Ghost.reveal ld);
    r2l_mls_inv_end lt enc l (SZ.v p0) v (SZ.v pc) vc;
    true
  } else {
    r2l_mls_inv_end_fail lt enc l (SZ.v p0) v (Ghost.reveal ld) (SZ.v pc) vc;
    false
  }
}

#pop-options
