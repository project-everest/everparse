module ASN1.Pulse.SetOf
#lang-pulse
(* Validators for SET OF: a list of TLVs whose encodings are sorted in
   non-decreasing lexicographic order (X.690 11.6). The loop keeps the
   offsets of the previous element; bytes are never copied. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.Set
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module I16 = FStar.Int16
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module SU = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module T = LowParse.Tot.Combinators
module SSB = LowParse.Spec.SeqBytes
module Sorted = LowParse.Spec.Sorted
module Lex = LowParse.Pulse.Lex

(* The ASN.1 byte order is the LowParse lexicographic byte comparison *)

let rec lex_byte_order'_eq
  (n1: nat)
  (b1: Seq.lseq byte n1)
  (n2: nat)
  (b2: Seq.lseq byte n2)
: Lemma
  (ensures (lex_byte_order' n1 b1 n2 b2 == (SSB.bytes_lex_compare b1 b2 <= 0)))
  (decreases (n1 + n2))
= if n1 = 0 || n2 = 0
  then ()
  else begin
    assert (b1 `Seq.equal` Seq.cons (Seq.index b1 0) (Seq.slice b1 1 n1));
    assert (b2 `Seq.equal` Seq.cons (Seq.index b2 0) (Seq.slice b2 1 n2));
    Seq.lemma_seq_to_list_cons (Seq.index b1 0) (Seq.slice b1 1 n1);
    Seq.lemma_seq_to_list_cons (Seq.index b2 0) (Seq.slice b2 1 n2);
    lex_byte_order'_eq (n1 - 1) (Seq.slice b1 1 n1) (n2 - 1) (Seq.slice b2 1 n2)
  end

let lex_byte_order_eq (b1 b2: bytes)
: Lemma (lex_byte_order b1 b2 == (SSB.bytes_lex_compare b1 b2 <= 0))
= lex_byte_order'_eq (Seq.length b1) b1 (Seq.length b2) b2

(* The spec parser, as a loop *)

let lbo (x y: bytes) : Pure bool True (fun z -> z == true <==> prop_order_of_bool_order lex_byte_order x y) =
  lex_byte_order x y

let rec aux_consumes_all
  (#t: Type)
  (p: parser asn1_strong_parser_kind t)
  (prev: bytes)
  (b: bytes)
: Lemma
  (ensures (match tot_parse_byte_sorted_list_aux lbo p prev b with
    | None -> True
    | Some (_, n) -> n == Seq.length b))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then ()
  else match p b with
  | None -> ()
  | Some (_, n) ->
    if n = 0 then ()
    else aux_consumes_all p (Seq.slice b 0 n) (Seq.slice b n (Seq.length b))

let set_of_consumed
  (#t: Type)
  (p: parser asn1_strong_parser_kind t)
  (b: bytes)
: GTot (option nat)
= match tot_parse_byte_sorted_list_bare lbo p b with
  | None -> None
  | Some (_, n) -> Some n

let set_of_parse_eq (#t: Type) (p: parser asn1_strong_parser_kind t) (b: bytes)
: Lemma (SB.parse (parse_asn1_set_of p) b == tot_parse_byte_sorted_list_bare lbo p b)
= let q = tot_parse_byte_sorted_list lex_byte_order p in
  assert (SB.parse (parse_asn1_set_of p) b == SB.parse q b);
  assert (SB.parse q b == SB.parse (parse_byte_sorted_list (prop_order_of_bool_order lex_byte_order) #_ #asn1_strong_parser_kind p) b);
  tot_parse_byte_sorted_list_correct (prop_order_of_bool_order lex_byte_order) lbo #_ #asn1_strong_parser_kind p b

let sized_set_eq (ne: bool) (#t: Type) (p: parser asn1_strong_parser_kind t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (parse_sized_set ne #t p) b ==
    (if Seq.length b = 0
     then (if ne then None else Some 0)
     else set_of_consumed p b) /\
    (match set_of_consumed p b with None -> True | Some n -> n == Seq.length b))
= T.parse_filter_eq #asn1_weak_parser_kind (parse_asn1_set_of p) (list_size_ok ne) b;
  set_of_parse_eq p b;
  if Seq.length b = 0
  then ()
  else match p b with
  | None -> ()
  | Some (_, n) ->
    if n = 0 then ()
    else aux_consumes_all p (Seq.slice b 0 n) (Seq.slice b n (Seq.length b))

let aux_step
  (#t: Type)
  (p: parser asn1_strong_parser_kind t)
  (v: bytes)
  (ps pe off: nat)
: Lemma
  (requires (ps <= pe /\ pe <= Seq.length v /\ off < Seq.length v))
  (ensures (
    Some? (tot_parse_byte_sorted_list_aux lbo p (Seq.slice v ps pe) (Seq.slice v off (Seq.length v))) ==
    (match consumed #asn1_strong_parser_kind p (Seq.slice v off (Seq.length v)) with
     | None -> false
     | Some n -> n > 0 &&
       lex_byte_order (Seq.slice v ps pe) (Seq.slice v off (off + n)) &&
       Some? (tot_parse_byte_sorted_list_aux lbo p (Seq.slice v off (off + n)) (Seq.slice v (off + n) (Seq.length v))))))
= let b = Seq.slice v off (Seq.length v) in
  match p b with
  | None -> ()
  | Some (_, n) ->
    Seq.slice_slice v off (Seq.length v) 0 n;
    Seq.slice_slice v off (Seq.length v) n (Seq.length v - off)

let bare_step
  (#t: Type)
  (p: parser asn1_strong_parser_kind t)
  (v: bytes)
  (off: nat)
: Lemma
  (requires (off < Seq.length v))
  (ensures (
    Some? (tot_parse_byte_sorted_list_bare lbo p (Seq.slice v off (Seq.length v))) ==
    (match consumed #asn1_strong_parser_kind p (Seq.slice v off (Seq.length v)) with
     | None -> false
     | Some n -> n > 0 &&
       Some? (tot_parse_byte_sorted_list_aux lbo p (Seq.slice v off (off + n)) (Seq.slice v (off + n) (Seq.length v))))))
= let b = Seq.slice v off (Seq.length v) in
  match p b with
  | None -> ()
  | Some (_, n) ->
    Seq.slice_slice v off (Seq.length v) 0 n;
    Seq.slice_slice v off (Seq.length v) n (Seq.length v - off)

(* Compare two (possibly overlapping) byte ranges of the same input *)

inline_for_extraction
fn compare_ranges
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (s1 e1 s2 e2: SZ.t)
requires
  S.pts_to input #pm v **
  pure (SZ.v s1 <= SZ.v e1 /\ SZ.v e1 <= Seq.length v /\ SZ.v s2 <= SZ.v e2 /\ SZ.v e2 <= Seq.length v)
returns res: bool
ensures
  S.pts_to input #pm v **
  pure (SZ.v s1 <= SZ.v e1 /\ SZ.v e1 <= Seq.length v /\ SZ.v s2 <= SZ.v e2 /\ SZ.v e2 <= Seq.length v /\
    res == lex_byte_order (Seq.slice v (SZ.v s1) (SZ.v e1)) (Seq.slice v (SZ.v s2) (SZ.v e2)))
{
  S.share input;
  let i1 = SU.subslice_trade input #(pm /. 2.0R) s1 e1;
  let i2 = SU.subslice_trade input #(pm /. 2.0R) s2 e2;
  let c = Lex.impl_bytes_lex_compare i1 i2;
  Trade.elim (S.pts_to i1 #(pm /. 2.0R) (Seq.slice v (SZ.v s1) (SZ.v e1))) _;
  Trade.elim (S.pts_to i2 #(pm /. 2.0R) (Seq.slice v (SZ.v s2) (SZ.v e2))) _;
  S.gather input;
  lex_byte_order_eq (Seq.slice v (SZ.v s1) (SZ.v e1)) (Seq.slice v (SZ.v s2) (SZ.v e2));
  (I16.lte c 0s)
}

(* SET OF, non-empty if SIZE (1..MAX) *)

inline_for_extraction
fn validate_sized_set
  (ne: bool)
  (#t: Type0)
  (#p: parser asn1_strong_parser_kind t)
  (v: LPS.validator #t #asn1_strong_parser_kind p)
: LPS.validator #(sized_list ne t) #asn1_weak_parser_kind (parse_sized_set ne #t p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  S.pts_to_len input;
  let input_len = S.len input;
  let off0 = !poffset;
  sized_set_eq ne p (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  if (off0 = input_len) {
    not ne
  } else {
    let mut pcontinue = true;
    let mut pfirst = true;
    let mut pstart = off0;
    let mut pend = off0;
    while (
      let c = !pcontinue;
      let off = !poffset;
      (c && SZ.lt off input_len)
    ) invariant exists* c first off ps pe .
      R.pts_to pcontinue c **
      R.pts_to pfirst first **
      R.pts_to poffset off **
      R.pts_to pstart ps **
      R.pts_to pend pe **
      S.pts_to input #pm v_bytes **
      pure (
        SZ.v ps <= SZ.v pe /\ SZ.v pe <= Seq.length v_bytes /\ SZ.v off <= Seq.length v_bytes /\
        (c == true ==> (
          if first
          then SZ.v off == SZ.v offset /\ SZ.v off < Seq.length v_bytes
          else SZ.v pe <= SZ.v off /\
            (Some? (tot_parse_byte_sorted_list_bare lbo p (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes))) ==
             Some? (tot_parse_byte_sorted_list_aux lbo p (Seq.slice v_bytes (SZ.v ps) (SZ.v pe)) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes)))))) /\
        (c == false ==> None? (tot_parse_byte_sorted_list_bare lbo p (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes))))
      )
      decreases %[(if !pcontinue then 1 else 0); (SZ.v input_len - SZ.v (!poffset))]
    {
      let off = !poffset;
      let ps = !pstart;
      let pe = !pend;
      let first = !pfirst;
      if first {
        bare_step p v_bytes (SZ.v off);
        ()
      } else {
        aux_step p v_bytes (SZ.v ps) (SZ.v pe) (SZ.v off);
        ()
      };
      let is_valid = v input poffset;
      if is_valid {
        let off' = !poffset;
        if (off' = off) {
          pcontinue := false
        } else {
          let sorted = (first || compare_ranges input ps pe off off');
          if sorted {
            pfirst := false;
            pstart := off;
            pend := off'
          } else {
            pcontinue := false
          }
        }
      } else {
        pcontinue := false
      }
    };
    let c = !pcontinue;
    c
  }
}
