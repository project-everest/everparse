module ASN1.Pulse.AnyDefinedBy
#lang-pulse
(* Validators for ANY DEFINED BY (a nonempty prefix is handled with
   ASN1.Pulse.SeqAny, see the end of this module): the key (e.g. an
   OBJECT IDENTIFIER) is not stored in memory; instead, the validator
   reads the identifier and length of the key, then tries each entry of
   the dispatch table in order, by checking that the key contents are
   equal to the entry key, and backtracking to the beginning of the key
   contents if not. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Choice
open ASN1.Spec.Any
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module SCo = LowParse.Spec.Combinators
module SL = LowParse.Spec.List
module SFL = LowParse.Spec.FLData
module SVG = LowParse.Spec.VLGen
module SDER = LowParse.Spec.DER
module T = LowParse.Tot.Combinators
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module OID = ASN1.Pulse.OID

(* Sequential composition and backtracking choice, on consumed lengths *)

let then_consumed (#k1: parser_kind) (#t1: Type) (p1: SB.parser k1 t1) (#k2: parser_kind) (#t2: Type) (p2: SB.parser k2 t2) (b: bytes) : GTot (option nat) =
  match consumed p1 b with
  | None -> None
  | Some c1 ->
    match consumed p2 (Seq.slice b c1 (Seq.length b)) with
    | None -> None
    | Some c2 -> Some (c1 + c2)

inline_for_extraction
fn validate_then_consumed
  (#t1: Type0) (#k1: Ghost.erased parser_kind) (#p1: SB.parser k1 t1) (v1: LPS.validator p1)
  (#t2: Type0) (#k2: Ghost.erased parser_kind) (#p2: SB.parser k2 t2) (v2: LPS.validator p2)
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: SB.parser k t { forall b . consumed p b == then_consumed p1 p2 b })
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  assert (pure (consumed p sinput == then_consumed p1 p2 sinput));
  if (v1 input poffset) {
    with off1 . assert (R.pts_to poffset off1);
    Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
    v2 input poffset
  } else {
    false
  }
}

inline_for_extraction
fn validate_try_else
  (#t1: Type0) (#k1: Ghost.erased parser_kind) (#p1: SB.parser k1 t1) (v1: LPS.validator p1)
  (#t2: Type0) (#k2: Ghost.erased parser_kind) (#p2: SB.parser k2 t2) (v2: LPS.validator p2)
  (#t3: Type0) (#k3: Ghost.erased parser_kind) (#p3: SB.parser k3 t3) (v3: LPS.validator p3)
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: SB.parser k t { forall b . consumed p b == (if Some? (consumed p1 b) then then_consumed p1 p2 b else consumed p3 b) })
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  assert (pure (consumed p sinput == (if Some? (consumed p1 sinput) then then_consumed p1 p2 sinput else consumed p3 sinput)));
  let off0 = !poffset;
  if (v1 input poffset) {
    with off1 . assert (R.pts_to poffset off1);
    Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
    v2 input poffset
  } else {
    poffset := off0;
    v3 input poffset
  }
}

(* OBJECT IDENTIFIER keys: equality with a constant, on the list of
   subidentifiers (X.690 8.19) *)

(* Named, so that SMT sees the same filter in all lemmas *)
let key_eq (#t: eqtype) (x: t) (y: t) : Tot bool = y = x

let oid_enc (x: asn1_oid_t) : Tot (list U32.t) =
  match x with
  | a :: b :: tl ->
    (if a = 2ul then U32.add 80ul b else U32.add (U32.mul 40ul a) b) :: tl

let synth_oid_eq (h: U32.t) (tl: list U32.t) (x: asn1_oid_t)
: Lemma (ASN1.Spec.Content.OIDU32.synth_OIDU32 (h, tl) == x <==> h :: tl == oid_enc x)
= ()

let subids_kind : parser_kind = SCo.parse_filter_kind (SL.parse_list_kind OID.subid_kind.parser_kind_injective)

let subids_eq_p (l: list U32.t) : Tot (SB.parser subids_kind (SCo.parse_filter_refine #(list U32.t) (key_eq l))) =
  SCo.parse_filter OID.subids (key_eq l)

#push-options "--z3rlimit 64 --ifuel 2"

let oid_filter_consumed (x: asn1_oid_t) (b: bytes)
: Lemma (consumed #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter (asn1_terminal_as_parser ASN1_OID) (key_eq x)) b == consumed (subids_eq_p (oid_enc x)) b)
= let open ASN1.Spec.Content.OIDU32 in
  lemma_synth_OIDU32_inj ();
  assert_norm (asn1_terminal_as_parser ASN1_OID == parse_asn1_OIDU32);
  SCo.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OID) (key_eq x) b;
  SCo.parse_filter_eq OID.subids (key_eq (oid_enc x)) b;
  let p = parse_asn1_identifier_U32_alt `T.nondep_then` parse_asn1_OIDU32_tail in
  T.parse_synth_eq p synth_OIDU32 b;
  T.nondep_then_eq parse_asn1_identifier_U32_alt parse_asn1_OIDU32_tail b;
  OID.subid_spec_eq b;
  SL.parse_list_eq OID.subid_spec b;
  SB.parser_kind_prop_equiv OID.subid_kind OID.subid_spec;
  match SB.parse OID.subid_spec b with
  | Some (h, n) ->
    OID.subids_eq (Seq.slice b n (Seq.length b));
    assert (SB.parse parse_asn1_identifier_U32_alt b == Some (h, n));
    begin match SB.parse OID.subids (Seq.slice b n (Seq.length b)) with
    | Some (tl, m) ->
      assert (SB.parse parse_asn1_OIDU32_tail (Seq.slice b n (Seq.length b)) == Some (tl, m));
      assert (SB.parse p b == Some ((h, tl), n + m));
      assert (SB.parse parse_asn1_OIDU32 b == Some (synth_OIDU32 (h, tl), n + m));
      assert (SB.parse OID.subids b == Some (h :: tl, n + m));
      synth_oid_eq h tl x;
      assert (consumed #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter (asn1_terminal_as_parser ASN1_OID) (key_eq x)) b == (if synth_OIDU32 (h, tl) = x then Some (n + m) else None));
      assert (consumed (subids_eq_p (oid_enc x)) b == (if h :: tl = oid_enc x then Some (n + m) else None))
    | _ -> ()
    end
  | _ -> ()

let subids_eq_nil (b: bytes)
: Lemma (consumed (subids_eq_p []) b == (if Seq.length b = 0 then Some 0 else None))
= SCo.parse_filter_eq OID.subids (key_eq []) b;
  SL.parse_list_eq OID.subid_spec b

let subids_eq_cons (h: U32.t) (tl: list U32.t) (b: bytes)
: Lemma (consumed (subids_eq_p (h :: tl)) b == (
    if Seq.length b = 0
    then None
    else match SB.parse OID.subid_spec b with
    | None -> None
    | Some (h', n) ->
      if h' = h
      then match consumed (subids_eq_p tl) (Seq.slice b n (Seq.length b)) with
        | None -> None
        | Some c -> Some (n + c)
      else None
  ))
= SCo.parse_filter_eq OID.subids (key_eq (h :: tl)) b;
  SL.parse_list_eq OID.subid_spec b;
  SB.parser_kind_prop_equiv OID.subid_kind OID.subid_spec;
  match SB.parse OID.subid_spec b with
  | Some (_, n) -> SCo.parse_filter_eq OID.subids (key_eq tl) (Seq.slice b n (Seq.length b))
  | _ -> ()

#pop-options

(* Extracted once as a C function *)
fn vread_subid_impl
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires S.pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: option U32.t
  ensures S.pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (vreader_postcond OID.subid_spec offset v off res))
{
  OID.vread_subid_spec input poffset
}

inline_for_extraction
let vread_subid : vreader OID.subid_spec = vread_subid_impl

inline_for_extraction
fn validate_subids_eq_nil (_: unit)
: LPS.validator #_ #subids_kind (subids_eq_p [])
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  subids_eq_nil (Seq.slice v (SZ.v offset) (Seq.length v));
  let off = !poffset;
  (off = S.len input)
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_subids_eq_cons (h: U32.t) (tl: Ghost.erased (list U32.t))
  (vtl: LPS.validator #_ #subids_kind (subids_eq_p tl))
: LPS.validator #_ #subids_kind (subids_eq_p (h :: tl))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  subids_eq_cons h tl (Seq.slice v (SZ.v offset) (Seq.length v));
  let off = !poffset;
  if (off = S.len input) {
    false
  } else {
    let r = vread_subid input poffset;
    match r {
      None -> { false }
      Some h' -> {
        if (h' = h) {
          with off1 . assert (R.pts_to poffset off1);
          Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
          vtl input poffset
        } else {
          false
        }
      }
    }
  }
}

#pop-options

(* Other keys: equality of the contents with a constant byte string, the
   DER encoding of the key (computed at extraction time from its literal) *)

let bytes_lit_val (e: list U8.t) : Tot (asn1_terminal_t ASN1_OCTETSTRING) = Seq.seq_of_list e

let bytes_eq_p (e: list U8.t)
: Tot (SB.parser (SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter_refine #(asn1_terminal_t ASN1_OCTETSTRING) (key_eq (bytes_lit_val e))))
= SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OCTETSTRING) (key_eq (bytes_lit_val e))

let parse_all_bytes_eq (b: bytes)
: Lemma (SB.parse (asn1_terminal_as_parser ASN1_OCTETSTRING) b == Some (b, Seq.length b))
= ASN1.Spec.Content.Enc.parse_leaf_enc ASN1_OCTETSTRING b

let bytes_eq_consumed (e: list U8.t) (b: bytes)
: Lemma ((Some? (consumed (bytes_eq_p e) b) <==> b == Seq.seq_of_list e) /\
    (Some? (consumed (bytes_eq_p e) b) ==> consumed (bytes_eq_p e) b == Some (Seq.length b)))
= SCo.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OCTETSTRING) (key_eq (bytes_lit_val e)) b;
  parse_all_bytes_eq b

let bytes_eq_nil (b: bytes)
: Lemma (consumed (bytes_eq_p []) b == (if Seq.length b = 0 then Some 0 else None))
= bytes_eq_consumed [] b;
  Seq.lemma_seq_of_list_induction #U8.t [];
  if Seq.length b = 0 then Seq.lemma_eq_elim b (Seq.seq_of_list #U8.t [])

let bytes_eq_cons (h: U8.t) (tl: list U8.t) (b: bytes)
: Lemma (consumed (bytes_eq_p (h :: tl)) b == (
    if Seq.length b = 0
    then None
    else if Seq.index b 0 = h
    then match consumed (bytes_eq_p tl) (Seq.slice b 1 (Seq.length b)) with
      | None -> None
      | Some c -> Some (1 + c)
    else None
  ))
= bytes_eq_consumed (h :: tl) b;
  Seq.lemma_seq_of_list_induction (h :: tl);
  if Seq.length b = 0
  then ()
  else begin
    let b' = Seq.slice b 1 (Seq.length b) in
    bytes_eq_consumed tl b';
    Seq.cons_head_tail b;
    assert (Seq.tail b == b');
    Classical.move_requires (Seq.lemma_cons_inj (Seq.head b) h b') (Seq.seq_of_list tl)
  end

inline_for_extraction
fn validate_bytes_eq_nil (_: unit)
: LPS.validator #_ #(SCo.parse_filter_kind asn1_weak_parser_kind) (bytes_eq_p [])
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  bytes_eq_nil (Seq.slice v (SZ.v offset) (Seq.length v));
  let off = !poffset;
  (off = S.len input)
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_bytes_eq_cons (h: U8.t) (tl: Ghost.erased (list U8.t))
  (vtl: LPS.validator #_ #(SCo.parse_filter_kind asn1_weak_parser_kind) (bytes_eq_p tl))
: LPS.validator #_ #(SCo.parse_filter_kind asn1_weak_parser_kind) (bytes_eq_p (h :: tl))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  bytes_eq_cons h tl (Seq.slice v (SZ.v offset) (Seq.length v));
  let off = !poffset;
  if (off = S.len input) {
    false
  } else {
    let h' = input.(off);
    if (h' = h) {
      poffset := SZ.add off 1sz;
      Seq.slice_slice v (SZ.v offset) (Seq.length v) 1 (Seq.length v - SZ.v offset);
      vtl input poffset
    } else {
      false
    }
  }
}

#pop-options

(* The key and the dispatch on its contents *)

let key_p (kid: asn1_id_t) (key_k: asn1_terminal_k) : Tot (asn1_strong_parser (asn1_terminal_t key_k)) =
  ASN1.Spec.ILC.parse_asn1_ILC kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k)

let disp_kind (l: nat) : Tot parser_kind = SCo.and_then_kind (SFL.parse_fldata_kind l asn1_weak_parser_kind) asn1_weak_parser_kind

let pl_spec
  (#key_t: Type)
  (#data_t: Type)
  (tag: data_t -> Tot key_t)
  (pl: (x: key_t) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (x: key_t)
: Tot (SB.parser asn1_weak_parser_kind (refine_with_tag tag x))
= pl x

let disp_p
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (l: nat)
: Tot (SB.parser (disp_kind l) data_t)
= SCo.parse_tagged_union #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata (asn1_terminal_as_parser key_k) l) tag #asn1_weak_parser_kind (pl_spec tag pl)

let fldata_eq (#k: parser_kind) (#t: Type) (p: SB.parser k t) (l: nat) (b: bytes)
: Lemma (SB.parse (SFL.parse_fldata p l) b == (
    if Seq.length b < l
    then None
    else match SB.parse p (Seq.slice b 0 l) with
    | Some (v, c) -> if c = l then Some (v, l) else None
    | None -> None
  ))
= ()

let disp_short
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (l: nat)
  (b: bytes)
: Lemma
  (requires (Seq.length b < l))
  (ensures (consumed (disp_p key_k tag pl l) b == None))
= SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata (asn1_terminal_as_parser key_k) l) tag #asn1_weak_parser_kind (pl_spec tag pl) b;
  fldata_eq #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) l b

#push-options "--z3rlimit 128 --ifuel 2"

#restart-solver

let adb_eq
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (b: bytes)
: Lemma (consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl) b == (
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id', c1) ->
      if id' = kid
      then
        let b1 = Seq.slice b c1 (Seq.length b) in
        match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) b1 with
        | None -> None
        | Some (len, c2) ->
          match consumed (disp_p key_k tag pl (U32.v len)) (Seq.slice b1 c2 (Seq.length b1)) with
          | None -> None
          | Some c3 -> Some (c1 + (c2 + c3))
      else None
  ))
= let p = asn1_terminal_as_parser key_k in
  T.parse_tagged_union_eq (key_p kid key_k) tag pl b;
  ILC.ilc_eq kid #(ASN1_TERMINAL key_k) p b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id', c1) ->
    if id' = kid
    then begin
      let b1 = Seq.slice b c1 (Seq.length b) in
      ILC.lc_eq p b1;
      SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) #asn1_weak_parser_kind #(asn1_terminal_t key_k) p b1;
      match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) b1 with
      | None -> ()
      | Some (len, c2) ->
        let b2 = Seq.slice b1 c2 (Seq.length b1) in
        let l = U32.v len in
        SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) tag #asn1_weak_parser_kind (pl_spec tag pl) b2;
        fldata_eq #asn1_weak_parser_kind p l b2;
        if Seq.length b2 < l
        then ()
        else begin
          Seq.slice_slice b1 c2 (Seq.length b1) 0 l;
          Seq.slice_slice b c1 (Seq.length b) c2 (c2 + l);
          Seq.slice_slice b1 c2 (Seq.length b1) l (Seq.length b2);
          Seq.slice_slice b c1 (Seq.length b) (c2 + l) (Seq.length b1)
        end
    end
    else ()

#pop-options

#push-options "--ifuel 2"
private
let vpc_some (#k: parser_kind) (#t: Type) (p: SB.parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) (x: t)
: Lemma (requires (vreader_postcond p offset v off (Some x)))
  (ensures (SZ.v offset <= SZ.v off /\ SZ.v off <= Seq.length v /\
    SB.parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (x, SZ.v off - SZ.v offset)))
= ()
#pop-options

private
let vpost_consumed (#k: parser_kind) (#t: Type) (p: SB.parser k t) (offset: SZ.t) (v: bytes) (off: SZ.t) (res: bool)
: Lemma (LPS.validator_postcond p offset v off res <==> (
    SZ.v offset <= Seq.length v /\ SZ.v off <= Seq.length v /\
    (if res
     then SZ.v offset <= SZ.v off /\ consumed p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (SZ.v off - SZ.v offset)
     else consumed p (Seq.slice v (SZ.v offset) (Seq.length v)) == None)))
= ()

private
let slice_tail2 (w: bytes) (c1: nat) (c2: nat)
: Lemma (requires (c1 <= Seq.length w /\ c2 <= Seq.length w - c1))
  (ensures (Seq.slice (Seq.slice w c1 (Seq.length w)) c2 (Seq.length w - c1) == Seq.slice w (c1 + c2) (Seq.length w)))
= Seq.slice_slice w c1 (Seq.length w) c2 (Seq.length w - c1)

#push-options "--fuel 0 --ifuel 1"
private
let adb_consumed_at
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (v: bytes)
  (offset off1 off2: SZ.t)
  (len: LowParse.Spec.BoundedInt.bounded_int32 0 ILC.asn1_length_max)
: Lemma
  (requires (
    vreader_postcond #asn1_strong_parser_kind parse_asn1_identifier_U32 offset v off1 (Some kid) /\
    vreader_postcond #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 v off2 (Some len)))
  (ensures (SZ.v offset <= SZ.v off2 /\ SZ.v off2 <= Seq.length v /\
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl) (Seq.slice v (SZ.v offset) (Seq.length v)) == (
      match consumed (disp_p key_k tag pl (U32.v len)) (Seq.slice v (SZ.v off2) (Seq.length v)) with
      | None -> None
      | Some c3 -> Some ((SZ.v off1 - SZ.v offset) + ((SZ.v off2 - SZ.v off1) + c3)))))
= vpc_some #asn1_strong_parser_kind parse_asn1_identifier_U32 offset v off1 kid;
  vpc_some #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 v off2 len;
  let b = Seq.slice v (SZ.v offset) (Seq.length v) in
  let c1 = SZ.v off1 - SZ.v offset in
  let c2 = SZ.v off2 - SZ.v off1 in
  slice_tail2 v (SZ.v offset) c1;
  slice_tail2 v (SZ.v off1) c2;
  adb_eq kid key_k tag pl b
#pop-options

#push-options "--fuel 0 --ifuel 1"

let validate_adb_short
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (v: bytes)
  (offset off1 off2: SZ.t)
  (len: LowParse.Spec.BoundedInt.bounded_int32 0 ILC.asn1_length_max)
: Lemma
  (requires (
    vreader_postcond #asn1_strong_parser_kind parse_asn1_identifier_U32 offset v off1 (Some kid) /\
    vreader_postcond #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 v off2 (Some len) /\
    U32.v len > Seq.length v - SZ.v off2))
  (ensures (LPS.validator_postcond #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl) offset v off2 false))
= adb_consumed_at kid key_k tag pl v offset off1 off2 len;
  disp_short key_k tag pl (U32.v len) (Seq.slice v (SZ.v off2) (Seq.length v));
  vpost_consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl) offset v off2 false

let validate_adb_long
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (v: bytes)
  (offset off1 off2 off3: SZ.t)
  (len: LowParse.Spec.BoundedInt.bounded_int32 0 ILC.asn1_length_max)
  (res: bool)
: Lemma
  (requires (
    vreader_postcond #asn1_strong_parser_kind parse_asn1_identifier_U32 offset v off1 (Some kid) /\
    vreader_postcond #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) off1 v off2 (Some len) /\
    LPS.validator_postcond #(disp_kind (U32.v len)) (disp_p key_k tag pl (U32.v len)) off2 v off3 res))
  (ensures (LPS.validator_postcond #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl) offset v off3 res))
= adb_consumed_at kid key_k tag pl v offset off1 off2 len;
  vpost_consumed #(disp_kind (U32.v len)) (disp_p key_k tag pl (U32.v len)) off2 v off3 res;
  vpost_consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl) offset v off3 res

#pop-options

#push-options "--z3rlimit 64 --ifuel 2"

inline_for_extraction
fn validate_adb
  (kid: asn1_id_t)
  (key_k: Ghost.erased asn1_terminal_k)
  (#data_t: Type0)
  (tag: Ghost.erased (data_t -> Tot (asn1_terminal_t key_k)))
  (pl: Ghost.erased ((x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x))))
  (vd: (l: SZ.t) -> LPS.validator #data_t #(disp_kind (SZ.v l)) (disp_p key_k tag pl (SZ.v l)))
: LPS.validator #data_t #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) tag pl)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  adb_eq kid key_k tag pl (Seq.slice v (SZ.v offset) (Seq.length v));
  let r = I.vread_identifier input poffset;
  match r {
    None -> { false }
    Some id' -> {
      if (ILC.asn1_id_eq id' kid) {
        with off1 . assert (R.pts_to poffset off1);
        Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
        let ol = ILC.vread_length input poffset;
        match ol {
          None -> { false }
          Some len -> {
            with off2 . assert (R.pts_to poffset off2);
            Seq.slice_slice v (SZ.v off1) (Seq.length v) (SZ.v off2 - SZ.v off1) (Seq.length v - SZ.v off1);
            let off = !poffset;
            let rem = SZ.sub (S.len input) off;
            if (LowParse.Pulse.SizeComparison.u32_lte_sizet len rem) {
              SZ.fits_lte (U32.v len) (SZ.v rem);
              let res = vd (SZ.uint32_to_sizet len) input poffset;
              with off3 . assert (R.pts_to poffset off3);
              validate_adb_long kid key_k tag pl v offset off1 off2 off3 len res;
              res
            } else {
              validate_adb_short kid key_k tag pl v offset off1 off2 len;
              false
            }
          }
        }
      } else {
        false
      }
    }
  }
}

#pop-options

(* Dispatch tables without fallback *)

let choice_disp_p
  (key_k: asn1_terminal_k)
  (lc: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind))
  (l: nat)
: Tot (SB.parser (disp_kind l) (make_gen_choice_type (extract_types lc)))
= disp_p key_k (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc) l

let choice_disp_nil (key_k: asn1_terminal_k) (l: nat) (b: bytes)
: Lemma (None? (SB.parse (choice_disp_p key_k [] l) b))
= let lc : list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind) = [] in
  SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata (asn1_terminal_as_parser key_k) l) (tag_of_gen_choice_type (extract_types lc)) #asn1_weak_parser_kind (pl_spec (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc)) b

let parse_synth_consumed
  (#k: parser_kind) (#t1: Type) (#t2: Type) (p1: parser k t1) (f2: t1 -> Tot t2) (b: bytes)
: Lemma
  (requires (k.parser_kind_injective ==> synth_injective f2))
  (ensures (consumed #k (T.parse_synth p1 f2) b == consumed #k p1 b))
  [SMTPat (SB.parse (T.parse_synth p1 f2) b)]
= T.parse_synth_eq p1 f2 b

let key_eq_fldata (key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (l: nat) =
  SFL.parse_fldata #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (key_eq x)) l

(* For keys other than OBJECT IDENTIFIER: the filter on the key value, in
   a fixed-length data, accepts exactly its DER content encoding *)

#push-options "--z3rlimit 64 --ifuel 2"

let key_lit_fldata_consumed (key_k: ASN1.Spec.Content.Enc.leaf_k) (x: asn1_terminal_t key_k) (e: list U8.t) (l: nat) (b: bytes)
: Lemma
  (requires (Seq.seq_of_list e == ASN1.Spec.Content.Enc.leaf_enc key_k x))
  (ensures (consumed (key_eq_fldata key_k x l) b == consumed (SFL.parse_fldata (bytes_eq_p e) l) b))
= let p = asn1_terminal_as_parser key_k in
  fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (key_eq x)) l b;
  fldata_eq (bytes_eq_p e) l b;
  if Seq.length b < l
  then ()
  else begin
    let s = Seq.slice b 0 l in
    SCo.parse_filter_eq #asn1_weak_parser_kind p (key_eq x) s;
    bytes_eq_consumed e s;
    ASN1.Spec.Content.Enc.leaf_enc_consumed key_k s;
    ASN1.Spec.Content.Enc.parse_leaf_enc key_k x;
    Seq.lemma_eq_elim (Seq.slice s 0 l) s
  end

#pop-options

#push-options "--z3rlimit 128 --ifuel 2"

#restart-solver

let choice_disp_cons
  (key_k: asn1_terminal_k)
  (x0: asn1_terminal_t key_k)
  (gp: gen_parser asn1_weak_parser_kind)
  (tl: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind))
  (l: nat)
  (b: bytes)
: Lemma (consumed (choice_disp_p key_k ((x0, gp) :: tl) l) b == (
    if Some? (consumed (key_eq_fldata key_k x0 l) b)
    then then_consumed (key_eq_fldata key_k x0 l) #asn1_weak_parser_kind (Mkgenparser?.p gp) b
    else consumed (choice_disp_p key_k tl l) b
  ))
= let p = asn1_terminal_as_parser key_k in
  let lc = (x0, gp) :: tl in
  SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) (tag_of_gen_choice_type (extract_types lc)) #asn1_weak_parser_kind (pl_spec (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc)) b;
  SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) (tag_of_gen_choice_type (extract_types tl)) #asn1_weak_parser_kind (pl_spec (tag_of_gen_choice_type (extract_types tl)) (make_gen_choice_weak_payload_parser tl)) b;
  fldata_eq #asn1_weak_parser_kind p l b;
  fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter p (key_eq x0)) l b;
  if Seq.length b < l
  then ()
  else begin
    SCo.parse_filter_eq #asn1_weak_parser_kind p (key_eq x0) (Seq.slice b 0 l);
    match SB.parse p (Seq.slice b 0 l) with
    | Some (x, c) ->
      if c = l
      then begin
        let b' = Seq.slice b l (Seq.length b) in
        if x = x0
        then T.parse_synth_eq (Mkgenparser?.p gp) (attach_tag lc x) b'
        else ()
      end
      else ()
    | None -> ()
  end

(* Dispatch tables with fallback *)

let choice_fb_disp_p
  (key_k: asn1_terminal_k)
  (lc: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind))
  (fb: gen_parser asn1_weak_parser_kind)
  (l: nat)
: Tot (SB.parser (disp_kind l) (make_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)))
= disp_p key_k (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb) l

let choice_fb_disp_nil (key_k: asn1_terminal_k) (fb: gen_parser asn1_weak_parser_kind) (l: nat) (b: bytes)
: Lemma (consumed (choice_fb_disp_p key_k [] fb l) b == then_consumed #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata (asn1_terminal_as_parser key_k) l) #asn1_weak_parser_kind (Mkgenparser?.p fb) b)
= let p = asn1_terminal_as_parser key_k in
  let lc : list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind) = [] in
  SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) #asn1_weak_parser_kind (pl_spec (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb)) b;
  match SB.parse (SFL.parse_fldata #asn1_weak_parser_kind p l) b with
  | Some (x, c) -> T.parse_synth_eq (Mkgenparser?.p fb) (attach_tag_with_fallback lc fb x) (Seq.slice b c (Seq.length b))
  | None -> ()

let choice_fb_disp_cons
  (key_k: asn1_terminal_k)
  (x0: asn1_terminal_t key_k)
  (gp: gen_parser asn1_weak_parser_kind)
  (tl: list (asn1_terminal_t key_k & gen_parser asn1_weak_parser_kind))
  (fb: gen_parser asn1_weak_parser_kind)
  (l: nat)
  (b: bytes)
: Lemma (consumed (choice_fb_disp_p key_k ((x0, gp) :: tl) fb l) b == (
    if Some? (consumed (key_eq_fldata key_k x0 l) b)
    then then_consumed (key_eq_fldata key_k x0 l) #asn1_weak_parser_kind (Mkgenparser?.p gp) b
    else consumed (choice_fb_disp_p key_k tl fb l) b
  ))
= let p = asn1_terminal_as_parser key_k in
  let lc = (x0, gp) :: tl in
  SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) #asn1_weak_parser_kind (pl_spec (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb)) b;
  SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) (tag_of_gen_choice_type_with_fallback (extract_types tl) (Mkgenparser?.t fb)) #asn1_weak_parser_kind (pl_spec (tag_of_gen_choice_type_with_fallback (extract_types tl) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser tl fb)) b;
  fldata_eq #asn1_weak_parser_kind p l b;
  fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter p (key_eq x0)) l b;
  if Seq.length b < l
  then ()
  else begin
    SCo.parse_filter_eq #asn1_weak_parser_kind p (key_eq x0) (Seq.slice b 0 l);
    match SB.parse p (Seq.slice b 0 l) with
    | Some (x, c) ->
      if c = l
      then begin
        let b' = Seq.slice b l (Seq.length b) in
        if x = x0
        then T.parse_synth_eq (Mkgenparser?.p gp) (attach_tag_with_fallback lc fb x) b'
        else ()
      end
      else ()
    | None -> ()
  end

#pop-options

(* The content parser of ANY DEFINED BY, with an empty prefix *)

let weaken_consumed (k: parser_kind) (#k': parser_kind) (#t: Type) (p: LowParse.Tot.Base.parser k' t) (b: bytes)
: Lemma
  (requires (k `is_weaker_than` k'))
  (ensures (consumed #k (LowParse.Tot.Base.weaken k p) b == consumed #k' p b))
  [SMTPat (consumed #k (LowParse.Tot.Base.weaken k p) b)]
= ()

[@@noextract_to "krml"]
noextract
let adb_k (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (ofb: option asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) []))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Tot asn1_content_k
= ASN1_ANY_DEFINED_BY [] ASN1_GEN_ITEMS_NIL kid key_k ls ofb pf pf'

#push-options "--z3rlimit 64"

let adb_content_none
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) []))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (b: bytes)
: Lemma
  (ensures (
    let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    consumed #asn1_weak_parser_kind (asn1_content_as_parser (adb_k kid key_k ls None pf pf')) b ==
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp)) b))
= assert (
    let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    consumed #asn1_weak_parser_kind (asn1_content_as_parser (adb_k kid key_k ls None pf pf')) b ==
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp)) b)
    by (FStar.Tactics.norm [delta_only [`%adb_k; `%asn1_content_as_parser; `%asn1_content_t; `%asn1_sequence_any_t_core; `%asn1_sequence_as_parser; `%make_asn1_sequence_any_parser; `%make_asn1_sequence_any_parser'; `%key_p; `%make_gen_choice_weak_parser; `%Mkparsertwin?.p]; zeta; iota; primops])

let adb_fb (fb: asn1_gen_items_lk) : Tot (gen_parser asn1_weak_parser_kind) =
  Mkgenparser _ (ASN1.Spec.Sequence.make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd fb)))

let adb_content_some
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) []))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (b: bytes)
: Lemma
  (ensures (
    let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    consumed #asn1_weak_parser_kind (asn1_content_as_parser (adb_k kid key_k ls (Some fb) pf pf')) b ==
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (adb_fb fb))) b))
= assert (
    let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    consumed #asn1_weak_parser_kind (asn1_content_as_parser (adb_k kid key_k ls (Some fb) pf pf')) b ==
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_p kid key_k) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (adb_fb fb))) b)
    by (FStar.Tactics.norm [delta_only [`%adb_k; `%asn1_content_as_parser; `%asn1_content_t; `%asn1_sequence_any_t_core; `%asn1_sequence_as_parser; `%make_asn1_sequence_any_parser; `%make_asn1_sequence_any_parser'; `%key_p; `%adb_fb; `%make_gen_choice_weak_parser; `%make_gen_choice_with_fallback_weak_parser; `%Mkparsertwin?.p]; zeta; iota; primops])

#pop-options

(* ANY DEFINED BY with a nonempty prefix: the suffix (key and dispatch) as
   a parser twin, as in the spec, and its validators, both when the key
   identifier has not been read yet and when the prefix has already read
   it. *)

let key_fp (kid: asn1_id_t) (key_k: asn1_terminal_k) (id: asn1_id_t) : Tot (asn1_strong_parser (asn1_terminal_t key_k)) =
  ASN1.Spec.ILC.parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k) id

#push-options "--z3rlimit 128 --ifuel 2"

#restart-solver

let adb_twin_eq
  (kid: asn1_id_t)
  (key_k: asn1_terminal_k)
  (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (id: asn1_id_t)
  (b: bytes)
: Lemma (consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_fp kid key_k id) tag pl) b == (
    if id = kid
    then
      match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) b with
      | None -> None
      | Some (len, c2) ->
        match consumed (disp_p key_k tag pl (U32.v len)) (Seq.slice b c2 (Seq.length b)) with
        | None -> None
        | Some c3 -> Some (c2 + c3)
    else None
  ))
= let p = asn1_terminal_as_parser key_k in
  T.parse_tagged_union_eq (key_fp kid key_k id) tag pl b;
  if id = kid
  then begin
    ILC.lc_eq p b;
    SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) #asn1_weak_parser_kind #(asn1_terminal_t key_k) p b;
    match SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) b with
    | None -> ()
    | Some (len, c2) ->
      let b2 = Seq.slice b c2 (Seq.length b) in
      let l = U32.v len in
      SCo.parse_tagged_union_eq #(SFL.parse_fldata_kind l asn1_weak_parser_kind) (SFL.parse_fldata p l) tag #asn1_weak_parser_kind (pl_spec tag pl) b2;
      fldata_eq #asn1_weak_parser_kind p l b2;
      if Seq.length b2 < l
      then ()
      else begin
        Seq.slice_slice b c2 (Seq.length b) 0 l;
        Seq.slice_slice b c2 (Seq.length b) l (Seq.length b2)
      end
  end
  else ()

#pop-options

#push-options "--z3rlimit 64"

inline_for_extraction
fn validate_adb_twin
  (kid: asn1_id_t)
  (key_k: Ghost.erased asn1_terminal_k)
  (#data_t: Type0)
  (tag: Ghost.erased (data_t -> Tot (asn1_terminal_t key_k)))
  (pl: Ghost.erased ((x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x))))
  (vd: (l: SZ.t) -> LPS.validator #data_t #(disp_kind (SZ.v l)) (disp_p key_k tag pl (SZ.v l)))
  (id: asn1_id_t)
: LPS.validator #data_t #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (key_fp kid key_k id) tag pl)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  adb_twin_eq kid key_k tag pl id (Seq.slice v (SZ.v offset) (Seq.length v));
  if (ILC.asn1_id_eq id kid) {
    let ol = ILC.vread_length input poffset;
    match ol {
      None -> { false }
      Some len -> {
        with off2 . assert (R.pts_to poffset off2);
        Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off2 - SZ.v offset) (Seq.length v - SZ.v offset);
        let off = !poffset;
        let rem = SZ.sub (S.len input) off;
        if (LowParse.Pulse.SizeComparison.u32_lte_sizet len rem) {
          SZ.fits_lte (U32.v len) (SZ.v rem);
          vd (SZ.uint32_to_sizet len) input poffset
        } else {
          disp_short key_k tag pl (U32.v len) (Seq.slice v (SZ.v off) (Seq.length v));
          false
        }
      }
    }
  } else {
    false
  }
}

#pop-options

let key_twin (kid: asn1_id_t) (key_k: asn1_terminal_k) : Tot (parser_twin asn1_strong_parser_kind (asn1_terminal_t key_k)) =
  let p = asn1_terminal_as_parser key_k in
  ASN1.Spec.ILC.parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) p;
  Mkparsertwin #asn1_strong_parser_kind #(asn1_terminal_t key_k) (key_p kid key_k) (key_fp kid key_k)

let adb_sfx_none (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Tot (parser_twin asn1_weak_parser_kind (make_gen_choice_type (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls))))
= let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  ASN1.Spec.ILC.parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k);
  make_gen_choice_weak_parser_twin_and_then_cases_injective (key_fp kid key_k) supported_p;
  Mkparsertwin
    (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser (key_p kid key_k) supported_p))
    (fun id -> weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin (key_fp kid key_k) supported_p id))

let adb_sfx_some (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk)
: Tot (parser_twin asn1_weak_parser_kind (make_gen_choice_type_with_fallback (extract_types (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls)) (Mkgenparser?.t (adb_fb fb))))
= let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  ASN1.Spec.ILC.parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) (asn1_terminal_as_parser key_k);
  make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective (key_fp kid key_k) supported_p (adb_fb fb);
  Mkparsertwin
    (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser (key_p kid key_k) supported_p (adb_fb fb)))
    (fun id -> weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin (key_fp kid key_k) supported_p (adb_fb fb) id))

[@@noextract_to "krml"]
noextract
let adb_prefix_k (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (ofb: option asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Tot asn1_content_k
= ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf'

#push-options "--z3rlimit 64"

let adb_prefix_content_none
  (ipd: id_decs) (prefix: asn1_gen_items_l ipd)
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (b: bytes)
: Lemma
  (ensures (
    consumed #asn1_weak_parser_kind (asn1_content_as_parser (adb_prefix_k ipd prefix kid key_k ls None pf pf')) b ==
    consumed #asn1_weak_parser_kind (ASN1.Pulse.SeqAny.seqa_p (asn1_sequence_as_parser prefix) (adb_sfx_none kid key_k ls) None) b))
= assert (
    asn1_content_as_parser (adb_prefix_k ipd prefix kid key_k ls None pf pf') ==
    make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_sfx_none kid key_k ls))
    by (FStar.Tactics.norm [delta_only [`%adb_prefix_k; `%asn1_content_as_parser; `%adb_sfx_none; `%adb_fb; `%key_p; `%key_fp; `%Mkparsertwin?.p; `%Mkparsertwin?.fp]; zeta; iota; primops]; FStar.Tactics.trefl ());
  assert (
    make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_sfx_none kid key_k ls) ==
    ASN1.Pulse.SeqAny.seqa_p (asn1_sequence_as_parser prefix) (adb_sfx_none kid key_k ls) None)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser; `%ASN1.Pulse.SeqAny.seqa_p]]; FStar.Tactics.trefl ())

let adb_prefix_content_some
  (ipd: id_decs) (prefix: asn1_gen_items_l ipd)
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (b: bytes)
: Lemma
  (ensures (
    consumed #asn1_weak_parser_kind (asn1_content_as_parser (adb_prefix_k ipd prefix kid key_k ls (Some fb) pf pf')) b ==
    consumed #asn1_weak_parser_kind (ASN1.Pulse.SeqAny.seqa_p (asn1_sequence_as_parser prefix) (adb_sfx_some kid key_k ls fb) None) b))
= assert (
    asn1_content_as_parser (adb_prefix_k ipd prefix kid key_k ls (Some fb) pf pf') ==
    make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_sfx_some kid key_k ls fb))
    by (FStar.Tactics.norm [delta_only [`%adb_prefix_k; `%asn1_content_as_parser; `%adb_sfx_some; `%adb_fb; `%key_p; `%key_fp; `%Mkparsertwin?.p; `%Mkparsertwin?.fp]; zeta; iota; primops]; FStar.Tactics.trefl ());
  assert (
    make_asn1_sequence_any_parser (asn1_sequence_as_parser prefix) (adb_sfx_some kid key_k ls fb) ==
    ASN1.Pulse.SeqAny.seqa_p (asn1_sequence_as_parser prefix) (adb_sfx_some kid key_k ls fb) None)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser; `%ASN1.Pulse.SeqAny.seqa_p]]; FStar.Tactics.trefl ())

(* The suffix twin, on consumed lengths *)

let adb_sfx_none_eq (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (st: option asn1_id_t) (b: bytes)
: Lemma (
    let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    consumed #asn1_weak_parser_kind (ASN1.Pulse.SeqAny.sfx_p (adb_sfx_none kid key_k ls) st) b ==
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (match st with None -> key_p kid key_k | Some id -> key_fp kid key_k id) (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp)) b)
= match st with
  | None -> ()
  | Some id -> ()

let adb_sfx_some_eq (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (st: option asn1_id_t) (b: bytes)
: Lemma (
    let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
    consumed #asn1_weak_parser_kind (ASN1.Pulse.SeqAny.sfx_p (adb_sfx_some kid key_k ls fb) st) b ==
    consumed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (T.parse_tagged_union (match st with None -> key_p kid key_k | Some id -> key_fp kid key_k id) (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (adb_fb fb))) b)
= match st with
  | None -> ()
  | Some id -> ()

#pop-options
