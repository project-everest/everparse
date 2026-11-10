module ASN1.Pulse.SeqAny
#lang-pulse
(* Validators for the sequence-then-suffix parser of the spec
   (`make_asn1_sequence_any_parser'`), used by ANY DEFINED BY with a
   nonempty prefix: the prefix items are validated as in a SEQUENCE, with
   the pending identifier as a runtime argument, then the suffix (the key
   and the dispatch on it) takes over, possibly with the identifier that the
   prefix has already read. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence
open ASN1.Spec.Any
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module T = LowParse.Tot.Combinators
module C = ASN1.Spec.Conformance

let seqa_p (items: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t)
: Tot (asn1_sequence_any_parser_type items t)
= make_asn1_sequence_any_parser' items sfx st

let seqa_body (items: list gen_decorated_parser_twin { Cons? items }) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t)
: Tot (asn1_sequence_any_parser_type items t)
= make_asn1_sequence_any_parser'' items sfx id

let sfx_p (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) : Tot (parser asn1_weak_parser_kind t) =
  match st with
  | Some id -> Mkparsertwin?.fp sfx id
  | None -> Mkparsertwin?.p sfx

(* Unfolding lemmas, on consumed lengths *)

let seqa_nil_eq (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (seqa_p [] sfx st) b == consumed #asn1_weak_parser_kind (sfx_p sfx st) b)
= C.any'_parse [] sfx st b

#push-options "--z3rlimit 32 --fuel 1 --ifuel 2"

let seqa_cons_eq (items: list gen_decorated_parser_twin { Cons? items }) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (seqa_p items sfx st) b == (
    match st with
    | Some id -> consumed #asn1_weak_parser_kind (seqa_body items sfx id) b
    | None ->
      match SB.parse parse_asn1_identifier_U32 b with
      | None -> None
      | Some (id, c1) ->
        match consumed #asn1_weak_parser_kind (seqa_body items sfx id) (Seq.slice b c1 (Seq.length b)) with
        | None -> None
        | Some c2 -> Some (c1 + c2)
  ))
= C.any'_parse items sfx st b;
  let pb = make_asn1_sequence_any_parser'' items sfx in
  T.and_then_eq (C.any_guard_p st) pb b;
  match st with
  | Some id -> Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b))
  | None -> ()

let seqa_body_eq (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (seqa_body (hd :: tl) sfx id) b == (
    if Set.mem id (item_set hd)
    then match consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b with
      | None -> None
      | Some c1 ->
        match consumed #asn1_weak_parser_kind (seqa_p tl sfx None) (Seq.slice b c1 (Seq.length b)) with
        | None -> None
        | Some c2 -> Some (c1 + c2)
    else if PLAIN? (item_dec hd)
    then None
    else consumed #asn1_weak_parser_kind (seqa_p tl sfx (Some id)) b
  ))
= C.any''_parse (hd :: tl) sfx id b;
  match hd with
  | Mkgendcparser d p fp ->
    let (| s, de, dk |) = d in
    if Set.mem id s
    then T.nondep_then_eq (parse_asn1_sequence_item_twin hd id) (make_asn1_sequence_any_parser' tl sfx None) b
    else match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      T.nondep_then_eq (weaken asn1_strong_parser_kind (T.parse_ret defv)) (make_asn1_sequence_any_parser' tl sfx (Some id)) b

#pop-options

(* Validators *)

inline_for_extraction
fn validate_seqa_nil
  (#t: Type0)
  (sfx: Ghost.erased (parser_twin asn1_weak_parser_kind t))
  (vp: LPS.validator #t #asn1_weak_parser_kind (Mkparsertwin?.p sfx))
  (vfp: (id: asn1_id_t) -> LPS.validator #t #asn1_weak_parser_kind (Mkparsertwin?.fp sfx id))
  (st: option asn1_id_t)
: LPS.validator #_ #asn1_weak_parser_kind (seqa_p [] sfx st)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  seqa_nil_eq sfx st (Seq.slice v (SZ.v offset) (Seq.length v));
  match st {
    None -> {
      vp input poffset
    }
    Some id -> {
      vfp id input poffset
    }
  }
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_seqa_cons
  (#t: Type0)
  (items: Ghost.erased (list gen_decorated_parser_twin) { Cons? items })
  (sfx: Ghost.erased (parser_twin asn1_weak_parser_kind t))
  (vbody: (id: asn1_id_t) -> LPS.validator #_ #asn1_weak_parser_kind (seqa_body items sfx id))
  (st: option asn1_id_t)
: LPS.validator #_ #asn1_weak_parser_kind (seqa_p items sfx st)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  seqa_cons_eq items sfx st (Seq.slice v (SZ.v offset) (Seq.length v));
  pts_to_len input;
  let r = get_pending_id st input poffset;
  match r {
    None -> {
      false
    }
    Some id -> {
      with off1 . assert (R.pts_to poffset off1);
      Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
      vbody id input poffset
    }
  }
}

inline_for_extraction
fn validate_seqa_body
  (#t: Type0)
  (hd: Ghost.erased gen_decorated_parser_twin)
  (tl: Ghost.erased (list gen_decorated_parser_twin))
  (sfx: Ghost.erased (parser_twin asn1_weak_parser_kind t))
  (id: asn1_id_t)
  (mem: bool { mem == Set.mem id (item_set hd) })
  (plain: bool { plain == PLAIN? (item_dec hd) })
  (vt: LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id))
  (vtail: (st: option asn1_id_t) -> LPS.validator #_ #asn1_weak_parser_kind (seqa_p tl sfx st))
: LPS.validator #_ #asn1_weak_parser_kind (seqa_body (Ghost.reveal hd :: Ghost.reveal tl) sfx id)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  seqa_body_eq hd tl sfx id (Seq.slice v (SZ.v offset) (Seq.length v));
  let r = validate_seq_item_step hd id mem plain vt input poffset;
  match r {
    None -> {
      false
    }
    Some st -> {
      with off1 . assert (R.pts_to poffset off1);
      Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
      vtail st input poffset
    }
  }
}

#pop-options
