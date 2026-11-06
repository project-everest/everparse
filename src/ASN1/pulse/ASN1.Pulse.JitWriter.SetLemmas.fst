module ASN1.Pulse.JitWriter.SetLemmas

(* Lemmas for the exact JIT writers of SET components
   (ASN1.Pulse.JitWriter): converses of the SET lemmas of
   ASN1.Pulse.JitWriter.Lemmas, from the well-formedness of the tags
   (`asn1_set_k_wf`) instead of runtime checks on what was written. The raw
   bytes of a component other than ANY are either empty or one TLV with one
   of its identifiers (`piece`), and those of several components, each
   inserted at its sorted position, are a sequence of such TLVs (`frs`). *)

open LowParse.Tot.Base
open LowParse.Tot.List
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Spec.Interpreter
open ASN1.Pulse.JitWriter.Lemmas

module SB = LowParse.Spec.Base
module Sq = ASN1.Pulse.Sequence
module PSL = ASN1.Pulse.ParseSequence.Lemmas
module SI = ASN1.Pulse.SortedInsert
module PSet = ASN1.Pulse.ParseSet.Lemmas
module FSet = FStar.Set
module TC = LowParse.Tot.Combinators
module SL = ASN1.Pulse.JitWriter.SeqLemmas
module C = ASN1.Spec.Conformance
module SC = ASN1.Pulse.SetComp
module In = ASN1.Pulse.Interpreter

let piece (s: FSet.set asn1_id_t) (p: bytes) : prop =
  tlvish p /\ (match SI.parse_id p with Some id -> FSet.mem id s | None -> False)

let rec frs (s: FSet.set asn1_id_t) (r: bytes) : Tot prop (decreases (Seq.length r)) =
  Seq.length r == 0 \/
  (exists (n: pos { n <= Seq.length r }) . piece s (Seq.slice r 0 n) /\ frs s (Seq.slice r n (Seq.length r)))

let piece_fl (s: FSet.set asn1_id_t) (p x: bytes)
: Lemma (requires (piece s p))
  (ensures (Seq.length p > 0 /\
    (SI.frame_len (Seq.append p x) == Seq.length p \/ SI.frame_len (Seq.append p x) == 0) /\
    SI.parse_id (Seq.append p x) == SI.parse_id p))
= tlvish_ext p x;
  frame_len_tlv_size (Seq.append p x);
  SL.append_prefix p x;
  ident_prefix p (Seq.append p x)

let piece_sub (s1 s2: FSet.set asn1_id_t) (p: bytes)
: Lemma (requires (piece s1 p /\ FSet.subset s1 s2)) (ensures (piece s2 p))
= ()

let frs_nil (s: FSet.set asn1_id_t) (r: bytes)
: Lemma (requires (Seq.length r == 0)) (ensures (frs s r))
= ()

#push-options "--fuel 1 --ifuel 1"
let frs_cons (s: FSet.set asn1_id_t) (p r: bytes)
: Lemma (requires (piece s p /\ frs s r)) (ensures (frs s (Seq.append p r)))
= piece_fl s p r;
  let b = Seq.append p r in
  let n : (n: pos { n <= Seq.length b }) = Seq.length p in
  Seq.append_slices p r;
  assert (piece s (Seq.slice b 0 n) /\ frs s (Seq.slice b n (Seq.length b)))

let frs_wit (s: FSet.set asn1_id_t) (r: bytes)
: Ghost (n: pos { n <= Seq.length r }) (requires (frs s r /\ Seq.length r > 0))
  (ensures (fun n -> piece s (Seq.slice r 0 n) /\ frs s (Seq.slice r n (Seq.length r))))
= FStar.IndefiniteDescription.indefinite_description_ghost (n: pos { n <= Seq.length r })
    (fun n -> piece s (Seq.slice r 0 n) /\ frs s (Seq.slice r n (Seq.length r)))

let frs_inv (s: FSet.set asn1_id_t) (r: bytes)
: Lemma (requires (frs s r /\ Seq.length r > 0))
  (ensures (
    (match SI.parse_id r with Some id -> FSet.mem id s | None -> False) /\
    (let n = SI.frame_len r in
     n == 0 \/ (n > 0 /\ n <= Seq.length r /\ piece s (Seq.slice r 0 n) /\ frs s (Seq.slice r n (Seq.length r))))))
= let n = frs_wit s r in
  Seq.lemma_split r n;
  piece_fl s (Seq.slice r 0 n) (Seq.slice r n (Seq.length r))

let rec frs_sub (s1 s2: FSet.set asn1_id_t) (r: bytes)
: Lemma (requires (frs s1 r /\ FSet.subset s1 s2)) (ensures (frs s2 r)) (decreases (Seq.length r))
= if Seq.length r = 0 then ()
  else begin
    let n = frs_wit s1 r in
    frs_sub s1 s2 (Seq.slice r n (Seq.length r));
    Seq.lemma_split r n;
    frs_cons s2 (Seq.slice r 0 n) (Seq.slice r n (Seq.length r))
  end

let rec frs_ins (s: FSet.set asn1_id_t) (p r: bytes)
: Lemma (requires ((Seq.length p == 0 \/ piece s p) /\ frs s r)) (ensures (frs s (SI.ins SI.lt_tag p r)))
  (decreases (Seq.length r))
= SI.ins_unfold SI.lt_tag p r;
  if Seq.length p = 0 then begin
    assert (Seq.equal p Seq.empty);
    ins_empty r
  end else if Seq.length r = 0 then begin
    assert (Seq.equal r Seq.empty);
    ins_empty_r p;
    assert (Seq.equal (Seq.slice p 0 (Seq.length p)) p);
    assert (Seq.equal (Seq.slice p (Seq.length p) (Seq.length p)) Seq.empty);
    frs_cons s p r;
    assert (Seq.equal (Seq.append p r) p)
  end else begin
    frs_inv s r;
    let n = SI.frame_len r in
    if n = 0 || not (SI.lt_tag (Seq.slice r 0 n) p) then frs_cons s p r
    else begin
      let r' = Seq.slice r n (Seq.length r) in
      frs_ins s p r';
      frs_cons s (Seq.slice r 0 n) (SI.ins SI.lt_tag p r')
    end
  end

(* The bytes of the elements of a SET are such a sequence *)

let rec fl_frs (its: list gen_decorated_parser_twin) (r: bytes) (l: list (set_elem_t its))
: Lemma (requires (fl its r l /\ C.items_tagged its)) (ensures (frs (PSet.items_set its) r)) (decreases l)
= match l with
  | [] -> ()
  | e :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    tag_frame its f e;
    assert (Seq.equal (Seq.slice f 0 n) (Seq.slice r 0 n));
    frame_prefix r f n;
    frame_len_tlv_size f;
    fl_frs its r' q;
    Seq.lemma_split r n;
    frs_cons (PSet.items_set its) f r'

let sacc_frs (its: list gen_decorated_parser_twin) (r: bytes)
: Lemma (requires (sacc its r /\ C.items_tagged its)) (ensures (frs (PSet.items_set its) r))
= eliminate exists (l: list (set_elem_t its)) . fl its r l /\ set_ok its l == true
  with fl_frs its r l
#pop-options

(* Parsing an element of the head component *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let set_elem_inl (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (b: bytes)
: Lemma (requires (match SB.parse parse_asn1_identifier_U32 b with Some (id, _) -> FSet.mem id (Sq.item_set hd) | None -> False))
  (ensures (match SB.parse (parse_set_elem (hd :: tl)) b, SB.parse parse_asn1_identifier_U32 b with
    | Some (e, n), Some (id, n1) -> Inl? (as_e hd tl e) /\ n1 <= n /\
      Sq.consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) (Seq.slice b n1 (Seq.length b)) == Some (n - n1 <: nat)
    | None, _ -> True
    | _ -> False))
= parse_set_elem_twin_cases_injective (hd :: tl);
  TC.and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t (hd :: tl)) (parse_set_elem_twin (hd :: tl)) b;
  let Some (id, n1) = SB.parse parse_asn1_identifier_U32 b in
  let b' = Seq.slice b n1 (Seq.length b) in
  TC.parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b'

let elem_inl_inv (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c: bytes)
: Lemma (requires ((match SB.parse parse_asn1_identifier_U32 c with Some (id, _) -> FSet.mem id (Sq.item_set hd) | None -> False) /\
    (match SB.parse (parse_set_elem (hd :: tl)) c with Some (_, n) -> (n <: nat) == Seq.length c | None -> False)))
  (ensures (iacc [hd] c))
= set_elem_inl hd tl c;
  ident_empty ();
  Sq.seq_cons_none [hd] c;
  let Some (id, n1) = SB.parse parse_asn1_identifier_U32 c in
  Sq.seq_single_some hd id (Seq.slice c n1 (Seq.length c))
#pop-options

(* An element of the tail components *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec fl_inr (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (r: bytes) (l: list (set_elem_t (hd :: tl)))
: Lemma (requires (set_cons_ok hd tl /\ frs (PSet.items_set tl) r /\ fl (hd :: tl) r l))
  (ensures (l == inr_l hd tl (tails (PSet.as_either hd tl l)) /\ fl tl r (tails (PSet.as_either hd tl l))))
  (decreases l)
= match l with
  | [] -> ()
  | e :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    frs_inv (PSet.items_set tl) r;
    let Some id = SI.parse_id f in
    assert (FSet.mem id (PSet.items_set tl));
    assert (asn1_same_tag id id);
    assert (~ (FSet.mem id (Sq.item_set hd)));
    set_elem_inr hd tl f;
    let Some (e2, _) = SB.parse (parse_set_elem tl) f in
    fl_inr hd tl r' q;
    assert (tails (PSet.as_either hd tl l) == e2 :: tails (PSet.as_either hd tl q))
#pop-options

(* Sortedness of a list with one element inserted *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec tags_sorted_lins_inv (#t: Type) (key: t -> Tot (option asn1_id_t)) (x: t) (l: list t)
: Lemma (requires (tags_sorted key (lins key x l) == true)) (ensures (tags_sorted key l == true))
= match l with
  | [] -> ()
  | y :: q ->
    if opt_tag_lt (key y) (key x) then begin
      tags_sorted_lins_inv key x q;
      lins_hd key x q;
      match q with
      | [] -> ()
      | z :: _ ->
        if opt_tag_lt (key y) (key z) then ()
        else begin
          let Some ky = key y in
          let Some kx = key x in
          let Some kz = key z in
          asn1_tag_lt_trans ky kx kz
        end
    end else ()
#pop-options

(* The elements of the SET, one of them inserted at its sorted position *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 128"
let rec fl_ins_inv (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c1 c2: bytes) (l: list (set_elem_t (hd :: tl)))
: Lemma (requires (set_cons_ok hd tl /\ piece (Sq.item_set hd) c1 /\ frs (PSet.items_set tl) c2 /\ fl (hd :: tl) (SI.ins SI.lt_tag c1 c2) l))
  (ensures (match SB.parse (parse_set_elem (hd :: tl)) c1 with
    | Some (x, n) -> (n <: nat) == Seq.length c1 /\ Inl? (as_e hd tl x) /\
      l == lins (elem_tag (hd :: tl)) x (inr_l hd tl (tails (PSet.as_either hd tl l))) /\
      fl tl c2 (tails (PSet.as_either hd tl l))
    | None -> False))
  (decreases (Seq.length c2))
= let its = hd :: tl in
  SI.ins_unfold SI.lt_tag c1 c2;
  let n2 = SI.frame_len c2 in
  SI.frame_len_le c2;
  piece_fl (Sq.item_set hd) c1 c2;
  let Some id1 = SI.parse_id c1 in
  if n2 = 0 || not (SI.lt_tag (Seq.slice c2 0 n2) c1) then begin
    let b = Seq.append c1 c2 in
    let n = Seq.length c1 in
    match l with
    | [] -> ()
    | x :: q ->
      assert (Seq.equal (Seq.slice b 0 n) c1);
      assert (Seq.equal (Seq.slice b n (Seq.length b)) c2);
      assert (pse_frame its c1 x);
      set_elem_inl hd tl c1;
      tag_frame its c1 x;
      fl_inr hd tl c2 q;
      match q with
      | [] -> ()
      | y :: _ ->
        tag_frame its (Seq.slice c2 0 n2) y
  end else begin
    let f2 = Seq.slice c2 0 n2 in
    let c2' = Seq.slice c2 n2 (Seq.length c2) in
    let i = SI.ins SI.lt_tag c1 c2' in
    let b = Seq.append f2 i in
    frs_inv (PSet.items_set tl) c2;
    SI.ins_length SI.lt_tag c1 c2';
    assert (Seq.equal (Seq.slice b 0 n2) (Seq.slice c2 0 n2));
    frame_prefix c2 b n2;
    match l with
    | [] -> ()
    | y :: q' ->
      assert (Seq.equal (Seq.slice b 0 n2) f2);
      assert (Seq.equal (Seq.slice b n2 (Seq.length b)) i);
      let Some id2 = SI.parse_id f2 in
      assert (asn1_same_tag id2 id2);
      set_elem_inr hd tl f2;
      let Some (y2, _) = SB.parse (parse_set_elem tl) f2 in
      tag_frame its f2 y;
      fl_ins_inv hd tl c1 c2' q';
      let Some (x, _) = SB.parse (parse_set_elem its) c1 in
      tag_frame its c1 x;
      assert (tails (PSet.as_either hd tl l) == y2 :: tails (PSet.as_either hd tl q'));
      assert (opt_tag_lt (elem_tag its y) (elem_tag its x))
  end
#pop-options

(* Main converse: if the SET is accepted, then so are the head component and
   the tail components *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let sacc_cons_inv (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c1 c2: bytes)
: Lemma (requires (set_cons_ok hd tl /\ (Seq.length c1 == 0 \/ piece (Sq.item_set hd) c1) /\ frs (PSet.items_set tl) c2 /\
    sacc (hd :: tl) (SI.ins SI.lt_tag c1 c2)))
  (ensures (iacc [hd] c1 /\ sacc tl c2))
= let its = hd :: tl in
  eliminate exists (l: list (set_elem_t its)) . fl its (SI.ins SI.lt_tag c1 c2) l /\ set_ok its l == true
  with begin
    if Seq.length c1 = 0 then begin
      assert (Seq.equal c1 Seq.empty);
      ins_empty c2;
      fl_inr hd tl c2 l;
      let l2 = tails (PSet.as_either hd tl l) in
      inr_l_props hd tl l2 (MK_ASN1_ID UNIVERSAL PRIMITIVE 0ul);
      iacc_single_empty hd;
      assert (fl tl c2 l2 /\ set_ok tl l2 == true)
    end else begin
      fl_ins_inv hd tl c1 c2 l;
      let Some (x, _) = SB.parse (parse_set_elem its) c1 in
      let l2 = tails (PSet.as_either hd tl l) in
      elem_inl_inv hd tl c1;
      tags_sorted_lins_inv (elem_tag its) x (inr_l hd tl l2);
      inr_l_props hd tl l2 (MK_ASN1_ID UNIVERSAL PRIMITIVE 0ul);
      lins_inr hd tl x l2;
      assert (fl tl c2 l2 /\ set_ok tl l2 == true)
    end
  end
#pop-options

(* Consequences used by the writers *)

let set_cons_frs (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c1 c2: bytes)
: Lemma (requires ((Seq.length c1 == 0 \/ piece (Sq.item_set hd) c1) /\ frs (PSet.items_set tl) c2))
  (ensures (frs (PSet.items_set (hd :: tl)) (SI.ins SI.lt_tag c1 c2)))
= let s = PSet.items_set (hd :: tl) in
  frs_sub (PSet.items_set tl) s c2;
  if Seq.length c1 = 0 then () else piece_sub (Sq.item_set hd) s c1;
  frs_ins s c1 c2

let set_cons_invalid1 (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c1 c2: bytes)
: Lemma (requires (set_cons_ok hd tl /\ (Seq.length c1 == 0 \/ piece (Sq.item_set hd) c1) /\ ~ (iacc [hd] c1) /\ sacc tl c2))
  (ensures (~ (sacc (hd :: tl) (SI.ins SI.lt_tag c1 c2)) /\ frs (PSet.items_set (hd :: tl)) (SI.ins SI.lt_tag c1 c2)))
= sacc_frs tl c2;
  Classical.move_requires (sacc_cons_inv hd tl c1) c2;
  set_cons_frs hd tl c1 c2

let set_cons_invalid2 (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c1 c2: bytes)
: Lemma (requires (set_cons_ok hd tl /\ (Seq.length c1 == 0 \/ piece (Sq.item_set hd) c1) /\ frs (PSet.items_set tl) c2 /\ ~ (sacc tl c2)))
  (ensures (~ (sacc (hd :: tl) (SI.ins SI.lt_tag c1 c2)) /\ frs (PSet.items_set (hd :: tl)) (SI.ins SI.lt_tag c1 c2)))
= Classical.move_requires (sacc_cons_inv hd tl c1) c2;
  set_cons_frs hd tl c1 c2

let set_single_inv (hd: gen_decorated_parser_twin) (c: bytes)
: Lemma (requires (set_cons_ok hd [] /\ (Seq.length c == 0 \/ piece (Sq.item_set hd) c) /\ ~ (iacc [hd] c)))
  (ensures (~ (sacc [hd] c) /\ frs (PSet.items_set [hd]) c))
= assert (frs (PSet.items_set []) Seq.empty);
  ins_empty_r c;
  Classical.move_requires (sacc_cons_inv hd [] c) Seq.empty;
  set_cons_frs hd [] c Seq.empty

(* A component other than ANY *)

let dfe_piece (hd: gen_decorated_parser_twin) (x: bytes)
: Lemma (requires (SL.dfe hd x)) (ensures (Seq.length x == 0 \/ piece (Sq.item_set hd) x))
= if Seq.length x = 0 then ()
  else begin
    framed_tlvish (Sq.item_set hd) x;
    framed_pid (Sq.item_set hd) x
  end

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let elt_of_iacc (hd: gen_decorated_parser_twin) (x: bytes)
: Lemma (requires (PSL.item_shaped hd /\ iacc [hd] x /\ SL.dfe hd x)) (ensures (elt_ok (Sq.item_set hd) x))
= if Seq.length x = 0 then ()
  else begin
    framed_pid (Sq.item_set hd) x;
    Sq.seq_cons_none [hd] x;
    let Some (id, n1) = SB.parse parse_asn1_identifier_U32 x in
    let x' = Seq.slice x n1 (Seq.length x) in
    Sq.seq_single_some hd id x';
    assert (match Sq.consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) x' with
      | Some n -> PSL.lc_size x' == Some n | None -> True);
    frame_len_tlv_size x
  end
#pop-options

(* Content-level converse: from the SET parser to the elements *)

let rec all_shaped (its: list gen_decorated_parser_twin) : prop =
  match its with
  | [] -> True
  | hd :: tl -> PSL.item_shaped hd /\ all_shaped tl

let rec all_shaped_twins (#i: _) (ls: asn1_gen_items_l i)
: Lemma (all_shaped (In.twins_of ls)) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> PSL.dec_shaped dk; all_shaped_twins tl

#push-options "--fuel 1 --ifuel 2 --z3rlimit 64"
let rec set_elem_twin_shaped (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma (requires (all_shaped its))
  (ensures (match Sq.consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) b with
    | Some n -> PSL.lc_size b == Some n
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    if FSet.mem id s then begin
      TC.parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b;
      assert (Sq.consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b == Sq.consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) b)
    end else begin
      TC.parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b;
      set_elem_twin_shaped tl id b
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec parse_fl (its: list gen_decorated_parser_twin) (r: bytes)
: Lemma (requires (C.items_tagged its /\ all_shaped its /\
    (match SB.parse (parse_list (parse_set_elem its)) r with Some (_, c) -> (c <: nat) == Seq.length r | None -> False)))
  (ensures (match SB.parse (parse_list (parse_set_elem its)) r with Some (l, _) -> fl its r l | None -> False))
  (decreases (Seq.length r))
= tot_parse_list_eq (parse_set_elem its) r;
  if Seq.length r = 0 then ()
  else begin
    let Some (e, n) = SB.parse (parse_set_elem its) r in
    SC.set_elem_eq its r;
    let Some (id, n1) = SB.parse parse_asn1_identifier_U32 r in
    set_elem_twin_shaped its id (Seq.slice r n1 (Seq.length r));
    frame_len_tlv_size r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    Seq.slice_slice r 0 n 0 n;
    SB.parse_strong_prefix #asn1_strong_parser_kind (parse_set_elem its) r f;
    assert (pse_frame its f e);
    assert (n > 0);
    let Some (_, c) = SB.parse (parse_list (parse_set_elem its)) r in
    assert (match SB.parse (parse_list (parse_set_elem its)) r' with
      | Some (_, c') -> (c <: nat) == n + c'
      | None -> False);
    parse_fl its r';
    let Some (l', _) = SB.parse (parse_list (parse_set_elem its)) r' in
    assert (fl its r (e :: l'))
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let acc_set_inv (ids: _) (items: asn1_gen_items_l ids) (pf: _) (b: bytes)
: Lemma (requires (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf)) b))
  (ensures (sacc (In.twins_of items) b))
= let its = In.twins_of items in
  set_to_tuple_injective its;
  TC.parse_synth_eq (parse_list (parse_set_elem its) `TC.parse_filter` set_ok its) (set_to_tuple its) b;
  TC.parse_filter_eq (parse_list (parse_set_elem its)) (set_ok its) b;
  C.items_tagged_intro items;
  all_shaped_twins items;
  parse_fl its b;
  let Some (l, _) = SB.parse (parse_list (parse_set_elem its)) b in
  assert (fl its b l /\ set_ok its l == true)
#pop-options
