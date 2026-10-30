module ASN1.Pulse.JitWriter.Lemmas

(* Lemmas for the just-in-time checked raw writers (ASN1.Pulse.JitWriter):
   a written chunk is "accepted" by a parser if the parser succeeds on it
   and consumes all of it. Acceptance of a TLV, a CHOICE, or a SEQUENCE
   follows from the acceptance of its parts and a few runtime checks on
   identifiers. *)

open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc

module SB = LowParse.Spec.Base
module U32 = FStar.UInt32
module Sq = ASN1.Pulse.Sequence
module Co = ASN1.Pulse.Constructed
module PSL = ASN1.Pulse.ParseSequence.Lemmas
module ILC = ASN1.Pulse.ILC
module C = ASN1.Spec.Conformance
module IE = ASN1.Spec.IdentifierU32.Enc
module In = ASN1.Pulse.Interpreter
module PS = ASN1.Pulse.ParseSequence

let acc (#k: parser_kind) (#t: Type) (p: SB.parser k t) (b: bytes) : prop =
  Sq.consumed p b == Some (Seq.length b)

let ident_empty (_: unit)
: Lemma (None? (parse parse_asn1_identifier_U32 Seq.empty))
= PSL.identifier_nonempty Seq.empty

(* The identifier at the start of `b`, and its size *)
let pid (b: bytes) : GTot (option (asn1_id_t & nat)) =
  match parse parse_asn1_identifier_U32 b with
  | None -> None
  | Some (id, c) -> Some (id, c)

let ident_prefix (b1 b2: bytes)
: Lemma
  (requires (Seq.length b1 <= Seq.length b2 /\ Seq.slice b2 0 (Seq.length b1) == b1 /\ Some? (parse parse_asn1_identifier_U32 b1)))
  (ensures (pid b2 == pid b1))
= let Some (_, c) = parse parse_asn1_identifier_U32 b1 in
  Seq.slice_slice b2 0 (Seq.length b1) 0 c;
  SB.parse_strong_prefix #asn1_strong_parser_kind parse_asn1_identifier_U32 b1 b2

let strong_prefix (#t: Type) (p: SB.parser asn1_strong_parser_kind t) (b1 b2: bytes)
: Lemma
  (requires (Seq.length b1 <= Seq.length b2 /\ Seq.slice b2 0 (Seq.length b1) == b1 /\ Some? (Sq.consumed p b1)))
  (ensures (Sq.consumed p b2 == Sq.consumed p b1))
= let Some (_, c) = SB.parse p b1 in
  Seq.slice_slice b2 0 (Seq.length b1) 0 c;
  SB.parse_strong_prefix p b1 b2

(* TLV *)

#push-options "--z3rlimit 64"
let acc_tlv (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (c: bytes)
: Lemma
  (requires (acc #asn1_weak_parser_kind p c /\ Seq.length c < 4294967296))
  (ensures (acc #asn1_strong_parser_kind (parse_asn1_ILC id p) (enc_tlv id true c)))
= let n = U32.uint_to_t (Seq.length c) in
  let e = enc_len n in
  let rest = e `Seq.append` c in
  let b = enc_tlv id true c in
  assert (b == IE.asn1_id_enc id `Seq.append` rest);
  IE.parse_asn1_identifier_U32_enc id rest;
  ILC.ilc_eq id p b;
  let c1 = Seq.length (IE.asn1_id_enc id) in
  assert (Seq.equal (Seq.slice b c1 (Seq.length b)) rest);
  parse_enc_len n c;
  C.vlgen_eq p rest;
  assert (Seq.equal (Seq.slice rest (Seq.length e) (Seq.length e + Seq.length c)) c)
#pop-options

(* CHOICE *)

let lacc (lc: list (asn1_id_t & asn1_content_k)) (b: bytes) : prop =
  match parse parse_asn1_identifier_U32 b with
  | None -> False
  | Some (id, c1) -> acc #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) (Seq.slice b c1 (Seq.length b))

let lacc_choice (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (b: bytes)
: Lemma (requires (lacc lc b)) (ensures (acc #asn1_strong_parser_kind (asn1_as_parser (ASN1_CHOICE_ILC lc pf)) b))
= PSL.k_id_then (ASN1_CHOICE_ILC lc pf) b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  Co.asn1_choice_twin_consumed lc pf id (Seq.slice b c1 (Seq.length b))

let lacc_hd (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (parse_asn1_ILC id' (asn1_content_as_parser c)) b)) (ensures (lacc ((id', c) :: tl) b))
= ILC.ilc_eq id' (asn1_content_as_parser c) b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  Co.asn1_choice_payload_cons id' c tl id (Seq.slice b c1 (Seq.length b))

let rec payload_mem (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Some? (Sq.consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) b)))
  (ensures (List.Tot.mem id (List.Tot.map fst lc)))
  (decreases lc)
= match lc with
  | [] -> Co.choice_payload_nil id b
  | (id', c) :: tl ->
    Co.asn1_choice_payload_cons id' c tl id b;
    if id = id' then () else payload_mem tl id b

let lacc_tl (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma
  (requires (lacc tl b /\ List.Tot.noRepeats (List.Tot.map fst ((id', c) :: tl))))
  (ensures (lacc ((id', c) :: tl) b))
= let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  let b1 = Seq.slice b c1 (Seq.length b) in
  payload_mem tl id b1;
  Co.asn1_choice_payload_cons id' c tl id b1

(* Sequence items *)

let iacc (l: list gen_decorated_parser_twin) (b: bytes) : prop =
  acc #asn1_weak_parser_kind (Sq.seq_p l None) b

let iacc_nil (_: unit) : Lemma (iacc [] Seq.empty) =
  Sq.seq_nil_none Seq.empty

let gdi_not_plain (hd: gen_decorated_parser_twin)
: Lemma (requires (Some? (generate_defaultable_item hd))) (ensures (~ (PLAIN? (Sq.item_dec hd))))
= match hd with
  | Mkgendcparser d _ _ ->
    let (| _, _, dk |) = d in
    match dk with
    | ASN1_PLAIN_ILC _ -> ()
    | _ -> ()

#push-options "--fuel 1 --ifuel 1"
let iacc_single_empty (hd: gen_decorated_parser_twin)
: Lemma (iacc [hd] Seq.empty <==> Some? (generate_defaultable_item hd))
= Sq.seq_cons_none [hd] Seq.empty;
  ident_empty ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
let twin_of_plain (#s: _) (k: asn1_k s)
: Lemma (Sq.item_dec (In.twin_of (ASN1_PLAIN_ILC k)) == PLAIN /\
    generate_defaultable_item (In.twin_of (ASN1_PLAIN_ILC k)) == None)
= ()

let twin_of_option (#s: _) (k: asn1_k s)
: Lemma (Sq.item_dec (In.twin_of (ASN1_OPTION_ILC k)) == OPTION /\
    Some? (generate_defaultable_item (In.twin_of (ASN1_OPTION_ILC k))))
= ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let iacc_plain (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (asn1_as_parser k) b)) (ensures (iacc [In.twin_of (ASN1_PLAIN_ILC k)] b))
= let hd = In.twin_of (ASN1_PLAIN_ILC k) in
  twin_of_plain k;
  PSL.k_id_then k b;
  Sq.seq_cons_none [hd] b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  let b1 = Seq.slice b c1 (Seq.length b) in
  Sq.seq_single_some hd id b1;
  assert (parse_asn1_sequence_item_twin hd id == snd (asn1_as_parser_twin k) id)

let iacc_option_some (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (asn1_as_parser k) b)) (ensures (iacc [In.twin_of (ASN1_OPTION_ILC k)] b))
= let hd = In.twin_of (ASN1_OPTION_ILC k) in
  twin_of_option k;
  PSL.k_id_then k b;
  PSL.identifier_nonempty b;
  Sq.seq_cons_none [hd] b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  let b1 = Seq.slice b c1 (Seq.length b) in
  Sq.seq_single_some hd id b1;
  assert (parse_asn1_sequence_item_twin hd id == (snd (asn1_as_parser_twin k) id `LowParse.Tot.Combinators.parse_synth` Some));
  LowParse.Tot.Combinators.parse_synth_eq (snd (asn1_as_parser_twin k) id) Some b1
#pop-options

let iacc_option_none (#s: _) (k: asn1_k s)
: Lemma (iacc [In.twin_of (ASN1_OPTION_ILC k)] Seq.empty)
= twin_of_option k;
  iacc_single_empty (In.twin_of (ASN1_OPTION_ILC k))

let iacc_default_none (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (requires (ASN1_DEFAULT_TERMINAL? dk \/ ASN1_DEFAULT_RESTRICTED_TERMINAL? dk)) (ensures (iacc [In.twin_of dk] Seq.empty))
= iacc_single_empty (In.twin_of dk)

#push-options "--fuel 2 --ifuel 1"
let twins_of_single (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (In.twins_of (PS.single dk) == [In.twin_of dk])
= ()

let twins_of_cons2 (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#s2: _) (#d2: _) (dk2: asn1_decorated_k s2 d2) (#ids2: _) (tl2: asn1_gen_items_l ids2)
: Lemma (In.twins_of (PS.cons2 dk dk2 tl2) == In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
= ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 128"
let iacc_cons
  (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (v: bytes) (p2 p1 p0: nat)
: Lemma
  (requires (p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v /\
    iacc [hd] (Seq.slice v p2 p1) /\ iacc tl (Seq.slice v p1 p0) /\
    (p2 < p1 ==> (match pid (Seq.slice v p2 (Seq.length v)) with
      | Some (id, _) -> Set.mem id (Sq.item_set hd)
      | None -> True)) /\
    ((p2 == p1 /\ p1 < p0) ==> (match pid (Seq.slice v p1 (Seq.length v)) with
      | Some (id, _) -> ~ (Set.mem id (Sq.item_set hd))
      | None -> True))))
  (ensures (iacc (hd :: tl) (Seq.slice v p2 p0)))
= let x = Seq.slice v p2 p0 in
  let xh = Seq.slice v p2 p1 in
  let xt = Seq.slice v p1 p0 in
  ident_empty ();
  Sq.seq_cons_none (hd :: tl) x;
  Sq.seq_cons_none [hd] xh;
  Sq.seq_cons_none tl xt;
  if p2 < p1
  then begin
    let Some (id, c1) = parse parse_asn1_identifier_U32 xh in
    let rh = Seq.slice xh c1 (Seq.length xh) in
    Sq.seq_single_some hd id rh;
    assert (Seq.equal (Seq.slice x 0 (Seq.length xh)) xh);
    ident_prefix xh x;
    let vr = Seq.slice v p2 (Seq.length v) in
    assert (Seq.equal (Seq.slice vr 0 (Seq.length xh)) xh);
    ident_prefix xh vr;
    let r = Seq.slice x c1 (Seq.length x) in
    assert (Seq.equal (Seq.slice r 0 (Seq.length rh)) rh);
    strong_prefix (parse_asn1_sequence_item_twin hd id) rh r;
    Sq.seq_cons_cons_some hd tl id r;
    assert (Seq.equal (Seq.slice r (Seq.length rh) (Seq.length r)) xt)
  end
  else if p1 < p0
  then begin
    assert (Seq.equal x xt);
    iacc_single_empty hd;
    gdi_not_plain hd;
    let Some (id, c1) = parse parse_asn1_identifier_U32 xt in
    let vr = Seq.slice v p1 (Seq.length v) in
    assert (Seq.equal (Seq.slice vr 0 (Seq.length xt)) xt);
    ident_prefix xt vr;
    Sq.seq_cons_cons_some hd tl id (Seq.slice x c1 (Seq.length x))
  end
  else begin
    iacc_single_empty hd;
    assert (Seq.equal xt Seq.empty);
    assert (Seq.equal x Seq.empty)
  end
#pop-options

(* Unfolding the interpreter *)

#push-options "--fuel 1 --ifuel 1"
let acc_k_ilc (id: asn1_id_t) (c: asn1_content_k) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser c)) b)) (ensures (acc #asn1_strong_parser_kind (asn1_as_parser (ASN1_ILC id c)) b))
= ()

let acc_prefixed (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (asn1_as_parser k) b)) (ensures (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_PREFIXED k)) b))
= ()

let acc_sequence (g: asn1_gen_items_lk) (b: bytes)
: Lemma (requires (iacc (In.twins_of (dsnd g)) b)) (ensures (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE g)) b))
= ()
#pop-options

#push-options "--fuel 2 --ifuel 1"
let supported_single (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (In.supported_dec dk))
: Tot (squash (In.supported_items (PS.single dk)))
= ()

let lc_tail_ok (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (u: squash (In.supported_lc (hd :: tl) /\ List.Tot.noRepeats (List.Tot.map fst (hd :: tl))))
: Tot (squash (In.supported_content (snd hd) /\ In.supported_lc tl /\ List.Tot.noRepeats (List.Tot.map fst tl)))
= ()
#pop-options

(* SEQUENCE OF and SET OF: each element is written and accepted on its
   own, and is nonempty; the elements of a SET OF are also checked to be
   frames, so that the insertion sort keeps them sorted *)

module W = LowParse.Pulse.R2L
module SI = ASN1.Pulse.SortedInsert
module Set = ASN1.Spec.Set
module RR = ASN1.Pulse.RawRel
module SDER = LowParse.Spec.DER

let eacc (#t: Type) (pp: asn1_strong_parser t) (b: bytes) : prop =
  acc #asn1_strong_parser_kind pp b /\ Seq.length b > 0

let rec all_eacc (#t: Type) (pp: asn1_strong_parser t) (l: list bytes) : prop =
  match l with
  | [] -> True
  | a :: q -> eacc pp a /\ all_eacc pp q

let rec all_eacc_snoc (#t: Type) (pp: asn1_strong_parser t) (l: list bytes) (y: bytes)
: Lemma (requires (all_eacc pp l /\ eacc pp y)) (ensures (all_eacc pp (List.Tot.append l [y])))
= match l with
  | [] -> ()
  | _ :: q -> all_eacc_snoc pp q y

let strong_ext (#k: parser_kind) (#t: Type) (p: SB.parser k t) (b x: bytes)
: Lemma (requires (k.parser_kind_subkind == Some SB.ParserStrong /\ Some? (SB.parse p b)))
  (ensures (match SB.parse p b, SB.parse p (Seq.append b x) with
    | Some (v1, c1), Some (v2, c2) -> v1 == v2 /\ (c1 <: nat) == c2
    | _ -> False))
= let Some (_, c) = SB.parse p b in
  assert (Seq.equal (Seq.slice (Seq.append b x) 0 c) (Seq.slice b 0 c));
  SB.parse_strong_prefix p b (Seq.append b x)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec list_parse (#t: Type) (pp: asn1_strong_parser t) (l: list bytes)
: Lemma (requires (all_eacc pp l))
  (ensures (match SB.parse (parse_list pp) (W.enc_list RR.id_enc l) with
    | Some (l', c) -> c == Seq.length (W.enc_list RR.id_enc l) /\ List.Tot.length l' == List.Tot.length l
    | None -> False))
= match l with
  | [] -> tot_parse_list_eq pp (W.enc_list RR.id_enc l)
  | a :: q ->
    list_parse pp q;
    let b = W.enc_list RR.id_enc l in
    let bq = W.enc_list RR.id_enc q in
    assert (b == Seq.append a bq);
    assert (Seq.equal (Seq.slice b (Seq.length a) (Seq.length b)) bq);
    strong_ext #asn1_strong_parser_kind pp a bq;
    tot_parse_list_eq pp b;
    let Some (v, n) = SB.parse pp b in
    assert (n == Seq.length a);
    let Some (lq, _) = SB.parse (parse_list pp) bq in
    assert (SB.parse (parse_list pp) (Seq.slice b n (Seq.length b)) == SB.parse (parse_list pp) bq);
    let Some (lb, _) = SB.parse (parse_list pp) b in
    assert (lb == v :: lq)
#pop-options

let acc_sized_list (ne: bool) (#t: Type) (pp: asn1_strong_parser t) (l: list bytes)
: Lemma (requires (all_eacc pp l /\ (ne == true ==> Seq.length (W.enc_list RR.id_enc l) > 0)))
  (ensures (acc #asn1_weak_parser_kind (parse_sized_list ne pp) (W.enc_list RR.id_enc l)))
= list_parse pp l;
  parse_filter_eq (parse_list pp) (list_size_ok ne) (W.enc_list RR.id_enc l)

let acc_seq_of (ne: bool) (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (acc #asn1_weak_parser_kind (parse_sized_list ne (asn1_as_parser k)) b))
  (ensures (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k)) b))
= ()

(* SET OF *)

let rec lex_total (n1: nat) (b1: Seq.lseq byte n1) (n2: nat) (b2: Seq.lseq byte n2)
: Lemma (ensures (Set.lex_byte_order' n1 b1 n2 b2 == true \/ Set.lex_byte_order' n2 b2 n1 b1 == true))
  (decreases (n1 + n2))
= if n1 = 0 || n2 = 0 then ()
  else
    let x1 = Seq.index b1 0 in
    let x2 = Seq.index b2 0 in
    if FStar.UInt8.lt x1 x2 || FStar.UInt8.lt x2 x1 then ()
    else lex_total (n1 - 1) (Seq.slice b1 1 n1) (n2 - 1) (Seq.slice b2 1 n2)

let frame_prefix (r1 r2: bytes) (n: nat)
: Lemma (requires (SI.frame_len r1 == n /\ n > 0 /\ n <= Seq.length r1 /\ n <= Seq.length r2 /\ Seq.slice r2 0 n == Seq.slice r1 0 n))
  (ensures (SI.frame_len r2 == n))
= let Some (_, n1) = SB.parse parse_asn1_identifier_U32 r1 in
  Seq.slice_slice r1 0 n 0 n1;
  Seq.slice_slice r2 0 n 0 n1;
  SB.parse_strong_prefix #asn1_strong_parser_kind parse_asn1_identifier_U32 r1 r2;
  let s1 = Seq.slice r1 n1 (Seq.length r1) in
  let s2 = Seq.slice r2 n1 (Seq.length r2) in
  let Some (_, n2) = SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) s1 in
  Seq.slice_slice r1 0 n n1 (n1 + n2);
  Seq.slice_slice r2 0 n n1 (n1 + n2);
  Seq.slice_slice r1 n1 (Seq.length r1) 0 n2;
  Seq.slice_slice r2 n1 (Seq.length r2) 0 n2;
  SB.parse_strong_prefix (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) s1 s2

(* The bytes `r` are a sequence of frames, each accepted by `pp`, sorted by
   encoding (the first one being greater than `prev`, if any) *)
let rec sf (#t: Type) (pp: asn1_strong_parser t) (prev: option bytes) (r: bytes)
: GTot prop (decreases (Seq.length r))
= if Seq.length r = 0 then True
  else
    let n = SI.frame_len r in
    if n = 0 then False
    else begin
      SI.frame_len_le r;
      let f = Seq.slice r 0 n in
      acc #asn1_strong_parser_kind pp f /\
      (match prev with None -> True | Some w -> Set.lex_byte_order w f == true) /\
      sf pp (Some f) (Seq.slice r n (Seq.length r))
    end

let prev_ok (prev: option bytes) (e: bytes) : prop =
  match prev with None -> True | Some w -> Set.lex_byte_order w e == true

let fresh_frame (#t: Type) (pp: asn1_strong_parser t) (e: bytes) : prop =
  acc #asn1_strong_parser_kind pp e /\ Seq.length e > 0 /\ SI.frame_len e == Seq.length e

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let sf_cons (#t: Type) (pp: asn1_strong_parser t) (prev: option bytes) (e r: bytes)
: Lemma (requires (fresh_frame pp e /\ prev_ok prev e /\ sf pp (Some e) r))
  (ensures (sf pp prev (Seq.append e r)))
= let b = Seq.append e r in
  assert (Seq.equal (Seq.slice b 0 (Seq.length e)) (Seq.slice e 0 (Seq.length e)));
  frame_prefix e b (Seq.length e);
  assert (Seq.equal (Seq.slice b 0 (Seq.length e)) e);
  assert (Seq.equal (Seq.slice b (Seq.length e) (Seq.length b)) r)

let sf_prev (#t: Type) (pp: asn1_strong_parser t) (prev: option bytes) (w: bytes) (r: bytes)
: Lemma (requires (sf pp prev r /\ (Seq.length r > 0 ==> (SI.frame_len_le r; Set.lex_byte_order w (Seq.slice r 0 (SI.frame_len r)) == true))))
  (ensures (sf pp (Some w) r))
= ()

let rec sf_ins (#t: Type) (pp: asn1_strong_parser t) (prev: option bytes) (e r: bytes)
: Lemma (requires (sf pp prev r /\ fresh_frame pp e /\ prev_ok prev e))
  (ensures (sf pp prev (SI.ins SI.lt_lex e r)))
  (decreases (Seq.length r))
= SI.ins_unfold SI.lt_lex e r;
  let n = SI.frame_len r in
  if n = 0 then begin
    assert (Seq.length r == 0);
    sf_cons pp prev e r
  end else begin
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    if SI.lt_lex f e then begin
      lex_total (Seq.length e) e (Seq.length f) f;
      sf_ins pp (Some f) e r';
      let i = SI.ins SI.lt_lex e r' in
      let b = Seq.append f i in
      assert (Seq.equal (Seq.slice b 0 n) (Seq.slice r 0 n));
      frame_prefix r b n;
      assert (Seq.equal (Seq.slice b 0 n) f);
      assert (Seq.equal (Seq.slice b n (Seq.length b)) i)
    end else begin
      sf_prev pp prev e r;
      sf_cons pp prev e r
    end
  end

let rec sf_aux (#t: Type) (tbo: bytes -> bytes -> bool) (pp: asn1_strong_parser t) (prev: bytes) (r: bytes)
: Lemma (requires (sf pp (Some prev) r /\ (forall x y . tbo x y == Set.lex_byte_order x y)))
  (ensures (match Set.tot_parse_byte_sorted_list_aux tbo pp prev r with
    | Some (_, c) -> c == Seq.length r
    | None -> False))
  (decreases (Seq.length r))
= if Seq.length r = 0 then ()
  else begin
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    assert (Seq.equal r (Seq.append f r'));
    strong_ext #asn1_strong_parser_kind pp f r';
    sf_aux tbo pp f r'
  end
#pop-options

let set_of_eq (#t: Type) (pp: asn1_strong_parser t) (r: bytes)
: Lemma (Sq.consumed #asn1_weak_parser_kind (Set.parse_asn1_set_of pp) r == Sq.consumed (Set.parse_byte_sorted_list (Set.prop_order_of_bool_order Set.lex_byte_order) #_ #asn1_strong_parser_kind pp) r /\
    Sq.consumed #asn1_weak_parser_kind (parse_sized_set true pp) r == (match SB.parse (Set.parse_asn1_set_of pp) r with Some (l, c) -> if Cons? l then Some (c <: nat) else None | None -> None) /\
    Sq.consumed #asn1_weak_parser_kind (parse_sized_set false pp) r == Sq.consumed #asn1_weak_parser_kind (Set.parse_asn1_set_of pp) r)
= let p' = Set.tot_parse_byte_sorted_list Set.lex_byte_order pp in
  assert (SB.parse p' r == SB.parse (Set.parse_byte_sorted_list (Set.prop_order_of_bool_order Set.lex_byte_order) #_ #asn1_strong_parser_kind pp) r);
  assert (SB.parse (Set.parse_asn1_set_of pp) r == SB.parse p' r);
  parse_filter_eq (Set.parse_asn1_set_of pp) (list_size_ok true) r;
  parse_filter_eq (Set.parse_asn1_set_of pp) (list_size_ok false) r

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"
let acc_sized_set (ne: bool) (#t: Type) (pp: asn1_strong_parser t) (r: bytes)
: Lemma (requires (sf pp None r /\ (ne == true ==> Seq.length r > 0)))
  (ensures (acc #asn1_weak_parser_kind (parse_sized_set ne pp) r))
= let tbo : (x: bytes) -> (y: bytes) -> Pure bool True (fun z -> z == true <==> Set.prop_order_of_bool_order Set.lex_byte_order x y) =
    fun x1 x2 -> Set.lex_byte_order x1 x2
  in
  Set.tot_parse_byte_sorted_list_correct (Set.prop_order_of_bool_order Set.lex_byte_order) tbo pp r;
  set_of_eq pp r;
  if Seq.length r = 0 then ()
  else begin
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    assert (Seq.equal r (Seq.append f r'));
    strong_ext #asn1_strong_parser_kind pp f r';
    sf_aux tbo pp f r';
    let Some (_, c1) = SB.parse pp r in
    assert (c1 == n);
    assert (Seq.slice r 0 c1 == f);
    assert (Seq.slice r c1 (Seq.length r) == r');
    assert (Some? (Set.tot_parse_byte_sorted_list_bare tbo pp r))
  end
#pop-options

let acc_set_of (ne: bool) (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (acc #asn1_weak_parser_kind (parse_sized_set ne (asn1_as_parser k)) b))
  (ensures (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET_OF ne k)) b))
= ()

let sf_empty (#t: Type) (pp: asn1_strong_parser t) : Lemma (sf pp None (SI.sort_list SI.lt_lex RR.id_enc [])) = ()
