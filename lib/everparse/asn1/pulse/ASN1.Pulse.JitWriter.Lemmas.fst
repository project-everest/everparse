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

(* Proven in a clean context: letting SMT unfold `id_then_v` and
   `consumed` inside `lacc_choice` was brittle (failed for most Z3
   seeds, and on macOS CI). *)
let id_then_v_acc (#t: Type) (fp: asn1_id_t -> parser asn1_strong_parser_kind t) (b: bytes)
  (id: asn1_id_t) (c1: SB.consumed_length b)
: Lemma
  (requires (
    parse parse_asn1_identifier_U32 b == Some (id, c1) /\
    acc #asn1_strong_parser_kind (fp id) (Seq.slice b c1 (Seq.length b))))
  (ensures (
    match PSL.id_then_v fp b with
    | Some (_, c) -> c == Seq.length b
    | None -> False))
= ()

let lacc_choice (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (b: bytes)
: Lemma (requires (lacc lc b)) (ensures (acc #asn1_strong_parser_kind (asn1_as_parser (ASN1_CHOICE_ILC lc pf)) b))
= let k = ASN1_CHOICE_ILC lc pf in
  PSL.k_id_then k b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  Co.asn1_choice_twin_consumed lc pf id (Seq.slice b c1 (Seq.length b));
  id_then_v_acc (snd (asn1_as_parser_twin k)) b id c1

(* Acceptance of an ILC, given the identifier at the start of `b`. Proven
   on its own: unfolding `ILC.ilc_eq` inside `lacc_hd`/`lacc_hd_inv` was
   brittle. *)
let ilc_consumed_acc (cb cl: option nat) (lb: nat) (c1: nat) (eq: bool)
: Lemma
  (requires (c1 <= lb /\ cb == (if eq then (match cl with None -> None | Some c2 -> Some (c1 + c2)) else None)))
  (ensures (cb == Some lb <==> (eq == true /\ cl == Some (lb - c1))))
= ()

#push-options "--fuel 0 --ifuel 1"
let ilc_acc (id': asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (b: bytes)
  (id: asn1_id_t) (c1: SB.consumed_length b)
: Lemma
  (requires (parse parse_asn1_identifier_U32 b == Some (id, c1)))
  (ensures (acc #asn1_strong_parser_kind (parse_asn1_ILC id' p) b <==>
    (id == id' /\ acc #asn1_strong_parser_kind (parse_asn1_LC p) (Seq.slice b c1 (Seq.length b)))))
= ILC.ilc_eq id' p b;
  let b1 = Seq.slice b c1 (Seq.length b) in
  let cb = Sq.consumed #asn1_strong_parser_kind (parse_asn1_ILC id' p) b in
  let cl = Sq.consumed #asn1_strong_parser_kind (parse_asn1_LC p) b1 in
  assert (cb == (if id = id' then (match cl with None -> None | Some c2 -> Some (c1 + c2)) else None));
  ilc_consumed_acc cb cl (Seq.length b) c1 (id = id');
  assert (Seq.length b1 == Seq.length b - c1);
  assert (acc #asn1_strong_parser_kind (parse_asn1_ILC id' p) b <==> cb == Some (Seq.length b));
  assert (acc #asn1_strong_parser_kind (parse_asn1_LC p) b1 <==> cl == Some (Seq.length b1));
  assert ((id = id') == true <==> id == id')
#pop-options

let lacc_hd (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (parse_asn1_ILC id' (asn1_content_as_parser c)) b)) (ensures (lacc ((id', c) :: tl) b))
= ILC.ilc_eq id' (asn1_content_as_parser c) b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  ilc_acc id' (asn1_content_as_parser c) b id c1;
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

(* Sequence facts proven on their own rather than by `Seq.equal` in large
   contexts, where they were brittle *)
let slice_split (r: bytes) (n: nat { n <= Seq.length r })
: Lemma (r == Seq.append (Seq.slice r 0 n) (Seq.slice r n (Seq.length r)))
= assert (Seq.equal r (Seq.append (Seq.slice r 0 n) (Seq.slice r n (Seq.length r))))

let slice_append_suffix (b x: bytes) (c1: nat { c1 <= Seq.length b })
: Lemma (Seq.slice (Seq.append b x) c1 (Seq.length b + Seq.length x) == Seq.append (Seq.slice b c1 (Seq.length b)) x)
= assert (Seq.equal (Seq.slice (Seq.append b x) c1 (Seq.length b + Seq.length x)) (Seq.append (Seq.slice b c1 (Seq.length b)) x))

let slice_append_prefix (b x: bytes)
: Lemma (Seq.slice (Seq.append b x) 0 (Seq.length b) == b)
= assert (Seq.equal (Seq.slice (Seq.append b x) 0 (Seq.length b)) b)

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

let prefix_sub (r1 r2: bytes) (n i j: nat)
: Lemma (requires (i <= j /\ j <= n /\ n <= Seq.length r1 /\ n <= Seq.length r2 /\ Seq.slice r2 0 n == Seq.slice r1 0 n))
  (ensures (Seq.slice r2 i j == Seq.slice r1 i j))
= Seq.slice_slice r1 0 n i j;
  Seq.slice_slice r2 0 n i j

let slice_head (r: bytes) (i j: nat)
: Lemma (requires (i <= j /\ j <= Seq.length r))
  (ensures (Seq.slice (Seq.slice r i (Seq.length r)) 0 (j - i) == Seq.slice r i j))
= Seq.slice_slice r i (Seq.length r) 0 (j - i)

#push-options "--fuel 0 --ifuel 2"
let frame_prefix (r1 r2: bytes) (n: nat)
: Lemma (requires (SI.frame_len r1 == n /\ n > 0 /\ n <= Seq.length r1 /\ n <= Seq.length r2 /\ Seq.slice r2 0 n == Seq.slice r1 0 n))
  (ensures (SI.frame_len r2 == n))
= let Some (_, n1) = SB.parse parse_asn1_identifier_U32 r1 in
  let s1 = Seq.slice r1 n1 (Seq.length r1) in
  let s2 = Seq.slice r2 n1 (Seq.length r2) in
  let Some (_, n2) = SB.parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) s1 in
  assert (n1 + n2 <= n);
  prefix_sub r1 r2 n 0 n1;
  SB.parse_strong_prefix #asn1_strong_parser_kind parse_asn1_identifier_U32 r1 r2;
  prefix_sub r1 r2 n n1 (n1 + n2);
  slice_head r1 n1 (n1 + n2);
  slice_head r2 n1 (n1 + n2);
  SB.parse_strong_prefix (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) s1 s2
#pop-options

(* The bytes `r` are a sequence of frames, each accepted by `pp`, sorted by
   encoding (the first one being greater than `prev`, if any) *)
#push-options "--fuel 0 --ifuel 1 --using_facts_from '* -ASN1.Pulse.SortedInsert.frame_len'"
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
#pop-options

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
    slice_split r n;
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
    slice_split r n;
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

(* SET { ... }: each component is written and checked on its own (it must
   be either empty, for an absent OPTIONAL or DEFAULT component, or exactly
   one frame whose identifier is one of those of the component), then
   inserted at its sorted position into the components written so far.
   `fl its r l`: `r` is the sequence of frames of the elements `l`. *)

open ASN1.Spec.SetComponents
module FSet = FStar.Set
module LT = FStar.List.Tot
module TC = LowParse.Tot.Combinators
module PSet = ASN1.Pulse.ParseSet.Lemmas
module SC = ASN1.Pulse.SetComp

let pse_frame (its: list gen_decorated_parser_twin) (f: bytes) (e: set_elem_t its) : prop =
  match SB.parse (parse_set_elem its) f with
  | Some (e', c) -> e' == e /\ (c <: nat) == Seq.length f
  | None -> False

let rec fl (its: list gen_decorated_parser_twin) (r: bytes) (l: list (set_elem_t its))
: GTot prop (decreases l)
= match l with
  | [] -> Seq.length r == 0
  | e :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    n > 0 /\ pse_frame its (Seq.slice r 0 n) e /\ fl its (Seq.slice r n (Seq.length r)) q

let sacc (its: list gen_decorated_parser_twin) (r: bytes) : prop =
  exists (l: list (set_elem_t its)) . fl its r l /\ set_ok its l == true

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec fl_parse (its: list gen_decorated_parser_twin) (r: bytes) (l: list (set_elem_t its))
: Lemma (requires (fl its r l))
  (ensures (match SB.parse (parse_list (parse_set_elem its)) r with
    | Some (l', c) -> l' == l /\ (c <: nat) == Seq.length r
    | None -> False))
  (decreases l)
= match l with
  | [] -> tot_parse_list_eq (parse_set_elem its) r
  | e :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    Seq.lemma_split r n;
    tot_parse_list_eq (parse_set_elem its) r;
    strong_ext #asn1_strong_parser_kind (parse_set_elem its) f r';
    fl_parse its r' q
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let acc_set (ids: _) (items: asn1_gen_items_l ids) (pf: _) (b: bytes)
: Lemma (requires (sacc (In.twins_of items) b))
  (ensures (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf)) b))
= let its = In.twins_of items in
  set_to_tuple_injective its;
  TC.parse_synth_eq (parse_list (parse_set_elem its) `TC.parse_filter` set_ok its) (set_to_tuple its) b;
  TC.parse_filter_eq (parse_list (parse_set_elem its)) (set_ok its) b;
  eliminate exists (l: list (set_elem_t its)) . fl its b l /\ set_ok its l == true
  with fl_parse its b l
#pop-options

(* Insertion of an element at its sorted position *)

let rec lins (#t: Type) (key: t -> Tot (option asn1_id_t)) (x: t) (l: list t) : Tot (list t) =
  match l with
  | [] -> [x]
  | y :: q -> if opt_tag_lt (key y) (key x) then y :: lins key x q else x :: l

let lins_hd (#t: Type) (key: t -> Tot (option asn1_id_t)) (x: t) (l: list t)
: Lemma (Cons? (lins key x l) /\ (LT.hd (lins key x l) == x \/ (Cons? l /\ LT.hd (lins key x l) == LT.hd l)))
= ()

let rec tags_distinct (#t: Type) (key: t -> Tot (option asn1_id_t)) (a: asn1_id_t) (l: list t) : Tot prop =
  match l with
  | [] -> True
  | y :: q -> (match key y with Some b -> ~ (asn1_same_tag a b) | None -> True) /\ tags_distinct key a q

let rec tags_in (#t: Type) (key: t -> Tot (option asn1_id_t)) (s: FSet.set asn1_id_t) (l: list t) : Tot prop =
  match l with
  | [] -> True
  | y :: q -> (match key y with Some b -> FSet.mem b s | None -> False) /\ tags_in key s q

let rec in_distinct (#t: Type) (key: t -> Tot (option asn1_id_t)) (a: asn1_id_t) (s1 s2: FSet.set asn1_id_t) (l: list t)
: Lemma (requires (FSet.mem a s1 /\ asn1_set_disjoint s1 s2 /\ tags_in key s2 l))
  (ensures (tags_distinct key a l))
= match l with
  | [] -> ()
  | _ :: q -> in_distinct key a s1 s2 q

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec tags_sorted_lins (#t: Type) (key: t -> Tot (option asn1_id_t)) (x: t) (a: asn1_id_t) (l: list t)
: Lemma (requires (tags_sorted key l /\ key x == Some a /\ tags_distinct key a l))
  (ensures (tags_sorted key (lins key x l)))
= match l with
  | [] -> ()
  | y :: q ->
    if opt_tag_lt (key y) (key x) then begin
      tags_sorted_lins key x a q;
      lins_hd key x q
    end else ()
#pop-options

(* Components of a SET with a head component `hd` *)

let as_e (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (e: set_elem_t (hd :: tl))
: Tot (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl))
= e

let inr_e (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (e: set_elem_t tl)
: Tot (set_elem_t (hd :: tl))
= Inr #(asn1_decorated_t (Mkgendcparser?.d hd)) e

let rec inr_l (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (l: list (set_elem_t tl))
: Tot (list (set_elem_t (hd :: tl)))
= match l with
  | [] -> []
  | e :: q -> inr_e hd tl e :: inr_l hd tl q

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec inr_l_props (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (l: list (set_elem_t tl)) (a: asn1_id_t)
: Lemma (heads (PSet.as_either hd tl (inr_l hd tl l)) == [] /\
    tails (PSet.as_either hd tl (inr_l hd tl l)) == l /\
    tags_sorted (elem_tag (hd :: tl)) (inr_l hd tl l) == tags_sorted (elem_tag tl) l /\
    (tags_distinct (elem_tag tl) a l ==> tags_distinct (elem_tag (hd :: tl)) a (inr_l hd tl l)))
= match l with
  | [] -> ()
  | _ :: q -> inr_l_props hd tl q a

let rec lins_inr (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (x: set_elem_t (hd :: tl)) (l: list (set_elem_t tl))
: Lemma (requires (Inl? (as_e hd tl x)))
  (ensures (heads (PSet.as_either hd tl (lins (elem_tag (hd :: tl)) x (inr_l hd tl l))) == [Inl?.v (as_e hd tl x)] /\
    tails (PSet.as_either hd tl (lins (elem_tag (hd :: tl)) x (inr_l hd tl l))) == l))
= inr_l_props hd tl l (MK_ASN1_ID UNIVERSAL PRIMITIVE 0ul);
  match l with
  | [] -> ()
  | _ :: q -> lins_inr hd tl x q
#pop-options

(* Parsing one element of a SET with a head component `hd` *)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let set_elem_inr (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (b: bytes)
: Lemma (requires (match SB.parse parse_asn1_identifier_U32 b with Some (id, _) -> ~ (FSet.mem id (Sq.item_set hd)) | None -> True))
  (ensures (match SB.parse (parse_set_elem tl) b, SB.parse (parse_set_elem (hd :: tl)) b with
    | None, None -> True
    | Some (e2, n2), Some (e, n) -> e == inr_e hd tl e2 /\ (n <: nat) == n2
    | _ -> False))
= parse_set_elem_twin_cases_injective (hd :: tl);
  parse_set_elem_twin_cases_injective tl;
  TC.and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t (hd :: tl)) (parse_set_elem_twin (hd :: tl)) b;
  TC.and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t tl) (parse_set_elem_twin tl) b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, n1) ->
    let b' = Seq.slice b n1 (Seq.length b) in
    TC.parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b'

let elem_inl (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c: bytes)
: Lemma (requires (iacc [hd] c /\ Seq.length c > 0 /\ (match SI.parse_id c with Some id -> FSet.mem id (Sq.item_set hd) | None -> False)))
  (ensures (match SB.parse (parse_set_elem (hd :: tl)) c with
    | Some (e, n) -> (n <: nat) == Seq.length c /\ Inl? (as_e hd tl e)
    | None -> False))
= Sq.seq_cons_none [hd] c;
  parse_set_elem_twin_cases_injective (hd :: tl);
  TC.and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t (hd :: tl)) (parse_set_elem_twin (hd :: tl)) c;
  let Some (id, n1) = SB.parse parse_asn1_identifier_U32 c in
  let c' = Seq.slice c n1 (Seq.length c) in
  Sq.seq_single_some hd id c';
  TC.parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) c'
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"
let tag_frame (its: list gen_decorated_parser_twin) (f: bytes) (e: set_elem_t its)
: Lemma (requires (pse_frame its f e /\ C.items_tagged its))
  (ensures (SI.parse_id f == elem_tag its e /\
    (match elem_tag its e with Some id -> FSet.mem id (PSet.items_set its) | None -> False)))
= SC.set_elem_eq its f;
  match SB.parse parse_asn1_identifier_U32 f with
  | Some (id, _) -> PSet.comp_of_id_mem its id
  | None -> ()

let rec fl_tags (its: list gen_decorated_parser_twin) (r: bytes) (l: list (set_elem_t its))
: Lemma (requires (fl its r l /\ C.items_tagged its))
  (ensures (tags_in (elem_tag its) (PSet.items_set its) l))
  (decreases l)
= match l with
  | [] -> ()
  | e :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    tag_frame its (Seq.slice r 0 n) e;
    fl_tags its (Seq.slice r n (Seq.length r)) q

let rec fl_lift (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (r: bytes) (l: list (set_elem_t tl))
: Lemma (requires (fl tl r l /\ C.items_tagged tl /\ asn1_set_disjoint (Sq.item_set hd) (PSet.items_set tl)))
  (ensures (fl (hd :: tl) r (inr_l hd tl l)))
  (decreases l)
= match l with
  | [] -> ()
  | e :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    tag_frame tl f e;
    let Some id = elem_tag tl e in
    assert (FSet.mem id (PSet.items_set tl));
    assert (asn1_same_tag id id);
    assert (~ (FSet.mem id (Sq.item_set hd)));
    set_elem_inr hd tl f;
    fl_lift hd tl (Seq.slice r n (Seq.length r)) q

let fl_cons (its: list gen_decorated_parser_twin) (e: bytes) (x: set_elem_t its) (r: bytes) (l: list (set_elem_t its))
: Lemma (requires (SI.frame_len e == Seq.length e /\ Seq.length e > 0 /\ pse_frame its e x /\ fl its r l))
  (ensures (fl its (Seq.append e r) (x :: l)))
= let b = Seq.append e r in
  let n = Seq.length e in
  assert (Seq.equal (Seq.slice b 0 n) (Seq.slice e 0 n));
  frame_prefix e b n;
  assert (Seq.equal (Seq.slice b 0 n) e);
  assert (Seq.equal (Seq.slice b n (Seq.length b)) r)

let rec fl_ins (its: list gen_decorated_parser_twin) (e: bytes) (x: set_elem_t its) (r: bytes) (l: list (set_elem_t its))
: Lemma (requires (C.items_tagged its /\ SI.frame_len e == Seq.length e /\ Seq.length e > 0 /\ pse_frame its e x /\ fl its r l))
  (ensures (fl its (SI.ins SI.lt_tag e r) (lins (elem_tag its) x l)))
  (decreases l)
= SI.ins_unfold SI.lt_tag e r;
  tag_frame its e x;
  match l with
  | [] ->
    ident_empty ();
    assert (Seq.equal r Seq.empty);
    fl_cons its e x r l
  | y :: q ->
    let n = SI.frame_len r in
    SI.frame_len_le r;
    let f = Seq.slice r 0 n in
    let r' = Seq.slice r n (Seq.length r) in
    tag_frame its f y;
    if opt_tag_lt (elem_tag its y) (elem_tag its x) then begin
      fl_ins its e x r' q;
      let i = SI.ins SI.lt_tag e r' in
      let b = Seq.append f i in
      assert (Seq.equal (Seq.slice b 0 n) (Seq.slice r 0 n));
      frame_prefix r b n;
      assert (Seq.equal (Seq.slice b 0 n) f);
      assert (Seq.equal (Seq.slice b n (Seq.length b)) i)
    end else
      fl_cons its e x r l
#pop-options

(* The checks on one component, and the well-formedness of the SET *)

let elt_ok (s: FSet.set asn1_id_t) (c: bytes) : prop =
  Seq.length c > 0 ==> (SI.frame_len c == Seq.length c /\ (match SI.parse_id c with Some id -> FSet.mem id s | None -> False))

let sacc1 (hd: gen_decorated_parser_twin) (c: bytes) : prop =
  iacc [hd] c /\ elt_ok (Sq.item_set hd) c

let set_cons_ok (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) : prop =
  C.items_tagged (hd :: tl) /\ asn1_set_disjoint (Sq.item_set hd) (PSet.items_set tl)

let ins_empty (r: bytes) : Lemma (SI.ins SI.lt_tag Seq.empty r == r) =
  SI.ins_unfold SI.lt_tag Seq.empty r;
  ident_empty ();
  Seq.append_empty_l r

let ins_empty_r (e: bytes) : Lemma (SI.ins SI.lt_tag e Seq.empty == e) =
  SI.ins_unfold SI.lt_tag e Seq.empty;
  ident_empty ();
  assert (Seq.equal (Seq.append e Seq.empty) e)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let sacc_cons (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (c1 c2: bytes)
: Lemma (requires (set_cons_ok hd tl /\ sacc1 hd c1 /\ sacc tl c2))
  (ensures (sacc (hd :: tl) (SI.ins SI.lt_tag c1 c2)))
= let its = hd :: tl in
  eliminate exists (l2: list (set_elem_t tl)) . fl tl c2 l2 /\ set_ok tl l2 == true
  with begin
    fl_lift hd tl c2 l2;
    let l = inr_l hd tl l2 in
    if Seq.length c1 = 0 then begin
      inr_l_props hd tl l2 (MK_ASN1_ID UNIVERSAL PRIMITIVE 0ul);
      assert (Seq.equal c1 Seq.empty);
      ins_empty c2;
      iacc_single_empty hd;
      assert (fl its (SI.ins SI.lt_tag c1 c2) l /\ set_ok its l == true)
    end else begin
      elem_inl hd tl c1;
      let Some (x, _) = SB.parse (parse_set_elem its) c1 in
      assert (pse_frame its c1 x);
      fl_ins its c1 x c2 l;
      let Some id = SI.parse_id c1 in
      tag_frame its c1 x;
      fl_tags tl c2 l2;
      in_distinct (elem_tag tl) id (Sq.item_set hd) (PSet.items_set tl) l2;
      inr_l_props hd tl l2 id;
      tags_sorted_lins (elem_tag its) x id l;
      lins_inr hd tl x l2;
      let l' = lins (elem_tag its) x l in
      assert (fl its (SI.ins SI.lt_tag c1 c2) l' /\ set_ok its l' == true)
    end
  end
#pop-options

#push-options "--fuel 1 --ifuel 1"
let sacc_nil (x: bytes) : Lemma (requires (iacc [] x)) (ensures (sacc [] x)) =
  Sq.seq_nil_none x;
  assert (fl [] x [] /\ set_ok [] [] == true)

let sacc_single (hd: gen_decorated_parser_twin) (c: bytes)
: Lemma (requires (set_cons_ok hd [] /\ sacc1 hd c)) (ensures (sacc [hd] c))
= assert (fl [] Seq.empty [] /\ set_ok [] [] == true);
  sacc_cons hd [] c Seq.empty;
  ins_empty_r c

let rec ids_disj (#i: _) (ls: asn1_gen_items_l i) (s: FSet.set asn1_id_t)
: Lemma (requires (asn1_set_k_wf' s i)) (ensures (asn1_set_disjoint s (PSet.items_set (In.twins_of ls)))) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS s' _ dk _ tl ->
    ids_disj tl s;
    assert (Sq.item_set (In.twin_of dk) == s')

let set_cons_ok_intro (#s: _) (#d: _) (dk: asn1_decorated_k s d) (#i: _) (tl: asn1_gen_items_l i)
: Lemma (requires (asn1_set_k_wf ((s, d) :: i))) (ensures (set_cons_ok (In.twin_of dk) (In.twins_of tl)))
= C.items_tagged_intro (ASN1_GEN_ITEMS_CONS s d dk i tl);
  ids_disj tl s;
  assert (Sq.item_set (In.twin_of dk) == s)
#pop-options

(* Terminals: checks on the raw input, before writing. `tacc k c` states
   that the content `c` is a valid DER content of the terminal type `k`;
   `holds k f c` that its value, if any, satisfies `f`. *)

module E = ASN1.Spec.Content.Enc
module ADB = ASN1.Pulse.AnyDefinedBy
module SFL = LowParse.Spec.FLData
module SCo = LowParse.Spec.Combinators
module INT = ASN1.Spec.Content.INTEGER

let tacc (k: asn1_terminal_k) (c: bytes) : prop =
  acc #asn1_weak_parser_kind (asn1_terminal_as_parser k) c

let holds (k: asn1_terminal_k) (f: asn1_terminal_t k -> bool) (c: bytes) : prop =
  match parse (asn1_terminal_as_parser k) c with
  | Some (v, n) -> n == Seq.length c ==> f v == true
  | None -> True

let leaf_tacc (k: E.leaf_k) (x: asn1_terminal_t k) (f: asn1_terminal_t k -> bool) (c: bytes)
: Lemma (requires (c == E.leaf_enc k x))
  (ensures (tacc k c /\ (holds k f c <==> f x == true)))
= E.parse_leaf_enc k x

let acc_restricted (k: asn1_terminal_k) (r: asn1_restriction k) (c: bytes)
: Lemma ((tacc k c /\ holds k (restriction_pred r) c) <==>
  acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) c)
= TC.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred r) c

let restricted_holds (k: asn1_terminal_k) (r: asn1_restriction k) (c: bytes)
: Lemma (requires (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) c))
  (ensures (tacc k c /\ holds k (restriction_pred r) c))
= TC.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred r) c

let acc_default (k: asn1_terminal_k) (defv: asn1_terminal_t k) (c: bytes)
: Lemma ((tacc k c /\ holds k (defaultv_filter defv) c) <==>
  acc #asn1_weak_parser_kind (asn1_content_as_parser (Co.default_content k defv)) c)
= TC.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred (RESTRICT_CUSTOM (defaultv_filter defv))) c

let acc_default_restricted (k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_terminal_t k) (c: bytes)
: Lemma (((tacc k c /\ holds k (restriction_pred r) c) /\ holds k (defaultv_filter defv) c) <==>
  acc #asn1_weak_parser_kind (asn1_content_as_parser (Co.default_restricted_content k r defv)) c)
= TC.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred (RESTRICT_CUSTOM (Co.restricted_default_filter r defv))) c

(* A content that is not the encoding of the default value *)
let neq_enc_holds (k: E.leaf_k) (defv: asn1_terminal_t k) (c: bytes)
: Lemma (requires (~ (c == E.leaf_enc k defv))) (ensures (holds k (defaultv_filter defv) c))
= E.leaf_enc_consumed k c;
  assert (Seq.equal (Seq.slice c 0 (Seq.length c)) c)

(* A content that the fixed-length equality check rejects *)
let neq_fl_holds (k: asn1_terminal_k) (defv: asn1_terminal_t k) (c: bytes)
: Lemma (requires (None? (parse (ADB.key_eq_fldata k defv (Seq.length c)) (Seq.slice c 0 (Seq.length c)))))
  (ensures (holds k (defaultv_filter defv) c))
= let p = asn1_terminal_as_parser k in
  assert (Seq.equal (Seq.slice c 0 (Seq.length c)) c);
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (ADB.key_eq defv)) (Seq.length c) c;
  SCo.parse_filter_eq #asn1_weak_parser_kind p (ADB.key_eq defv) c

(* A content that the fixed-length equality check accepts *)
let fl_eq_not_holds (k: asn1_terminal_k) (defv: asn1_terminal_t k) (c: bytes)
: Lemma (requires (Some? (parse (ADB.key_eq_fldata k defv (Seq.length c)) (Seq.slice c 0 (Seq.length c)))))
  (ensures (~ (holds k (defaultv_filter defv) c)))
= let p = asn1_terminal_as_parser k in
  assert (Seq.equal (Seq.slice c 0 (Seq.length c)) c);
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (ADB.key_eq defv)) (Seq.length c) c;
  SCo.parse_filter_eq #asn1_weak_parser_kind p (ADB.key_eq defv) c

let restricted_iff (k: asn1_terminal_k) (r: asn1_restriction k) (c: bytes)
: Lemma (requires (tacc k c))
  (ensures (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) c <==> holds k (restriction_pred r) c))
= TC.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred r) c

(* INTEGER contents encoded from a 64-bit integer *)
let i64_interval (bound: pos { bound <= 8 }) (x: int) (c: bytes)
: Lemma (requires (INT.interval 8 x /\ c == E.integer_enc 8 x /\ tacc (ASN1_INTEGER bound) c))
  (ensures (INT.interval bound x))
= E.leaf_enc_consumed (ASN1_INTEGER bound) c;
  assert (Seq.equal (Seq.slice c 0 (Seq.length c)) c);
  let Some (v, _) = parse (asn1_terminal_as_parser (ASN1_INTEGER bound)) c in
  let v : int = v in
  INT.interval_weaken bound 8 v;
  E.leaf_enc_inj (ASN1_INTEGER 8) v x

(* DEFAULT: the item is present and accepted *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let iacc_default (id0: asn1_id_t) (#k: asn1_terminal_k) (defl: asn1_key_lit k) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (parse_asn1_ILC id0 (asn1_content_as_parser (Co.default_content k (key_of_lit k defl)))) b))
  (ensures (iacc [In.twin_of (ASN1_DEFAULT_TERMINAL id0 #k defl)] b))
= let hd = In.twin_of (ASN1_DEFAULT_TERMINAL id0 #k defl) in
  let p = asn1_content_as_parser (Co.default_content k (key_of_lit k defl)) in
  ILC.ilc_eq id0 p b;
  PSL.identifier_nonempty b;
  Sq.seq_cons_none [hd] b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  let b1 = Seq.slice b c1 (Seq.length b) in
  Sq.seq_single_some hd id b1;
  Co.default_terminal_twin_consumed id0 #k defl id b1

let iacc_default_restricted (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defl: asn1_key_lit k { restriction_pred r (key_of_lit k defl) }) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (parse_asn1_ILC id0 (asn1_content_as_parser (Co.default_restricted_content k r (key_of_lit k defl)))) b))
  (ensures (iacc [In.twin_of (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)] b))
= let hd = In.twin_of (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl) in
  let p = asn1_content_as_parser (Co.default_restricted_content k r (key_of_lit k defl)) in
  ILC.ilc_eq id0 p b;
  PSL.identifier_nonempty b;
  Sq.seq_cons_none [hd] b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  let b1 = Seq.slice b c1 (Seq.length b) in
  Sq.seq_single_some hd id b1;
  Co.default_restricted_twin_consumed id0 #k r defl id b1
#pop-options

(* Conversely, a TLV is accepted only if its contents are, and are
   shorter than 2^32 bytes *)

let hdr_big_head (n: nat) (rest: bytes)
: Lemma (requires (n >= 4294967296))
  (ensures (Seq.length (enc_hdr true n `Seq.append` rest) > 0 /\ Seq.index (enc_hdr true n `Seq.append` rest) 0 == 0xFFuy))
= let h1 = Seq.create 1 0xFFuy in
  let h2 = Seq.create 1 0uy `Seq.append` enc_unary n in
  Seq.lemma_index_app1 h1 h2 0;
  Seq.lemma_index_app1 (h1 `Seq.append` h2) rest 0

#push-options "--fuel 0 --ifuel 1"
let hdr_big_none (n: nat) (rest: bytes)
: Lemma (requires (n >= 4294967296))
  (ensures (None? (parse parse_asn1_length_u32_t (enc_hdr true n `Seq.append` rest))))
= let b = enc_hdr true n `Seq.append` rest in
  hdr_big_head n rest;
  parse_len_consumed b;
  match parse parse_asn1_length_u32_t b with
  | Some (y, c) ->
    enc_len_head y;
    Seq.lemma_index_slice b 0 c 0
  | None -> ()
#pop-options

#push-options "--z3rlimit 64"
let acc_tlv_inv (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (c: bytes)
: Lemma
  (requires (acc #asn1_strong_parser_kind (parse_asn1_ILC id p) (enc_tlv id true c)))
  (ensures (acc #asn1_weak_parser_kind p c /\ Seq.length c < 4294967296))
= let hdr = enc_hdr true (Seq.length c) in
  let rest = hdr `Seq.append` c in
  let b = enc_tlv id true c in
  assert (b == IE.asn1_id_enc id `Seq.append` rest);
  IE.parse_asn1_identifier_U32_enc id rest;
  ILC.ilc_eq id p b;
  Seq.append_slices (IE.asn1_id_enc id) rest;
  C.vlgen_eq p rest;
  if Seq.length c >= 4294967296
  then hdr_big_none (Seq.length c) c
  else begin
    let n = U32.uint_to_t (Seq.length c) in
    parse_enc_len n c;
    assert (Seq.equal (Seq.slice rest (Seq.length hdr) (Seq.length hdr + Seq.length c)) c)
  end
#pop-options

let acc_tlv_iff (id: asn1_id_t) (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack)) (c: bytes)
: Lemma (acc #asn1_strong_parser_kind (parse_asn1_ILC id p) (enc_tlv id true c) <==>
    (acc #asn1_weak_parser_kind p c /\ Seq.length c < 4294967296))
= Classical.move_requires (acc_tlv_inv id p) c;
  Classical.move_requires (acc_tlv id p) c


(* Framed chunks: one TLV with one of the given identifiers. A present
   component (other than ANY) is framed, and the acceptance of a framed
   first component and of the remaining ones are then independent, so that
   a failure in either is a failure of the whole. *)

let framed (s: FStar.Set.set asn1_id_t) (x: bytes) : prop =
  exists (id: asn1_id_t) (c: bytes) . FStar.Set.mem id s /\ x == enc_tlv id true c

let enc_tlv_ne (id: asn1_id_t) (c: bytes)
: Lemma (Seq.length (enc_tlv id true c) > 0)
= if Seq.length c < 4294967296 then enc_len_head (U32.uint_to_t (Seq.length c))

let framed_ne (s: FStar.Set.set asn1_id_t) (x: bytes)
: Lemma (requires (framed s x)) (ensures (Seq.length x > 0))
= eliminate exists (id: asn1_id_t) (c: bytes) . FStar.Set.mem id s /\ x == enc_tlv id true c
  with enc_tlv_ne id c

let framed_intro (id: asn1_id_t) (s: FStar.Set.set asn1_id_t) (c: bytes)
: Lemma (requires (FStar.Set.mem id s)) (ensures (framed s (enc_tlv id true c)))
= ()

let framed_sub (s1 s2: FStar.Set.set asn1_id_t) (x: bytes)
: Lemma (requires (framed s1 x /\ FStar.Set.subset s1 s2)) (ensures (framed s2 x))
= ()

#push-options "--fuel 1 --ifuel 1"
let iacc_plain_iff (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (acc #asn1_strong_parser_kind (asn1_as_parser k) b <==> iacc [In.twin_of (ASN1_PLAIN_ILC k)] b)
= let hd = In.twin_of (ASN1_PLAIN_ILC k) in
  twin_of_plain k;
  PSL.k_id_then k b;
  Sq.seq_cons_none [hd] b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    Sq.seq_single_some hd id b1;
    assert (parse_asn1_sequence_item_twin hd id == snd (asn1_as_parser_twin k) id)

let iacc_option_iff (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (Seq.length b > 0))
  (ensures (acc #asn1_strong_parser_kind (asn1_as_parser k) b <==> iacc [In.twin_of (ASN1_OPTION_ILC k)] b))
= let hd = In.twin_of (ASN1_OPTION_ILC k) in
  twin_of_option k;
  PSL.k_id_then k b;
  Sq.seq_cons_none [hd] b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    Sq.seq_single_some hd id b1;
    assert (parse_asn1_sequence_item_twin hd id == (snd (asn1_as_parser_twin k) id `LowParse.Tot.Combinators.parse_synth` Some));
    LowParse.Tot.Combinators.parse_synth_eq (snd (asn1_as_parser_twin k) id) Some b1

let iacc_default_iff (id0: asn1_id_t) (#k: asn1_terminal_k) (defl: asn1_key_lit k) (b: bytes)
: Lemma (requires (Seq.length b > 0))
  (ensures (acc #asn1_strong_parser_kind (parse_asn1_ILC id0 (asn1_content_as_parser (Co.default_content k (key_of_lit k defl)))) b <==>
    iacc [In.twin_of (ASN1_DEFAULT_TERMINAL id0 #k defl)] b))
= let hd = In.twin_of (ASN1_DEFAULT_TERMINAL id0 #k defl) in
  let p = asn1_content_as_parser (Co.default_content k (key_of_lit k defl)) in
  ILC.ilc_eq id0 p b;
  Sq.seq_cons_none [hd] b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    Sq.seq_single_some hd id b1;
    Co.default_terminal_twin_consumed id0 #k defl id b1

let iacc_default_restricted_iff (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defl: asn1_key_lit k { restriction_pred r (key_of_lit k defl) }) (b: bytes)
: Lemma (requires (Seq.length b > 0))
  (ensures (acc #asn1_strong_parser_kind (parse_asn1_ILC id0 (asn1_content_as_parser (Co.default_restricted_content k r (key_of_lit k defl)))) b <==>
    iacc [In.twin_of (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)] b))
= let hd = In.twin_of (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl) in
  let p = asn1_content_as_parser (Co.default_restricted_content k r (key_of_lit k defl)) in
  ILC.ilc_eq id0 p b;
  Sq.seq_cons_none [hd] b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    Sq.seq_single_some hd id b1;
    Co.default_restricted_twin_consumed id0 #k r defl id b1
#pop-options

let strong_prefix_down (#t: Type) (p: SB.parser asn1_strong_parser_kind t) (b1 b2: bytes) (n: nat)
: Lemma
  (requires (Seq.length b1 <= Seq.length b2 /\ Seq.slice b2 0 (Seq.length b1) == b1 /\ Sq.consumed p b2 == Some n /\ n <= Seq.length b1))
  (ensures (Sq.consumed p b1 == Some n))
= let Some (_, c) = SB.parse p b2 in
  Seq.slice_slice b2 0 (Seq.length b1) 0 c;
  SB.parse_strong_prefix p b2 b1

let lc_size_tlv (c x2: bytes)
: Lemma
  (PSL.lc_size ((enc_hdr true (Seq.length c) `Seq.append` c) `Seq.append` x2) ==
    (if Seq.length c < 4294967296 then Some (Seq.length (enc_hdr true (Seq.length c)) + Seq.length c) else None))
= let hdr = enc_hdr true (Seq.length c) in
  Seq.append_assoc hdr c x2;
  if Seq.length c < 4294967296
  then parse_enc_len (U32.uint_to_t (Seq.length c)) (c `Seq.append` x2)
  else hdr_big_none (Seq.length c) (c `Seq.append` x2)

let slice_append_r (a b: bytes)
: Lemma (Seq.slice (a `Seq.append` b) (Seq.length a) (Seq.length a + Seq.length b) == b)
= assert (Seq.equal (Seq.slice (a `Seq.append` b) (Seq.length a) (Seq.length a + Seq.length b)) b)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 128"
let iacc_cons_inv' (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (id: asn1_id_t) (c x2: bytes)
: Lemma
  (requires (FStar.Set.mem id (Sq.item_set hd) /\ PSL.item_shaped hd /\ iacc (hd :: tl) (enc_tlv id true c `Seq.append` x2)))
  (ensures (iacc [hd] (enc_tlv id true c) /\ iacc tl x2))
= let hdr = enc_hdr true (Seq.length c) in
  let r1 = hdr `Seq.append` c in
  let x1 = enc_tlv id true c in
  let x = x1 `Seq.append` x2 in
  let ie = IE.asn1_id_enc id in
  let rr = r1 `Seq.append` x2 in
  Seq.append_assoc ie r1 x2;
  IE.parse_asn1_identifier_U32_enc id rr;
  IE.parse_asn1_identifier_U32_enc id r1;
  enc_tlv_ne id c;
  Sq.seq_cons_none (hd :: tl) x;
  Sq.seq_cons_none [hd] x1;
  let c1 = Seq.length ie in
  assert (x1 == ie `Seq.append` r1);
  assert (x == ie `Seq.append` rr);
  slice_append_r ie rr;
  slice_append_r ie r1;
  Sq.seq_cons_cons_some hd tl id rr;
  Sq.seq_single_some hd id r1;
  let tw = parse_asn1_sequence_item_twin hd id in
  assert (PSL.lc_shaped tw);
  lc_size_tlv c x2;
  match Sq.consumed #asn1_strong_parser_kind tw rr with
  | None -> ()
  | Some n1 ->
    assert (Seq.equal (Seq.slice rr 0 (Seq.length r1)) r1);
    strong_prefix_down tw r1 rr n1;
    assert (Seq.equal (Seq.slice rr n1 (Seq.length rr)) x2)
#pop-options

let iacc_cons_inv (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (x1 x2: bytes)
: Lemma
  (requires (framed (Sq.item_set hd) x1 /\ PSL.item_shaped hd /\ iacc (hd :: tl) (x1 `Seq.append` x2)))
  (ensures (iacc [hd] x1 /\ iacc tl x2))
= eliminate exists (id: asn1_id_t) (c: bytes) . FStar.Set.mem id (Sq.item_set hd) /\ x1 == enc_tlv id true c
  with iacc_cons_inv' hd tl id c x2

(* Converses, used by the JIT writers to report invalid inputs *)

#push-options "--fuel 2 --ifuel 1"
let item_set_twin (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (Sq.item_set (In.twin_of dk) == s)
= ()

let acc_k_ilc_inv (id: asn1_id_t) (c: asn1_content_k) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (asn1_as_parser (ASN1_ILC id c)) b)) (ensures (acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser c)) b))
= ()

let acc_prefixed_inv (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (requires (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_PREFIXED k)) b)) (ensures (acc #asn1_strong_parser_kind (asn1_as_parser k) b))
= ()

let acc_sequence_inv (g: asn1_gen_items_lk) (b: bytes)
: Lemma (requires (acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE g)) b)) (ensures (iacc (In.twins_of (dsnd g)) b))
= ()
#pop-options

(* CHOICE: converses *)

let framed_pid (s: FStar.Set.set asn1_id_t) (b: bytes)
: Lemma (requires (framed s b))
  (ensures (match parse parse_asn1_identifier_U32 b with Some (id, _) -> FStar.Set.mem id s | None -> False))
= eliminate exists (id: asn1_id_t) (c: bytes) . FStar.Set.mem id s /\ b == enc_tlv id true c
  with begin
    let r1 = enc_hdr true (Seq.length c) `Seq.append` c in
    assert (enc_tlv id true c == IE.asn1_id_enc id `Seq.append` r1);
    IE.parse_asn1_identifier_U32_enc id r1
  end

let id_then_acc (#t: Type) (fp: asn1_id_t -> parser asn1_strong_parser_kind t) (b: bytes)
: Lemma (requires (match PSL.id_then_v fp b with Some (_, c) -> c == Seq.length b | None -> False))
  (ensures (match parse parse_asn1_identifier_U32 b with
    | Some (id, c1) -> acc #asn1_strong_parser_kind (fp id) (Seq.slice b c1 (Seq.length b))
    | None -> False))
= ()

let lacc_choice_inv (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (b: bytes)
: Lemma (requires (acc #asn1_strong_parser_kind (asn1_as_parser (ASN1_CHOICE_ILC lc pf)) b)) (ensures (lacc lc b))
= PSL.k_id_then (ASN1_CHOICE_ILC lc pf) b;
  id_then_acc (snd (asn1_as_parser_twin (ASN1_CHOICE_ILC lc pf))) b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  Co.asn1_choice_twin_consumed lc pf id (Seq.slice b c1 (Seq.length b))

let lacc_hd_inv (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma (requires (lacc ((id', c) :: tl) b /\ framed (FStar.Set.singleton id') b))
  (ensures (acc #asn1_strong_parser_kind (parse_asn1_ILC id' (asn1_content_as_parser c)) b))
= framed_pid (FStar.Set.singleton id') b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  ilc_acc id' (asn1_content_as_parser c) b id c1;
  Co.asn1_choice_payload_cons id' c tl id (Seq.slice b c1 (Seq.length b))

let rec as_set'_mem (l: list asn1_id_t) (x: asn1_id_t)
: Lemma (FStar.Set.mem x (FStar.Set.as_set' l) <==> List.Tot.mem x l)
= match l with
  | [] -> ()
  | _ :: q -> as_set'_mem q x

#push-options "--fuel 2 --ifuel 1"
let lacc_tl_inv (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k)) (b: bytes)
: Lemma
  (requires (lacc ((id', c) :: tl) b /\ framed (FStar.Set.as_set' (List.Tot.map fst tl)) b /\
    List.Tot.noRepeats (List.Tot.map fst ((id', c) :: tl))))
  (ensures (lacc tl b))
= framed_pid (FStar.Set.as_set' (List.Tot.map fst tl)) b;
  let Some (id, c1) = parse parse_asn1_identifier_U32 b in
  as_set'_mem (List.Tot.map fst tl) id;
  Co.asn1_choice_payload_cons id' c tl id (Seq.slice b c1 (Seq.length b))
#pop-options

(* SEQUENCE OF: converses. Each element is parsed as one TLV
   (`tlv_shaped`), so if an element that is one TLV (`tlvish`) is
   rejected on its own, then so is the whole list. *)

let tlv_shaped (#t: Type) (pp: asn1_strong_parser t) : prop =
  forall (b: bytes) . match SB.parse pp b with
    | Some (_, n) -> PSL.tlv_size b == Some n
    | None -> True

#push-options "--fuel 1 --ifuel 1"
let tlv_shaped_k' (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (match SB.parse (asn1_as_parser k) b with
    | Some (_, n) -> PSL.tlv_size b == Some n
    | None -> True)
= PSL.k_id_then k b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) -> PSL.k_twin_shaped' k id (Seq.slice b c1 (Seq.length b))
#pop-options

let tlv_shaped_k (#s: _) (k: asn1_k s)
: Lemma (tlv_shaped (asn1_as_parser k))
= Classical.forall_intro (tlv_shaped_k' k)

let tlv_ne (b: bytes)
: Lemma (requires (Some? (PSL.tlv_size b))) (ensures (Seq.length b > 0))
= PSL.identifier_nonempty b

let acc_tlv_ne (#t: Type) (pp: asn1_strong_parser t) (b: bytes)
: Lemma (requires (tlv_shaped pp /\ acc #asn1_strong_parser_kind pp b)) (ensures (Seq.length b > 0))
= assert (match SB.parse pp b with Some (_, n) -> PSL.tlv_size b == Some n | None -> True);
  tlv_ne b

let tlvish (y: bytes) : prop =
  (exists (id: asn1_id_t) (c: bytes) . y == enc_tlv id true c) \/ PSL.tlv_size y == Some (Seq.length y)

let framed_tlvish (s: FStar.Set.set asn1_id_t) (y: bytes)
: Lemma (requires (framed s y)) (ensures (tlvish y))
= ()

let tlv_size_ext (b x: bytes)
: Lemma (requires (Some? (PSL.tlv_size b))) (ensures (PSL.tlv_size (Seq.append b x) == PSL.tlv_size b))
= let Some (_, c1) = parse parse_asn1_identifier_U32 b in
  strong_ext #asn1_strong_parser_kind parse_asn1_identifier_U32 b x;
  let b1 = Seq.slice b c1 (Seq.length b) in
  slice_append_suffix b x c1;
  strong_ext #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t b1 x

let tlv_enc_ext (id: asn1_id_t) (c x: bytes)
: Lemma (Seq.length (enc_tlv id true c) > 0 /\
    (PSL.tlv_size (Seq.append (enc_tlv id true c) x) == Some (Seq.length (enc_tlv id true c)) \/
     PSL.tlv_size (Seq.append (enc_tlv id true c) x) == None))
= let r1 = enc_hdr true (Seq.length c) `Seq.append` c in
  let ie = IE.asn1_id_enc id in
  let rr = r1 `Seq.append` x in
  Seq.append_assoc ie r1 x;
  IE.parse_asn1_identifier_U32_enc id rr;
  enc_tlv_ne id c;
  assert (enc_tlv id true c == ie `Seq.append` r1);
  let b = Seq.append (enc_tlv id true c) x in
  assert (b == ie `Seq.append` rr);
  Seq.append_slices ie rr;
  lc_size_tlv c x

let tlvish_ext (y x: bytes)
: Lemma (requires (tlvish y))
  (ensures (Seq.length y > 0 /\
    (PSL.tlv_size (Seq.append y x) == Some (Seq.length y) \/ PSL.tlv_size (Seq.append y x) == None)))
= Classical.forall_intro_2 (fun id c -> tlv_enc_ext id c x);
  Classical.move_requires (tlv_size_ext y) x;
  Classical.move_requires tlv_ne y

let tlvish_inv (#t: Type) (pp: asn1_strong_parser t) (y x: bytes)
: Lemma (requires (tlv_shaped pp /\ tlvish y /\ ~ (acc #asn1_strong_parser_kind pp y)))
  (ensures (None? (SB.parse pp (Seq.append y x))))
= tlvish_ext y x;
  let b = Seq.append y x in
  match SB.parse pp b with
  | None -> ()
  | Some (_, n) ->
    assert (PSL.tlv_size b == Some n);
    slice_append_prefix y x;
    strong_prefix_down pp y b n

#push-options "--fuel 2 --ifuel 1 --z3rlimit 32"
let rec list_invalid (#t: Type) (pp: asn1_strong_parser t) (ld: list bytes) (y: bytes) (tl: list bytes)
: Lemma (requires (all_eacc pp ld /\ tlv_shaped pp /\ tlvish y /\ ~ (acc #asn1_strong_parser_kind pp y)))
  (ensures (None? (SB.parse (parse_list pp) (W.enc_list RR.id_enc (List.Tot.append ld (y :: tl))))))
  (decreases ld)
= match ld with
  | [] ->
    let bt = W.enc_list RR.id_enc tl in
    let b = W.enc_list RR.id_enc (y :: tl) in
    assert (b == Seq.append y bt);
    tlvish_inv pp y bt;
    tlvish_ext y bt;
    tot_parse_list_eq pp b
  | a :: q ->
    list_invalid pp q y tl;
    let b = W.enc_list RR.id_enc (List.Tot.append ld (y :: tl)) in
    let bq = W.enc_list RR.id_enc (List.Tot.append q (y :: tl)) in
    assert (b == Seq.append a bq);
    assert (Seq.equal (Seq.slice b (Seq.length a) (Seq.length b)) bq);
    strong_ext #asn1_strong_parser_kind pp a bq;
    tot_parse_list_eq pp b
#pop-options

let sized_list_none (ne: bool) (#t: Type) (pp: asn1_strong_parser t) (b: bytes)
: Lemma (requires (None? (SB.parse (parse_list pp) b)))
  (ensures (~ (acc #asn1_weak_parser_kind (parse_sized_list ne pp) b)))
= parse_filter_eq (parse_list pp) (list_size_ok ne) b

let sized_list_empty (#t: Type) (pp: asn1_strong_parser t) (b: bytes)
: Lemma (requires (Seq.length b == 0))
  (ensures (~ (acc #asn1_weak_parser_kind (parse_sized_list true pp) b)))
= tot_parse_list_eq pp b;
  parse_filter_eq (parse_list pp) (list_size_ok true) b

let p_raw_tlvish (w y: bytes)
: Lemma (requires (match SB.parse RR.p_raw w with Some (y', n) -> y' == y /\ n == Seq.length w | None -> False))
  (ensures (tlvish y))
= RR.any_enc_injective ();
  LowParse.Spec.Combinators.parse_synth_eq RR.p_any RR.any_enc w;
  tlv_shaped_k' ASN1_ANY_ILC w;
  ASN1.Spec.Serializer.asn1_as_parser_consumed ASN1_ANY_ILC w;
  assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

(* SET OF: converses. An accepted element is one frame, so that the
   runtime frame check is not needed. If all the elements are one TLV,
   then their sorted concatenation is a concatenation of all of them in
   some order (`sort_acc_l`), which is rejected as soon as one of them
   is. *)

let frame_len_tlv_size (b: bytes)
: Lemma (SI.frame_len b == (match PSL.tlv_size b with Some n -> if n <= Seq.length b then n else 0 | None -> 0))
= match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (_, n1) -> ILC.length_eq (Seq.slice b n1 (Seq.length b))

let acc_frame (#t: Type) (pp: asn1_strong_parser t) (b: bytes)
: Lemma (requires (tlv_shaped pp /\ acc #asn1_strong_parser_kind pp b))
  (ensures (SI.frame_len b == Seq.length b /\ Seq.length b > 0))
= assert (match SB.parse pp b with Some (_, n) -> PSL.tlv_size b == Some n | None -> True);
  tlv_ne b;
  frame_len_tlv_size b

let rec all_tlvish (l: list bytes) : prop =
  match l with
  | [] -> True
  | a :: q -> tlvish a /\ all_tlvish q

let rec has_bad (#t: Type) (pp: asn1_strong_parser t) (l: list bytes) : prop =
  match l with
  | [] -> False
  | a :: q -> ~ (acc #asn1_strong_parser_kind pp a) \/ has_bad pp q

let rec all_tlvish_snoc (l: list bytes) (y: bytes)
: Lemma (requires (all_tlvish l /\ tlvish y)) (ensures (all_tlvish (List.Tot.append l [y])))
= match l with
  | [] -> ()
  | _ :: q -> all_tlvish_snoc q y

let rec has_bad_snoc (#t: Type) (pp: asn1_strong_parser t) (l: list bytes) (y: bytes)
: Lemma (has_bad pp (List.Tot.append l [y]) <==> (has_bad pp l \/ ~ (acc #asn1_strong_parser_kind pp y)))
= match l with
  | [] -> ()
  | _ :: q -> has_bad_snoc pp q y

let rec ins_l (lt: SI.lt_t) (e: bytes) (l: list bytes) : GTot (list bytes) (decreases l) =
  match l with
  | [] -> [e]
  | a :: q ->
    if PSL.tlv_size (Seq.append a (W.enc_list RR.id_enc q)) = Some (Seq.length a) && lt a e
    then a :: ins_l lt e q
    else e :: l

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"
let rec ins_enc (#t: Type) (pp: asn1_strong_parser t) (lt: SI.lt_t) (e: bytes) (l: list bytes)
: Lemma (requires (tlvish e /\ all_tlvish l))
  (ensures (SI.ins lt e (W.enc_list RR.id_enc l) == W.enc_list RR.id_enc (ins_l lt e l) /\
    all_tlvish (ins_l lt e l) /\
    (has_bad pp (ins_l lt e l) <==> (~ (acc #asn1_strong_parser_kind pp e) \/ has_bad pp l))))
  (decreases l)
= let r = W.enc_list RR.id_enc l in
  SI.ins_unfold lt e r;
  match l with
  | [] -> ()
  | a :: q ->
    let rq = W.enc_list RR.id_enc q in
    assert (r == Seq.append a rq);
    tlvish_ext a rq;
    frame_len_tlv_size r;
    if PSL.tlv_size r = Some (Seq.length a)
    then begin
      Seq.append_slices a rq;
      assert (SI.frame_len r == Seq.length a);
      assert (Seq.slice r 0 (Seq.length a) == a);
      assert (Seq.slice r (Seq.length a) (Seq.length r) == rq);
      if lt a e
      then ins_enc pp lt e q
      else ()
    end
    else assert (SI.frame_len r == 0)
#pop-options

let rec sort_acc_l (lt: SI.lt_t) (la: list bytes) (l: list bytes) : GTot (list bytes) (decreases l) =
  match l with
  | [] -> la
  | a :: q -> sort_acc_l lt (ins_l lt a la) q

#push-options "--fuel 2 --ifuel 1"
let rec sort_enc (#t: Type) (pp: asn1_strong_parser t) (lt: SI.lt_t) (la: list bytes) (l: list bytes)
: Lemma (requires (all_tlvish la /\ all_tlvish l))
  (ensures (SI.sort_acc lt RR.id_enc (W.enc_list RR.id_enc la) l == W.enc_list RR.id_enc (sort_acc_l lt la l) /\
    all_tlvish (sort_acc_l lt la l) /\
    (has_bad pp (sort_acc_l lt la l) <==> (has_bad pp la \/ has_bad pp l))))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    ins_enc pp lt a la;
    sort_enc pp lt (ins_l lt a la) q
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"
let rec sorted_aux_invalid (#t: Type) (tbo: bytes -> bytes -> bool) (pp: asn1_strong_parser t) (prev: bytes) (l: list bytes)
: Lemma (requires (tlv_shaped pp /\ all_tlvish l /\ has_bad pp l))
  (ensures (None? (Set.tot_parse_byte_sorted_list_aux tbo pp prev (W.enc_list RR.id_enc l))))
  (decreases l)
= match l with
  | a :: q ->
    let b = W.enc_list RR.id_enc l in
    let bq = W.enc_list RR.id_enc q in
    assert (b == Seq.append a bq);
    tlvish_ext a bq;
    if Sq.consumed #asn1_strong_parser_kind pp a = Some (Seq.length a)
    then begin
      strong_ext #asn1_strong_parser_kind pp a bq;
      Seq.append_slices a bq;
      sorted_aux_invalid tbo pp a q
    end
    else tlvish_inv pp a bq
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 64"
let set_invalid (ne: bool) (#t: Type) (pp: asn1_strong_parser t) (l: list bytes)
: Lemma (requires (tlv_shaped pp /\ all_tlvish l /\ has_bad pp l))
  (ensures (~ (acc #asn1_weak_parser_kind (parse_sized_set ne pp) (SI.sort_list SI.lt_lex RR.id_enc l))))
= sort_enc pp SI.lt_lex [] l;
  let l' = sort_acc_l SI.lt_lex [] l in
  let r = W.enc_list RR.id_enc l' in
  assert (SI.sort_list SI.lt_lex RR.id_enc l == r);
  let tbo : (x: bytes) -> (y: bytes) -> Pure bool True (fun z -> z == true <==> Set.prop_order_of_bool_order Set.lex_byte_order x y) =
    fun x1 x2 -> Set.lex_byte_order x1 x2
  in
  Set.tot_parse_byte_sorted_list_correct (Set.prop_order_of_bool_order Set.lex_byte_order) tbo pp r;
  set_of_eq pp r;
  match l' with
  | a :: q ->
    let bq = W.enc_list RR.id_enc q in
    assert (r == Seq.append a bq);
    tlvish_ext a bq;
    if Sq.consumed #asn1_strong_parser_kind pp a = Some (Seq.length a)
    then begin
      strong_ext #asn1_strong_parser_kind pp a bq;
      Seq.append_slices a bq;
      sorted_aux_invalid tbo pp a q
    end
    else tlvish_inv pp a bq
#pop-options

let set_empty (#t: Type) (pp: asn1_strong_parser t) (r: bytes)
: Lemma (requires (Seq.length r == 0))
  (ensures (~ (acc #asn1_weak_parser_kind (parse_sized_set true pp) r)))
= let tbo : (x: bytes) -> (y: bytes) -> Pure bool True (fun z -> z == true <==> Set.prop_order_of_bool_order Set.lex_byte_order x y) =
    fun x1 x2 -> Set.lex_byte_order x1 x2
  in
  Set.tot_parse_byte_sorted_list_correct (Set.prop_order_of_bool_order Set.lex_byte_order) tbo pp r;
  set_of_eq pp r;
  let p' = Set.tot_parse_byte_sorted_list Set.lex_byte_order pp in
  assert (SB.parse p' r == SB.parse (Set.parse_byte_sorted_list (Set.prop_order_of_bool_order Set.lex_byte_order) #_ #asn1_strong_parser_kind pp) r);
  assert (SB.parse (Set.parse_asn1_set_of pp) r == SB.parse p' r)
