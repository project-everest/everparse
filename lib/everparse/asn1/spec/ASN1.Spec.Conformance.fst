module ASN1.Spec.Conformance

(* Conformance of generic ASN.1 DER values to a schema, as a Boolean
   predicate on values.

   For every well-formed schema `k` (`wf k`), the typed parser
   `asn1_as_parser k` accepts exactly the inputs that the generic ANY parser
   `parse_asn1_value` accepts and whose resulting value `v` satisfies
   `conforms k v`, with the same number of consumed bytes
   (`conformance_correct` below.)

   The proof goes through soundness: every input accepted by a well-formed
   typed parser is accepted by the generic parser, with the same number of
   consumed bytes. Then, since the generic value determines its encoding
   (`ASN1.Spec.Value.Enc`), conformance is decided by the typed parser on
   that encoding. *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List
open LowParse.Tot.VLGen
open LowParse.Tot.Defaultable

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.Value
open ASN1.Spec.Value.Enc
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Spec.Any
open ASN1.Spec.Set
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.INTEGER

module RV = LowParse.Spec.RecursiveVLGen
module U32 = FStar.UInt32
module Seq = FStar.Seq

(* Generic acceptance *)

let list_ok (b: bytes) : GTot bool =
  Some? (parse (tot_parse_list pv) b)

let value_at (b: bytes) (n: nat) : GTot bool =
  match parse pv b with
  | Some (_, c) -> c = n
  | None -> false

let twin_at (id: asn1_id_t) (b: bytes) (n: nat) : GTot bool =
  match parse (parse_asn1_value_twin id) b with
  | Some (_, c) -> c = n
  | None -> false

(* After the identifier `id` has been read: one value, then a list of values,
   up to position `n` *)
let rest_ok (id: asn1_id_t) (b: bytes) (n: nat) : GTot bool =
  match parse (parse_asn1_value_twin id) b with
  | Some (_, c) -> c <= n && n <= Seq.length b && list_ok (Seq.slice b c n)
  | None -> false

let content_ok (id: asn1_id_t) (b: bytes) : GTot bool =
  if CONSTRUCTED? id.f
  then list_ok b
  else asn1_any_leaf_ok id b

(* Soundness of typed parsers *)

let sound (#k: parser_kind) (#t: Type) (p: parser k t) : prop =
  forall b. match parse p b with
  | Some (_, n) -> value_at b n == true
  | None -> True

let sound_twin (#k: parser_kind) (#t: Type) (fp: asn1_id_t -> parser k t) : prop =
  forall id b. match parse (fp id) b with
  | Some (_, n) -> twin_at id b n == true
  | None -> True

let content_sound (id: asn1_id_t) (#k: parser_kind) (#t: Type) (p: parser k t) : prop =
  forall b. Seq.length b < 4294967296 ==> (match parse p b with
  | Some (_, n) -> n == Seq.length b ==> content_ok id b == true
  | None -> True)

(* Sequence contents, from the start (`None`) or after an identifier *)
let seq_sound (#k: parser_kind) (#t: Type) (p: parser k t) : prop =
  forall b. match parse p b with
  | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
  | None -> True

let seq_sound_twin (#k: parser_kind) (#t: Type) (fp: asn1_id_t -> parser k t) : prop =
  forall id b. match parse (fp id) b with
  | Some (_, n) -> rest_ok id b n == true
  | None -> True

(* The generic parser, as an identifier followed by its twin *)

let vlgen_eq
  (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: Lemma
  (parse (LowParse.Tot.VLGen.parse_vlgen_weak 0 4294967295 parse_asn1_length_u32_t p) b == (
    match parse parse_asn1_length_u32_t b with
    | None -> None
    | Some (len, sz) ->
      if Seq.length b < sz + U32.v len
      then None
      else match parse p (Seq.slice b sz (sz + U32.v len)) with
      | Some (x, c) -> if c = U32.v len then Some (x, sz + U32.v len) else None
      | None -> None))
= ()

let twin_eq (id: asn1_any_id_t) (b: bytes)
: Lemma
  (parse (parse_asn1_value_twin id) b == (
    match parse parse_asn1_length_u32_t b with
    | None -> None
    | Some (len, sz) ->
      if Seq.length b < sz + U32.v len
      then None
      else match parse (RV.rec_vlgen_body asn1_value_param pv id) (Seq.slice b sz (sz + U32.v len)) with
      | Some (x, c) -> if c = U32.v len then Some (synth_asn1_value_twin id x, sz + U32.v len) else None
      | None -> None))
= parse_synth_eq (RV.rec_vlgen_payload_parser asn1_value_param pv id) (synth_asn1_value_twin id) b;
  vlgen_eq (RV.rec_vlgen_body asn1_value_param pv id) b

let slice_slice_3 (b: bytes) (c1 c2 len: nat)
: Lemma
  (requires (c1 + c2 + len <= Seq.length b))
  (ensures (Seq.slice (Seq.slice b c1 (Seq.length b)) c2 (c2 + len) == Seq.slice b (c1 + c2) (c1 + c2 + len)))
= Seq.slice_slice b c1 (Seq.length b) c2 (c2 + len)

private
let slice_from_slice (b: bytes) (c1 c2 n: nat)
: Lemma
  (requires (c1 <= n /\ c2 <= n - c1 /\ n <= Seq.length b))
  (ensures (Seq.slice (Seq.slice b c1 (Seq.length b)) c2 (n - c1) == Seq.slice b (c1 + c2) n))
= Seq.slice_slice b c1 (Seq.length b) c2 (n - c1)

private
let twin_at_some (id: asn1_id_t) (b1: bytes) (n2: nat) (len: U32.t) (c2: nat)
: Lemma
  (requires (twin_at id b1 n2 /\ c2 <= Seq.length b1 /\ parse parse_asn1_length_u32_t b1 == Some (len, c2)))
  (ensures (asn1_any_id_valid id /\ c2 + U32.v len == n2 /\ n2 <= Seq.length b1 /\
    (match parse (RV.rec_vlgen_body asn1_value_param pv id) (Seq.slice b1 c2 n2) with
     | Some (_, c) -> c == U32.v len
     | None -> False)))
= if asn1_any_id_valid id then twin_eq id b1

private
let twin_at_len (id: asn1_id_t) (b1: bytes) (n2: nat)
: Lemma
  (requires (twin_at id b1 n2))
  (ensures (asn1_any_id_valid id /\ Some? (parse parse_asn1_length_u32_t b1)))
= if asn1_any_id_valid id then twin_eq id b1

private
let any_identifier_of_u32 (b: bytes) (c1: nat) (id: asn1_id_t)
: Lemma
  (requires (c1 <= Seq.length b /\ parse parse_asn1_identifier_U32 b == Some (id, c1) /\ asn1_any_id_valid id))
  (ensures (parse parse_asn1_any_identifier b == Some ((id <: asn1_any_id_t), c1)))
= parse_any_identifier_consumed b

private
let value_at_intro (b: bytes) (id: asn1_any_id_t) (c1 c2 n2: nat) (len: U32.t)
: Lemma
  (requires (c1 <= Seq.length b /\ RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + c2, U32.v len) /\
    c2 + U32.v len == n2 /\ n2 <= Seq.length (Seq.slice b c1 (Seq.length b)) /\
    (match parse (RV.rec_vlgen_body asn1_value_param pv id) (Seq.slice (Seq.slice b c1 (Seq.length b)) c2 n2) with
     | Some (_, c) -> c == U32.v len
     | None -> False)))
  (ensures (value_at b (c1 + n2)))
= slice_slice_3 b c1 c2 (U32.v len);
  RV.parse_rec_vlgen_eq asn1_value_param b

private
let header_intro (b: bytes) (c1: nat) (id: asn1_any_id_t)
: Lemma
  (requires (c1 <= Seq.length b /\ parse parse_asn1_any_identifier b == Some (id, c1)))
  (ensures (match parse parse_asn1_length_u32_t (Seq.slice b c1 (Seq.length b)) with
    | Some (len, c2) -> RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + c2, U32.v len)
    | None -> True))
= ()

let value_of_twin (b: bytes) (c1: nat) (id: asn1_id_t) (n2: nat)
: Lemma
  (requires (c1 <= Seq.length b /\ parse parse_asn1_identifier_U32 b == Some (id, c1) /\ twin_at id (Seq.slice b c1 (Seq.length b)) n2))
  (ensures (value_at b (c1 + n2)))
= let b1 = Seq.slice b c1 (Seq.length b) in
  twin_at_len id b1 n2;
  any_identifier_of_u32 b c1 id;
  header_intro b c1 id;
  match parse parse_asn1_length_u32_t b1 with
  | Some (len, c2) ->
    twin_at_some id b1 n2 len c2;
    value_at_intro b id c1 c2 n2 len
  | None -> ()

let twin_at_valid (id: asn1_id_t) (b: bytes) (n: nat)
: Lemma
  (requires (twin_at id b n))
  (ensures (asn1_any_id_valid id))
= ()

(* Lists of generic values *)

let list_ok_empty (b: bytes)
: Lemma
  (requires (Seq.length b == 0))
  (ensures (list_ok b))
= tot_parse_list_eq pv b

let list_ok_consumes_all (b: bytes)
: Lemma
  (match parse (tot_parse_list pv) b with
   | Some (_, n) -> n == Seq.length b
   | None -> True)
= parser_kind_prop_equiv (parse_list_kind true) (tot_parse_list pv)

let value_at_pos (b: bytes) (n: nat)
: Lemma
  (requires (value_at b n))
  (ensures (n > 0 /\ n <= Seq.length b))
= parser_kind_prop_equiv (RV.rec_vlgen_kind asn1_value_param) pv

#push-options "--z3rlimit 32"
let list_ok_cons (b: bytes) (c n: nat)
: Lemma
  (requires (value_at b c /\ c <= n /\ n <= Seq.length b /\ list_ok (Seq.slice b c n)))
  (ensures (list_ok (Seq.slice b 0 n)))
= value_at_pos b c;
  let b' = Seq.slice b 0 n in
  parse_strong_prefix #(RV.rec_vlgen_kind asn1_value_param) pv b b';
  tot_parse_list_eq pv b';
  Seq.slice_slice b 0 n c n
#pop-options

let list_ok_twin (b: bytes) (c1: nat) (id: asn1_id_t) (n: nat)
: Lemma
  (requires (c1 <= n /\ n <= Seq.length b /\ parse parse_asn1_identifier_U32 b == Some (id, c1) /\ rest_ok id (Seq.slice b c1 (Seq.length b)) (n - c1)))
  (ensures (list_ok (Seq.slice b 0 n)))
= let b1 = Seq.slice b c1 (Seq.length b) in
  let Some (_, c2) = parse (parse_asn1_value_twin id) b1 in
  value_of_twin b c1 id c2;
  slice_from_slice b c1 c2 n;
  list_ok_cons b (c1 + c2) n

let list_ok_single (b: bytes)
: Lemma
  (requires (value_at b (Seq.length b)))
  (ensures (list_ok b))
= list_ok_empty (Seq.slice b (Seq.length b) (Seq.length b));
  list_ok_cons b (Seq.length b) (Seq.length b);
  Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b))

(* Length-prefixed contents *)

#push-options "--z3rlimit 32"
let lc_twin_at
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (c: bytes)
: Lemma
  (requires (asn1_any_id_valid id /\ content_sound id p))
  (ensures (match parse (parse_asn1_LC p) c with
    | Some (_, n) -> twin_at id c n == true
    | None -> True))
= vlgen_eq p c;
  twin_eq id c;
  match parse parse_asn1_length_u32_t c with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length c < sz + U32.v len
    then ()
    else begin
      let ct = Seq.slice c sz (sz + U32.v len) in
      match parse p ct with
      | Some (_, m) ->
        if m = U32.v len
        then begin
          assert (content_ok id ct);
          rec_vlgen_body_eq id ct;
          list_ok_consumes_all ct
        end
      | None -> ()
    end
#pop-options

let lc_sound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
: Lemma
  (requires (asn1_any_id_valid id /\ content_sound id p))
  (ensures (forall c. match parse (parse_asn1_LC p) c with
    | Some (_, n) -> twin_at id c n == true
    | None -> True))
= Classical.forall_intro (Classical.move_requires (lc_twin_at id p))

let ilc_twin_sound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
: Lemma
  (requires (asn1_any_id_valid id /\ content_sound id p))
  (ensures (sound_twin (parse_asn1_ILC_twin id p)))
= lc_sound id p

#push-options "--z3rlimit 32"
let ilc_value_at
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
  (b: bytes)
: Lemma
  (requires (asn1_any_id_valid id /\ content_sound id p))
  (ensures (match parse (parse_asn1_ILC id p) b with
    | Some (_, n) -> value_at b n == true
    | None -> True))
= let pf = parse_asn1_identifier_U32 `parse_filter` (fun id' -> id' = id) in
  parse_synth_eq (pf `nondep_then` parse_asn1_LC p) snd b;
  nondep_then_eq pf (parse_asn1_LC p) b;
  parse_filter_eq parse_asn1_identifier_U32 (fun id' -> id' = id) b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id', c1) ->
    if id' = id
    then begin
      let b1 = Seq.slice b c1 (Seq.length b) in
      lc_twin_at id p b1;
      match parse (parse_asn1_LC p) b1 with
      | Some (_, n2) -> value_of_twin b c1 id n2
      | None -> ()
    end
  | None -> ()
#pop-options

let ilc_sound
  (id: asn1_id_t)
  (#ack: asn1_content_k)
  (p: asn1_weak_parser (asn1_content_t ack))
: Lemma
  (requires (asn1_any_id_valid id /\ content_sound id p))
  (ensures (sound (parse_asn1_ILC id p)))
= Classical.forall_intro (Classical.move_requires (ilc_value_at id p))

(* Well-formed schemas: identifiers are valid, primitive/constructed flags
   match the contents, and the terminal type of a universal primitive
   identifier is that of the corresponding universal type *)

let leaf_compat (id: asn1_id_t) (k: asn1_terminal_k) : Tot bool =
  PRIMITIVE? id.f &&
  (match id with
   | MK_ASN1_ID UNIVERSAL _ v ->
     begin match asn1_universal_terminal v with
     | None -> true
     | Some (ASN1_INTEGER _) -> ASN1_INTEGER? k
     | Some k0 -> k0 = k
     end
   | _ -> true)

(* Primitive identifiers whose generic contents are arbitrary bytes (OCTET
   STRING, or a non-universal or unknown universal tag): they may encapsulate
   any DER value, e.g. X.509 extension values *)
let opaque_leaf (id: asn1_id_t) : Tot bool =
  PRIMITIVE? id.f &&
  (match id with
   | MK_ASN1_ID UNIVERSAL _ v ->
     begin match asn1_universal_terminal v with
     | None -> true
     | Some k0 -> k0 = ASN1_OCTETSTRING
     end
   | _ -> true)

let opaque_leaf_ok (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (opaque_leaf id /\ Seq.length b < 4294967296))
  (ensures (content_ok id b))
= match id with
  | MK_ASN1_ID UNIVERSAL _ v ->
    begin match asn1_universal_terminal v with
    | Some _ -> ()
    | None -> ()
    end
  | _ -> ()

let encap_ok (id: asn1_id_t) : Tot bool =
  CONSTRUCTED? id.f || opaque_leaf id

let rec wf_terminal (id: asn1_id_t) (k: asn1_terminal_k) : Tot bool (decreases k) =
  asn1_any_id_valid id &&
  (match k with
   | ASN1_PREFIXED_TERMINAL id2 k2 -> encap_ok id && wf_terminal id2 k2
   | _ -> leaf_compat id k)

(* Terminals *)

let terminal_universal_parser_eq (k: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (not (ASN1_PREFIXED_TERMINAL? k)))
  (ensures (parse (asn1_universal_terminal_parser k) b == parse (asn1_terminal_as_parser k) b))
= match k with
  | ASN1_BOOLEAN -> ()
  | ASN1_INTEGER _ -> ()
  | ASN1_BITSTRING -> ()
  | ASN1_OCTETSTRING -> ()
  | ASN1_PRINTABLESTRING -> ()
  | ASN1_UTF8STRING -> ()
  | ASN1_IA5STRING -> ()
  | ASN1_VISIBLESTRING -> ()
  | ASN1_BMPSTRING -> ()
  | ASN1_UNIVERSALSTRING -> ()
  | ASN1_TELETEXSTRING -> ()
  | ASN1_NUMERICSTRING -> ()
  | ASN1_VIDEOTEXSTRING -> ()
  | ASN1_GRAPHICSTRING -> ()
  | ASN1_GENERALSTRING -> ()
  | ASN1_OBJECTDESCRIPTOR -> ()
  | ASN1_RELATIVE_OID -> ()
  | ASN1_OID_IRI -> ()
  | ASN1_RELATIVE_OID_IRI -> ()
  | ASN1_DATE -> ()
  | ASN1_TIME_OF_DAY -> ()
  | ASN1_DATE_TIME -> ()
  | ASN1_NULL -> ()
  | ASN1_OID -> ()
  | ASN1_UTCTIME -> ()
  | ASN1_GENERALIZEDTIME -> ()

let integer_bound_weaken (bound: pos) (b: bytes)
: Lemma
  (requires (Seq.length b < 4294967296 /\ (match parse (parse_untagged_bounded_integer bound) b with Some (_, n) -> n == Seq.length b | None -> False)))
  (ensures (match parse (parse_untagged_bounded_integer asn1_any_integer_bound) b with Some (_, n) -> n == Seq.length b | None -> False))
= ()

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
let terminal_leaf (id: asn1_id_t) (k: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (leaf_compat id k /\ not (ASN1_PREFIXED_TERMINAL? k) /\ Seq.length b < 4294967296 /\
    (match parse (asn1_terminal_as_parser k) b with Some (_, n) -> n == Seq.length b | None -> False)))
  (ensures (content_ok id b))
= match id with
  | MK_ASN1_ID UNIVERSAL _ v ->
    begin match asn1_universal_terminal v with
    | None -> ()
    | Some (ASN1_INTEGER bound0) ->
      let ASN1_INTEGER bound = k in
      integer_bound_weaken bound b
    | Some k0 ->
      terminal_universal_parser_eq k b
    end
  | _ -> ()
#pop-options

let terminal_sound_post (id: asn1_id_t) (k: asn1_terminal_k) (b: bytes) : prop =
  Seq.length b < 4294967296 ==> (match parse (asn1_terminal_as_parser k) b with
    | Some (_, n) -> n == Seq.length b ==> content_ok id b == true
    | None -> True)

private
let terminal_sound_leaf (id: asn1_id_t) (k: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (wf_terminal id k /\ ~ (ASN1_PREFIXED_TERMINAL? k)))
  (ensures (terminal_sound_post id k b))
= match parse (asn1_terminal_as_parser k) b with
  | Some (_, n) -> if n = Seq.length b && Seq.length b < 4294967296 then terminal_leaf id k b
  | None -> ()

private
let terminal_sound_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (wf_terminal id (ASN1_PREFIXED_TERMINAL id2 k2) /\ (forall b' . terminal_sound_post id2 k2 b')))
  (ensures (terminal_sound_post id (ASN1_PREFIXED_TERMINAL id2 k2) b))
= ilc_value_at id2 #(ASN1_TERMINAL k2) (asn1_terminal_as_parser k2) b;
  match parse (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) b with
  | Some (_, n) ->
    if n = Seq.length b && Seq.length b < 4294967296 then
      (if CONSTRUCTED? id.f then list_ok_single b else opaque_leaf_ok id b)
  | None -> ()

let rec terminal_sound_at (id: asn1_id_t) (k: asn1_terminal_k) (b: bytes)
: Lemma
  (requires (wf_terminal id k))
  (ensures (terminal_sound_post id k b))
  (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    Classical.forall_intro (Classical.move_requires (terminal_sound_at id2 k2));
    terminal_sound_prefixed id id2 k2 b
  | _ -> terminal_sound_leaf id k b

let terminal_sound (id: asn1_id_t) (k: asn1_terminal_k)
: Lemma
  (requires (wf_terminal id k))
  (ensures (content_sound id (asn1_terminal_as_parser k)))
= Classical.forall_intro (Classical.move_requires (terminal_sound_at id k))

(* SEQUENCE OF, SET OF *)

let rec list_sound_at (#t: Type) (p: asn1_strong_parser t) (b: bytes)
: Lemma
  (requires (sound p))
  (ensures (match parse (parse_list p) b with
    | Some (_, n) -> list_ok b == true
    | None -> True))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then list_ok_empty b
  else match parse p b with
  | None -> tot_parse_list_eq p b
  | Some (_, c) ->
    if c = 0
    then tot_parse_list_eq p b
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      list_sound_at p b';
      tot_parse_list_eq p b;
      assert (value_at b c);
      if Some? (parse (parse_list p) b)
      then begin
        list_ok_cons b c (Seq.length b);
        Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b))
      end
    end

let sized_list_sound (ne: bool) (#t: Type) (p: asn1_strong_parser t)
: Lemma
  (requires (sound p))
  (ensures (forall b. match parse (parse_sized_list ne p) b with
    | Some (_, n) -> list_ok b == true
    | None -> True))
= let prf (b: bytes) : Lemma (match parse (parse_sized_list ne p) b with
    | Some (_, n) -> list_ok b == true
    | None -> True)
  = parse_filter_eq (parse_list p) (list_size_ok ne) b;
    list_sound_at p b
  in
  Classical.forall_intro prf

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let rec sorted_list_aux_sound
  (ord: (bytes -> bytes -> bool))
  (#t: Type) (p: asn1_strong_parser t)
  (prev: bytes) (b: bytes)
: Lemma
  (requires (sound p))
  (ensures (match tot_parse_byte_sorted_list_aux ord p prev b with
    | Some (_, n) -> list_ok b == true
    | None -> True))
  (decreases (Seq.length b))
= tot_parse_list_eq pv b;
  if Seq.length b = 0
  then ()
  else match parse p b with
  | None -> ()
  | Some (_, c) ->
    if c = 0 then ()
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      assert (Seq.length b' < Seq.length b);
      sorted_list_aux_sound ord p (Seq.slice b 0 c) b'
    end

let sorted_list_sound
  (ord: (bytes -> bytes -> bool))
  (#t: Type) (p: asn1_strong_parser t)
  (b: bytes)
: Lemma
  (requires (sound p))
  (ensures (match tot_parse_byte_sorted_list_bare ord p b with
    | Some (_, n) -> list_ok b == true
    | None -> True))
= tot_parse_list_eq pv b;
  if Seq.length b = 0
  then ()
  else match parse p b with
  | None -> ()
  | Some (_, c) ->
    if c = 0 then ()
    else begin
      let b' = Seq.slice b c (Seq.length b) in
      assert (Seq.length b' < Seq.length b);
      sorted_list_aux_sound ord p (Seq.slice b 0 c) b'
    end

#pop-options

let sized_set_sound (ne: bool) (#t: Type) (p: asn1_strong_parser t)
: Lemma
  (requires (sound p))
  (ensures (forall b. match parse (parse_sized_set ne p) b with
    | Some (_, n) -> list_ok b == true
    | None -> True))
= let prf (b: bytes) : Lemma (match parse (parse_sized_set ne p) b with
    | Some (_, n) -> list_ok b == true
    | None -> True)
  = parse_filter_eq (parse_asn1_set_of p) (list_size_ok ne) b;
    Classical.forall_intro (fun ord -> Classical.move_requires (sorted_list_sound ord p) b)
  in
  Classical.forall_intro prf

(* CHOICE *)

let twin_sound_for (x: asn1_id_t) (#k: parser_kind) (#t: Type) (p: parser k t) : prop =
  forall c. match parse p c with
  | Some (_, n) -> twin_at x c n == true
  | None -> True

let rec choice_entries_ok (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind)) : Tot prop (decreases lp) =
  match lp with
  | [] -> True
  | (x, gp) :: tl -> twin_sound_for x (Mkgenparser?.p gp) /\ choice_entries_ok tl

let synth_consumed
  (#k: parser_kind) (#t1 #t2: Type) (p: parser k t1) (f: t1 -> Tot t2) (b: bytes)
: Lemma
  (requires (synth_injective f))
  (ensures (match parse (parse_synth p f) b, parse p b with
    | Some (_, n1), Some (_, n2) -> n1 == n2
    | None, None -> True
    | _ -> False))
  [SMTPat (parse (parse_synth p f) b)]
= parse_synth_eq p f b

let rec choice_payload_at
  (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind))
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (requires (choice_entries_ok lp))
  (ensures (match parse (make_gen_choice_strong_payload_parser lp id) b with
    | Some (_, n) -> twin_at id b n == true
    | None -> True))
  (decreases lp)
= match lp with
  | [] -> ()
  | (x, gp) :: tl ->
    if id = x
    then parse_synth_eq (Mkgenparser?.p gp) (attach_tag lp id) b
    else begin
      choice_payload_at tl id b
    end

(* SEQUENCE items *)

let filter_consumed
  (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bool) (b: bytes)
: Lemma
  (match parse (parse_filter p f) b, parse p b with
    | Some (_, n1), Some (_, n2) -> n1 == n2
    | None, _ -> True
    | _ -> False)
  [SMTPat (parse (parse_filter p f) b)]
= parse_filter_eq p f b

let rec items_sound (its: list gen_decorated_parser_twin) : Tot prop (decreases its) =
  match its with
  | [] -> True
  | hd :: tl -> sound_twin (Mkgendcparser?.fp hd) /\ items_sound tl

#push-options "--z3rlimit 32 --fuel 1 --ifuel 2"
let item_twin_at (item: gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (sound_twin (Mkgendcparser?.fp item)))
  (ensures (match parse (parse_asn1_sequence_item_twin item id) b with
    | Some (_, n) -> twin_at id b n == true
    | None -> True))
= match item with
  | Mkgendcparser d p fp ->
    let (| _, _, dk |) = d in
    assert (match parse (fp id) b with Some (_, n) -> twin_at id b n == true | None -> True)
#pop-options

let rest_ok_twin (id: asn1_id_t) (b: bytes) (n: nat)
: Lemma
  (requires (twin_at id b n /\ n <= Seq.length b))
  (ensures (rest_ok id b n))
= list_ok_empty (Seq.slice b n n)

let rest_ok_cons (id: asn1_id_t) (b: bytes) (c n: nat)
: Lemma
  (requires (twin_at id b c /\ c <= n /\ n <= Seq.length b /\ list_ok (Seq.slice (Seq.slice b c (Seq.length b)) 0 (n - c))))
  (ensures (rest_ok id b n))
= slice_from_slice b c 0 n;
  match parse (parse_asn1_value_twin id) b with
  | Some (_, c') -> assert (c' == c)
  | None -> ()

let list_ok_slice_0 (b: bytes) (n: nat)
: Lemma
  (requires (n == Seq.length b /\ list_ok b))
  (ensures (list_ok (Seq.slice b 0 n)))
= Seq.lemma_eq_elim b (Seq.slice b 0 n)

(* Unfolding the SEQUENCE machine *)

let seq'_unfold (its: list gen_decorated_parser_twin) (st: option asn1_id_t)
: Lemma (make_asn1_sequence_parser' its st == make_asn1_sequence_parser_guard its make_asn1_sequence_parser'' st)
= assert (make_asn1_sequence_parser' its st == make_asn1_sequence_parser_guard its make_asn1_sequence_parser'' st) by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser']; zeta; iota]; FStar.Tactics.trefl ())

let seq''_unfold (its: list gen_decorated_parser_twin {Cons? its}) (st: option asn1_id_t)
: Lemma (make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
   make_asn1_sequence_parser'' its st == make_asn1_sequence_parser_body (make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser') st)
= make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  assert (make_asn1_sequence_parser'' its st == make_asn1_sequence_parser_body (make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser') st) by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser'']; zeta; iota]; FStar.Tactics.trefl ())

let olen (#t: Type) (#b: bytes) (r: option (t & consumed_length b)) : Tot (option nat) =
  match r with None -> None | Some (_, n) -> Some n

#push-options "--fuel 1 --ifuel 2 --z3rlimit 64"
let body_twin_eq (its: list gen_decorated_parser_twin {Cons? its}) (id: asn1_id_t) (b: bytes)
: Lemma (
    let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
    match its with
    | [hd] -> olen (parse (pbt id) b) == olen (parse (parse_asn1_sequence_item_twin hd id) b)
    | hd :: tl ->
      let Mkgendcparser d _ _ = hd in
      let (| s, de, _ |) = d in
      if FStar.Set.mem id s
      then olen (parse (pbt id) b) == olen (parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_parser' tl None) b)
      else match de with
      | PLAIN -> parse (pbt id) b == None
      | _ -> (match generate_defaultable_item hd with
        | Some defv -> olen (parse (pbt id) b) == olen (parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_parser' tl (Some id)) b)
        | None -> False))
= let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  match its with
  | [hd] -> 
    assert (olen (parse (pbt id) b) == olen (parse (parse_asn1_sequence_item_twin hd id) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota])
  | hd :: tl ->
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    if FStar.Set.mem id s
    then
      assert (olen (parse (pbt id) b) == olen (parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_parser' tl None) b))
        by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota])
    else match de with
    | PLAIN ->
      assert (olen (parse (pbt id) b) == olen (parse (fail_parser asn1_strong_parser_kind (asn1_decorated_t d) `nondep_then` make_asn1_sequence_parser' tl None) b))
        by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota]);
      nondep_then_eq (fail_parser asn1_strong_parser_kind (asn1_decorated_t d)) (make_asn1_sequence_parser' tl None) b
    | _ -> 
      let Some defv = generate_defaultable_item hd in
      assert (olen (parse (pbt id) b) == olen (parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_parser' tl (Some id)) b))
        by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body_twin]; zeta; iota])
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 64"
let seq'_parse (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma (olen (parse (make_asn1_sequence_parser' its st) b) == (match its with
    | [] -> (match st with None -> Some 0 | Some _ -> None)
    | _ ->
      if None? st && Some? (generate_defaultable_items its) && Seq.length b = 0
      then Some 0
      else olen (parse (make_asn1_sequence_parser'' its st) b)))
= seq'_unfold its st;
  match its with
  | [] -> 
    assert (olen (parse (make_asn1_sequence_parser_guard its make_asn1_sequence_parser'' st) b) == (match st with None -> olen (parse parse_empty b) | Some _ -> None))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_guard]; zeta; iota])
  | _ ->
    let defv = match st with None -> generate_defaultable_items its | Some _ -> None in
    let p = make_asn1_sequence_parser'' its st in
    assert (olen (parse (make_asn1_sequence_parser_guard its make_asn1_sequence_parser'' st) b) == olen (parse (parse_defaultable defv p) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_guard]; zeta; iota]);
    parse_defaultable_eq #asn1_weak_parser_kind defv p b

let seq''_parse (its: list gen_decorated_parser_twin {Cons? its}) (st: option asn1_id_t) (b: bytes)
: Lemma (
    make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
    let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
    let k = glb asn1_strong_parser_kind parse_ret_kind in
    let p = match st with None -> weaken k parse_asn1_identifier_U32 | Some id -> weaken k (parse_ret id) in
    and_then_cases_injective pbt /\
    olen (parse (make_asn1_sequence_parser'' its st) b) == olen (parse (p `and_then` pbt) b))
= make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  seq''_unfold its st;
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  let p = match st with None -> weaken k parse_asn1_identifier_U32 | Some id -> weaken k (parse_ret id) in
  assert (olen (parse (make_asn1_sequence_parser_body pbt st) b) == olen (parse (p `and_then` pbt) b))
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser_body]; zeta; iota])
#pop-options

(* The SEQUENCE machine *)

let seq_post (st: option asn1_id_t) (b: bytes) (n: nat) : GTot bool =
  match st with
  | None -> n <= Seq.length b && list_ok (Seq.slice b 0 n)
  | Some id -> rest_ok id b n

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let rec seq_machine (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (items_sound its))
  (ensures (match parse (make_asn1_sequence_parser' its st) b with
    | Some (_, n) -> seq_post st b n == true
    | None -> True))
  (decreases %[its; 2])
= seq'_parse its st b;
  match its with
  | [] ->
    begin match st with
    | None -> list_ok_empty (Seq.slice b 0 0)
    | Some _ -> ()
    end
  | _ ->
    seq_body its st b;
    begin match st with
    | None ->
      if Seq.length b = 0 then list_ok_empty (Seq.slice b 0 0)
    | Some _ -> ()
    end

and seq_body (its: list gen_decorated_parser_twin) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_sound its))
  (ensures (match parse (make_asn1_sequence_parser'' its st) b with
    | Some (_, n) -> seq_post st b n == true
    | None -> True))
  (decreases %[its; 1])
= seq''_parse its st b;
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  match st with
  | None ->
    and_then_eq (weaken k parse_asn1_identifier_U32) pbt b;
    begin match parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, c1) ->
      let b1 = Seq.slice b c1 (Seq.length b) in
      seq_twin its id b1;
      match parse (pbt id) b1 with
      | None -> ()
      | Some (_, n1) -> list_ok_twin b c1 id (c1 + n1)
    end
  | Some id ->
    and_then_eq (weaken k (parse_ret id)) pbt b;
    Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
    seq_twin its id b

and seq_twin (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_sound its))
  (ensures (match parse (make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' id) b with
    | Some (_, n) -> rest_ok id b n == true
    | None -> True))
  (decreases %[its; 0])
= body_twin_eq its id b;
  match its with
  | [hd] ->
    item_twin_at hd id b;
    begin match parse (parse_asn1_sequence_item_twin hd id) b with
    | Some (_, n) -> rest_ok_twin id b n
    | None -> ()
    end
  | hd :: tl ->
    let Mkgendcparser d _ _ = hd in
    let (| s, de, dk |) = d in
    if FStar.Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_parser' tl None in
      nondep_then_eq p1 p2 b;
      item_twin_at hd id b;
      match parse p1 b with
      | None -> ()
      | Some (_, c) ->
        let b' = Seq.slice b c (Seq.length b) in
        seq_machine tl None b';
        match parse p2 b' with
        | None -> ()
        | Some (_, n2) -> rest_ok_cons id b c (c + n2)
    end
    else match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_parser' tl (Some id) in
      nondep_then_eq p1 p2 b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      seq_machine tl (Some id) b
#pop-options

(* Unfolding the ANY DEFINED BY machine *)

let any_guard_p (st: option asn1_id_t) : Tot (parser asn1_strong_parser_kind asn1_id_t) =
  match st with
  | Some id -> weaken asn1_strong_parser_kind (parse_ret id)
  | None -> weaken asn1_strong_parser_kind parse_asn1_identifier_U32

#push-options "--fuel 1 --ifuel 2 --z3rlimit 64"
let any'_parse (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) (b: bytes)
: Lemma (match its with
    | [] -> olen (parse (make_asn1_sequence_any_parser' its sfx st) b) == olen (parse (match st with Some id -> Mkparsertwin?.fp sfx id | None -> Mkparsertwin?.p sfx) b)
    | _ ->
      and_then_cases_injective (make_asn1_sequence_any_parser'' its sfx) /\
      olen (parse (make_asn1_sequence_any_parser' its sfx st) b) == olen (parse (any_guard_p st `and_then` make_asn1_sequence_any_parser'' its sfx) b))
= match its with
  | [] ->
    assert (olen (parse (make_asn1_sequence_any_parser' its sfx st) b) == olen (parse (match st with Some id -> Mkparsertwin?.fp sfx id | None -> Mkparsertwin?.p sfx) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser']; zeta; iota])
  | _ ->
    assert (olen (parse (make_asn1_sequence_any_parser' its sfx st) b) == olen (parse (make_asn1_sequence_any_parser_guard its (make_asn1_sequence_any_parser'' its sfx) st) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser']; zeta; iota]);
    assert (olen (parse (make_asn1_sequence_any_parser_guard its (make_asn1_sequence_any_parser'' its sfx) st) b) == olen (parse (any_guard_p st `and_then` make_asn1_sequence_any_parser'' its sfx) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_guard; `%any_guard_p]; zeta; iota])

let any''_parse (its: list gen_decorated_parser_twin {Cons? its}) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma (
    let hd :: tl = its in
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    let pb = make_asn1_sequence_any_parser'' its sfx id in
    if FStar.Set.mem id s
    then olen (parse pb b) == olen (parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' tl sfx None) b)
    else match de with
    | PLAIN -> parse pb b == None
    | _ -> (match generate_defaultable_item hd with
      | Some defv -> olen (parse pb b) == olen (parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' tl sfx (Some id)) b)
      | None -> False))
= let hd :: tl = its in
  let Mkgendcparser d _ _ = hd in
  let (| s, de, _ |) = d in
  let pb = make_asn1_sequence_any_parser'' its sfx id in
  assert (make_asn1_sequence_any_parser'' its sfx id == make_asn1_sequence_any_parser_body its (make_asn1_sequence_any_parser' (List.Tot.tl its) sfx) id)
    by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser'']; zeta; iota]; FStar.Tactics.trefl ());
  if FStar.Set.mem id s
  then
    assert (olen (parse pb b) == olen (parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' tl sfx None) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota])
  else match de with
  | PLAIN ->
    assert (olen (parse pb b) == olen (parse (fail_parser asn1_strong_parser_kind (asn1_decorated_t d) `nondep_then` make_asn1_sequence_any_parser' tl sfx None) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota]);
    nondep_then_eq (fail_parser asn1_strong_parser_kind (asn1_decorated_t d)) (make_asn1_sequence_any_parser' tl sfx None) b
  | _ ->
    let Some defv = generate_defaultable_item hd in
    assert (olen (parse pb b) == olen (parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' tl sfx (Some id)) b))
      by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_any_parser_body]; zeta; iota])
#pop-options

(* The ANY DEFINED BY machine, parametric in its suffix *)

let sfx_ok (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) : prop =
  seq_sound (Mkparsertwin?.p sfx) /\ seq_sound_twin (Mkparsertwin?.fp sfx)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let rec any_machine (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (st: option asn1_id_t) (b: bytes)
: Lemma
  (requires (items_sound its /\ sfx_ok sfx))
  (ensures (match parse (make_asn1_sequence_any_parser' its sfx st) b with
    | Some (_, n) -> seq_post st b n == true
    | None -> True))
  (decreases %[its; 1])
= any'_parse its sfx st b;
  match its with
  | [] -> ()
  | _ ->
    let pb = make_asn1_sequence_any_parser'' its sfx in
    match st with
    | None ->
      and_then_eq (any_guard_p None) pb b;
      begin match parse parse_asn1_identifier_U32 b with
      | None -> ()
      | Some (id, c1) ->
        let b1 = Seq.slice b c1 (Seq.length b) in
        any_twin its sfx id b1;
        match parse (pb id) b1 with
        | None -> ()
        | Some (_, n1) -> list_ok_twin b c1 id (c1 + n1)
      end
    | Some id ->
      and_then_eq (any_guard_p st) pb b;
      Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
      any_twin its sfx id b

and any_twin (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (Cons? its /\ items_sound its /\ sfx_ok sfx))
  (ensures (match parse (make_asn1_sequence_any_parser'' its sfx id) b with
    | Some (_, n) -> rest_ok id b n == true
    | None -> True))
  (decreases %[its; 0])
= any''_parse its sfx id b;
  let hd :: tl = its in
  let Mkgendcparser d _ _ = hd in
  let (| s, de, dk |) = d in
  if FStar.Set.mem id s
  then begin
    let p1 = parse_asn1_sequence_item_twin hd id in
    let p2 = make_asn1_sequence_any_parser' tl sfx None in
    nondep_then_eq p1 p2 b;
    item_twin_at hd id b;
    match parse p1 b with
    | None -> ()
    | Some (_, c) ->
      let b' = Seq.slice b c (Seq.length b) in
      any_machine tl sfx None b';
      match parse p2 b' with
      | None -> ()
      | Some (_, n2) -> rest_ok_cons id b c (c + n2)
  end
  else match de with
  | PLAIN -> ()
  | _ ->
    let Some defv = generate_defaultable_item hd in
    let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
    let p2 = make_asn1_sequence_any_parser' tl sfx (Some id) in
    nondep_then_eq p1 p2 b;
    Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
    any_machine tl sfx (Some id) b
#pop-options

(* The suffix: a key, then a choice of item sequences *)

let rec weak_entries_ok (#t: eqtype) (lc: list (t & gen_parser asn1_weak_parser_kind)) : Tot prop (decreases lc) =
  match lc with
  | [] -> True
  | (_, gp) :: tl -> seq_sound (Mkgenparser?.p gp) /\ weak_entries_ok tl

let rec weak_payload_ok (#t: eqtype) (lc: list (t & gen_parser asn1_weak_parser_kind)) (x: t) (b: bytes)
: Lemma
  (requires (weak_entries_ok lc))
  (ensures (match parse (make_gen_choice_weak_payload_parser lc x) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True))
  (decreases lc)
= match lc with
  | [] -> ()
  | (x', gp) :: tl ->
    if x = x'
    then parse_synth_eq (Mkgenparser?.p gp) (attach_tag lc x) b
    else weak_payload_ok tl x b

let rec weak_payload_fb_ok (#t: eqtype) (lc: list (t & gen_parser asn1_weak_parser_kind)) (fb: gen_parser asn1_weak_parser_kind) (x: t) (b: bytes)
: Lemma
  (requires (weak_entries_ok lc /\ seq_sound (Mkgenparser?.p fb)))
  (ensures (match parse (make_gen_choice_with_fallback_weak_payload_parser lc fb x) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True))
  (decreases lc)
= match lc with
  | [] -> parse_synth_eq (Mkgenparser?.p fb) (attach_tag_with_fallback lc fb x) b
  | (x', gp) :: tl ->
    if x = x'
    then parse_synth_eq (Mkgenparser?.p gp) (attach_tag_with_fallback lc fb x) b
    else weak_payload_fb_ok tl fb x b

let list_ok_cons2 (b: bytes) (c n2: nat)
: Lemma
  (requires (value_at b c /\ c + n2 <= Seq.length b /\ list_ok (Seq.slice (Seq.slice b c (Seq.length b)) 0 n2)))
  (ensures (list_ok (Seq.slice b 0 (c + n2))))
= Seq.slice_slice b c (Seq.length b) 0 n2;
  value_at_pos b c;
  list_ok_cons b c (c + n2)

#push-options "--z3rlimit 32"
let weak_choice_sound (#t: eqtype) (#k: parser_kind) (kp: parser k t) (lc: list (t & gen_parser asn1_weak_parser_kind)) (b: bytes)
: Lemma
  (requires (sound kp /\ weak_entries_ok lc))
  (ensures (match parse (make_gen_choice_weak_parser kp lc) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True))
= parse_tagged_union_eq kp (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc) b;
  match parse kp b with
  | None -> ()
  | Some (x, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    weak_payload_ok lc x b1;
    match parse (make_gen_choice_weak_payload_parser lc x) b1 with
    | None -> ()
    | Some (_, n2) -> list_ok_cons2 b c1 n2

let weak_choice_twin_sound (#t: eqtype) (#k: parser_kind) (kfp: asn1_id_t -> parser k t {and_then_cases_injective kfp}) (lc: list (t & gen_parser asn1_weak_parser_kind)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (sound_twin kfp /\ weak_entries_ok lc))
  (ensures (match parse (make_gen_choice_weak_parser_twin kfp lc id) b with
    | Some (_, n) -> rest_ok id b n == true
    | None -> True))
= parse_tagged_union_eq (kfp id) (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc) b;
  match parse (kfp id) b with
  | None -> ()
  | Some (x, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    weak_payload_ok lc x b1;
    match parse (make_gen_choice_weak_payload_parser lc x) b1 with
    | None -> ()
    | Some (_, n2) -> rest_ok_cons id b c1 (c1 + n2)

let weak_choice_fb_sound (#t: eqtype) (#k: parser_kind) (kp: parser k t) (lc: list (t & gen_parser asn1_weak_parser_kind)) (fb: gen_parser asn1_weak_parser_kind) (b: bytes)
: Lemma
  (requires (sound kp /\ weak_entries_ok lc /\ seq_sound (Mkgenparser?.p fb)))
  (ensures (match parse (make_gen_choice_with_fallback_weak_parser kp lc fb) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True))
= parse_tagged_union_eq kp (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb) b;
  match parse kp b with
  | None -> ()
  | Some (x, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    weak_payload_fb_ok lc fb x b1;
    match parse (make_gen_choice_with_fallback_weak_payload_parser lc fb x) b1 with
    | None -> ()
    | Some (_, n2) -> list_ok_cons2 b c1 n2

let weak_choice_fb_twin_sound (#t: eqtype) (#k: parser_kind) (kfp: asn1_id_t -> parser k t {and_then_cases_injective kfp}) (lc: list (t & gen_parser asn1_weak_parser_kind)) (fb: gen_parser asn1_weak_parser_kind) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (sound_twin kfp /\ weak_entries_ok lc /\ seq_sound (Mkgenparser?.p fb)))
  (ensures (match parse (make_gen_choice_with_fallback_weak_parser_twin kfp lc fb id) b with
    | Some (_, n) -> rest_ok id b n == true
    | None -> True))
= parse_tagged_union_eq (kfp id) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb) b;
  match parse (kfp id) b with
  | None -> ()
  | Some (x, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    weak_payload_fb_ok lc fb x b1;
    match parse (make_gen_choice_with_fallback_weak_payload_parser lc fb x) b1 with
    | None -> ()
    | Some (_, n2) -> rest_ok_cons id b c1 (c1 + n2)
#pop-options

(* CHOICE, top-level *)

#push-options "--z3rlimit 32"
let choice_sound_at (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind)) (b: bytes)
: Lemma
  (requires (choice_entries_ok lp))
  (ensures (match parse (make_gen_choice_strong_parser parse_asn1_identifier_U32 lp) b with
    | Some (_, n) -> value_at b n == true
    | None -> True))
= parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    choice_payload_at lp id b1;
    match parse (make_gen_choice_strong_payload_parser lp id) b1 with
    | None -> ()
    | Some (_, n2) -> value_of_twin b c1 id n2

let choice_twin_at (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind)) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (choice_entries_ok lp))
  (ensures (match parse (parse_tagged_union_payload (project_tags lp) (make_gen_choice_strong_payload_parser lp) id) b with
    | Some (_, n) -> twin_at id b n == true
    | None -> True))
= parse_synth_eq (make_gen_choice_strong_payload_parser lp id) (synth_tagged_union_data (project_tags lp) id) b;
  choice_payload_at lp id b
#pop-options

(* Content-level helpers *)

let content_sound_filter (id: asn1_id_t) (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bool)
: Lemma
  (requires (content_sound id p))
  (ensures (content_sound id (parse_filter p f)))
= ()

let content_sound_list (id: asn1_id_t) (#k: parser_kind) (#t: Type) (p: parser k t)
: Lemma
  (requires (CONSTRUCTED? id.f /\ (forall b. match parse p b with Some (_, n) -> list_ok (Seq.slice b 0 n) == true | None -> True)))
  (ensures (content_sound id p))
= let prf (b: bytes) : Lemma (Seq.length b < 4294967296 ==> (match parse p b with
    | Some (_, n) -> n == Seq.length b ==> content_ok id b == true
    | None -> True))
  = Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b))
  in
  Classical.forall_intro prf

let content_sound_single (id: asn1_id_t) (#k: parser_kind) (#t: Type) (p: parser k t)
: Lemma
  (requires (encap_ok id /\ sound p))
  (ensures (content_sound id p))
= let prf (b: bytes) : Lemma (Seq.length b < 4294967296 ==> (match parse p b with
    | Some (_, n) -> n == Seq.length b ==> content_ok id b == true
    | None -> True))
  = match parse p b with
    | Some (_, n) ->
      if n = Seq.length b && Seq.length b < 4294967296 then
        (if CONSTRUCTED? id.f then list_ok_single b else opaque_leaf_ok id b)
    | None -> ()
  in
  Classical.forall_intro prf

let content_sound_seq_of (id: asn1_id_t) (#k: parser_kind) (#t: Type) (p: parser k t)
: Lemma
  (requires (CONSTRUCTED? id.f /\ (forall b. match parse p b with Some (_, n) -> list_ok b == true | None -> True)))
  (ensures (content_sound id p))
= ()

(* Well-formed schemas *)

let rec wf_content (id: asn1_id_t) (k: asn1_content_k) : Tot bool (decreases k) =
  asn1_any_id_valid id &&
  (match k with
   | ASN1_RESTRICTED_TERMINAL k' _ -> wf_terminal id k'
   | ASN1_TERMINAL k' -> wf_terminal id k'
   | ASN1_SEQUENCE gitems -> CONSTRUCTED? id.f && wf_items (dsnd gitems)
   | ASN1_SET _ items _ -> CONSTRUCTED? id.f && wf_items items
   | ASN1_SEQUENCE_OF _ k' -> CONSTRUCTED? id.f && wf k'
   | ASN1_SET_OF _ k' -> CONSTRUCTED? id.f && wf k'
   | ASN1_PREFIXED k' -> encap_ok id && wf k'
   | ASN1_ANY_DEFINED_BY _ prefix kid key_k ls ofb _ _ ->
     CONSTRUCTED? id.f && wf_items prefix && wf_terminal kid key_k && wf_ls ls &&
     (match ofb with None -> true | Some gitems -> wf_items (dsnd gitems)))

and wf_ls (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot bool (decreases ls) =
  match ls with
  | [] -> true
  | (_, y) :: tl -> wf_items (dsnd y) && wf_ls tl

and wf_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (x, y) :: tl -> wf_content x y && wf_lc tl

and wf (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC id k' -> wf_content id k'
  | ASN1_CHOICE_ILC lc _ -> wf_lc lc
  | ASN1_ANY_ILC -> true

and wf_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> wf k
  | ASN1_OPTION_ILC k -> wf k
  | ASN1_DEFAULT_TERMINAL id #k _ -> wf_terminal id k
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k _ _ -> wf_terminal id k

and wf_items (#ids: _) (ls: asn1_gen_items_l ids) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> wf_dec dk && wf_items tl

(* Soundness of the typed parsers of well-formed schemas *)

let seq_parser_sound (its: list gen_decorated_parser_twin)
: Lemma
  (requires (items_sound its))
  (ensures (seq_sound (make_asn1_sequence_parser its)))
= let prf (b: bytes) : Lemma (match parse (make_asn1_sequence_parser its) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True)
  = seq_machine its None b
  in
  Classical.forall_intro prf

let any_parser_sound (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
: Lemma
  (requires (items_sound its /\ sfx_ok sfx))
  (ensures (seq_sound (make_asn1_sequence_any_parser its sfx)))
  [SMTPat (seq_sound (make_asn1_sequence_any_parser its sfx))]
= let prf (b: bytes) : Lemma (match parse (make_asn1_sequence_any_parser its sfx) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True)
  = any_machine its sfx None b
  in
  Classical.forall_intro prf

(* SET components *)

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let rec set_elem_twin_at (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (items_sound its))
  (ensures (match parse (parse_set_elem_twin its id) b with
    | Some (_, n) -> twin_at id b n == true
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    if FStar.Set.mem id s
    then begin
      item_twin_at hd id b;
      parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b
    end
    else begin
      set_elem_twin_at tl id b;
      parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b
    end
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_elem_value_at (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_sound its))
  (ensures (match parse (parse_set_elem its) b with
    | Some (_, n) -> value_at b n == true
    | None -> True))
= parse_set_elem_twin_cases_injective its;
  and_then_eq parse_asn1_identifier_U32 (parse_set_elem_twin its) b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    set_elem_twin_at its id b1;
    (match parse (parse_set_elem_twin its id) b1 with
     | Some (_, n2) -> value_of_twin b c1 id n2
     | None -> ())
  | None -> ()
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_parser_sound (its: list gen_decorated_parser_twin)
: Lemma
  (requires (items_sound its))
  (ensures (seq_sound (make_asn1_set_parser its)))
= Classical.forall_intro (Classical.move_requires (set_elem_value_at its));
  assert (sound (parse_set_elem its));
  set_to_tuple_injective its;
  let pl = parse_list (parse_set_elem its) in
  let pf = pl `parse_filter` set_ok its in
  let prf (b: bytes) : Lemma (match parse (make_asn1_set_parser its) b with
    | Some (_, n) -> list_ok (Seq.slice b 0 n) == true
    | None -> True)
  = parse_synth_eq pf (set_to_tuple its) b;
    parse_filter_eq pl (set_ok its) b;
    list_sound_at (parse_set_elem its) b;
    parser_kind_prop_equiv (parse_list_kind true) pl;
    match parse pl b with
    | Some (_, n) -> list_ok_slice_0 b n
    | None -> ()
  in
  Classical.forall_intro prf
#pop-options

let value_sound () : Lemma (sound parse_asn1_value /\ sound_twin parse_asn1_value_twin) = ()

#push-options "--z3rlimit 128 --fuel 1 --ifuel 1"
let any_content_sound (id: asn1_id_t)
  (idp: id_decs) (prefix: asn1_gen_items_l idp) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (ofb: option asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) idp))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
: Lemma
  (requires (CONSTRUCTED? id.f /\
    items_sound (asn1_sequence_as_parser prefix) /\ wf_terminal kid key_k /\
    weak_entries_ok (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) /\
    (match ofb with None -> True | Some gitems -> items_sound (asn1_sequence_as_parser (dsnd gitems)))))
  (ensures (content_sound id (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf'))))
= let itemtwins = asn1_sequence_as_parser prefix in
  let tp = asn1_terminal_as_parser key_k in
  terminal_sound kid key_k;
  ilc_sound kid #(ASN1_TERMINAL key_k) tp;
  ilc_twin_sound kid #(ASN1_TERMINAL key_k) tp;
  let key_p = parse_asn1_ILC kid #(ASN1_TERMINAL key_k) tp in
  let _ = parser_asn1_ILC_twin_case_injective kid #(ASN1_TERMINAL key_k) tp in
  let key_fp = parse_asn1_ILC_twin kid #(ASN1_TERMINAL key_k) tp in
  let supported_p = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
  match ofb with
  | None ->
    Classical.forall_intro (weak_choice_sound key_p supported_p);
    Classical.forall_intro_2 (weak_choice_twin_sound key_fp supported_p);
    make_gen_choice_weak_parser_twin_and_then_cases_injective key_fp supported_p;
    assert (seq_sound (weaken asn1_weak_parser_kind (make_gen_choice_weak_parser key_p supported_p)));
    assert (seq_sound_twin (fun id -> weaken asn1_weak_parser_kind (make_gen_choice_weak_parser_twin key_fp supported_p id)));
    assert (seq_sound (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf')))
      by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser]; zeta; iota]);
    content_sound_list id (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls None pf pf'))
  | Some gitems ->
    let fallback_p = Mkgenparser _ (make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd gitems))) in
    seq_parser_sound (asn1_sequence_as_parser (dsnd gitems));
    Classical.forall_intro (weak_choice_fb_sound key_p supported_p fallback_p);
    Classical.forall_intro_2 (weak_choice_fb_twin_sound key_fp supported_p fallback_p);
    make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective key_fp supported_p fallback_p;
    assert (seq_sound (weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser key_p supported_p fallback_p)));
    assert (seq_sound_twin (fun id -> weaken asn1_weak_parser_kind (make_gen_choice_with_fallback_weak_parser_twin key_fp supported_p fallback_p id)));
    assert (seq_sound (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some gitems) pf pf')))
      by (FStar.Tactics.norm [delta_only [`%asn1_content_as_parser]; zeta; iota]);
    content_sound_list id (asn1_content_as_parser (ASN1_ANY_DEFINED_BY idp prefix kid key_k ls (Some gitems) pf pf'))
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec content_lemma (id: asn1_id_t) (k: asn1_content_k)
: Lemma
  (requires (wf_content id k))
  (ensures (content_sound id (asn1_content_as_parser k)))
  (decreases k)
= match k with
  | ASN1_RESTRICTED_TERMINAL k' r ->
    terminal_sound id k';
    content_sound_filter id (asn1_terminal_as_parser k') (restriction_pred r)
  | ASN1_TERMINAL k' -> terminal_sound id k'
  | ASN1_SEQUENCE gitems ->
    items_lemma (dsnd gitems);
    seq_parser_sound (asn1_sequence_as_parser (dsnd gitems));
    content_sound_list id (make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd gitems)))
  | ASN1_SET _ items _ ->
    items_lemma items;
    set_parser_sound (asn1_sequence_as_parser items);
    content_sound_list id (make_asn1_set_parser (asn1_sequence_as_parser items))
  | ASN1_SEQUENCE_OF ne k' ->
    top_lemma k';
    sized_list_sound ne (asn1_as_parser k')
  | ASN1_SET_OF ne k' ->
    top_lemma k';
    sized_set_sound ne (asn1_as_parser k')
  | ASN1_PREFIXED k' ->
    top_lemma k';
    content_sound_single id (asn1_as_parser k')
  | ASN1_ANY_DEFINED_BY idp prefix kid key_k ls ofb pf pf' ->
    items_lemma prefix;
    ls_lemma (asn1_terminal_t key_k) (key_of_lit key_k) ls;
    (match ofb with None -> () | Some gitems -> items_lemma (dsnd gitems));
    any_content_sound id idp prefix kid key_k ls ofb pf pf'

and ls_lemma (#lt: eqtype) (t: eqtype) (f: lt -> Tot t) (ls: list (lt & asn1_gen_items_lk))
: Lemma
  (requires (wf_ls ls))
  (ensures (weak_entries_ok (asn1_ls_as_parser t f ls)))
  (decreases ls)
= match ls with
  | [] -> ()
  | h :: tl ->
    let (_, y) = h in
    items_lemma (dsnd y);
    seq_parser_sound (asn1_sequence_as_parser (dsnd y));
    ls_lemma t f tl

and lc_lemma (lc: list (asn1_id_t & asn1_content_k))
: Lemma
  (requires (wf_lc lc))
  (ensures (choice_entries_ok (asn1_lc_as_parser lc)))
  (decreases lc)
= match lc with
  | [] -> ()
  | h :: tl ->
    let (x, y) = h in
    content_lemma x y;
    lc_sound x (asn1_content_as_parser y);
    lc_lemma tl

and top_lemma (#s: _) (k: asn1_k s)
: Lemma
  (requires (wf k))
  (ensures (sound (asn1_as_parser k) /\ sound_twin (snd (asn1_as_parser_twin k))))
  (decreases k)
= match k with
  | ASN1_ILC id k' ->
    content_lemma id k';
    ilc_sound id (asn1_content_as_parser k');
    ilc_twin_sound id (asn1_content_as_parser k')
  | ASN1_CHOICE_ILC lc pf ->
    lc_lemma lc;
    let lp = asn1_lc_as_parser lc in
    Classical.forall_intro (Classical.move_requires (choice_sound_at lp));
    Classical.forall_intro_2 (Classical.move_requires_2 (choice_twin_at lp))
  | ASN1_ANY_ILC -> value_sound ()

and dec_lemma (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma
  (requires (wf_dec dk))
  (ensures (sound_twin (Mkgendcparser?.fp (asn1_decorated_as_parser_twin dk))))
  (decreases dk)
= match dk with
  | ASN1_PLAIN_ILC k -> top_lemma k
  | ASN1_OPTION_ILC k -> top_lemma k
  | ASN1_DEFAULT_TERMINAL id #k _ ->
    terminal_sound id k;
    ilc_twin_sound id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r _ ->
    terminal_sound id k;
    content_sound_filter id (asn1_terminal_as_parser k) (restriction_pred r);
    ilc_twin_sound id #(ASN1_RESTRICTED_TERMINAL k r) (weaken _ ((asn1_terminal_as_parser k) `parse_filter` (restriction_pred r)))

and items_lemma (#ids: _) (ls: asn1_gen_items_l ids)
: Lemma
  (requires (wf_items ls))
  (ensures (items_sound (asn1_sequence_as_parser ls)))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    dec_lemma dk;
    items_lemma tl
#pop-options

(* Conformance of a generic value to a schema *)

(* A generic value conforms to `k` if the typed parser accepts exactly its
   (unique, DER) encoding.  This is a total, executable Boolean predicate on
   the value. *)
let conforms (#s: _) (k: asn1_k s) (v: asn1_value) : Tot bool =
  let e = asn1_value_enc v in
  match coerce_to_tot_bare_parser _ _ (asn1_as_parser k) e with
  | Some (_, n) -> n = Seq.length e
  | None -> false

(* For a well-formed schema, the typed parser accepts exactly those inputs
   accepted by the generic ANY parser whose value conforms to the schema,
   consuming the same number of bytes. *)
let conformance_spec (#s: _) (k: asn1_k s) (b: bytes) : GTot prop =
  match parse (asn1_as_parser k) b, parse parse_asn1_value b with
  | Some (_, n1), Some (v, n2) -> n1 == n2 /\ conforms k v == true
  | None, Some (v, _) -> conforms k v == false
  | Some _, None -> False
  | None, None -> True

#push-options "--z3rlimit 64"
let conformance_correct (#s: _) (k: asn1_k s) (b: bytes)
: Lemma
  (requires (wf k))
  (ensures (conformance_spec k b))
= top_lemma k;
  let p = asn1_as_parser k in
  parse_asn1_value_consumed' b;
  match parse p b, parse parse_asn1_value b with
  | Some (_, n1), Some (v, n2) ->
    assert (value_at b n1);
    let e = Seq.slice b 0 n1 in
    parse_strong_prefix #asn1_strong_parser_kind p b e
  | None, Some (v, n2) ->
    let e = Seq.slice b 0 n2 in
    begin match parse p e with
    | Some (_, n) ->
      if n = Seq.length e then parse_strong_prefix #asn1_strong_parser_kind p e b
    | None -> ()
    end
  | Some (_, n1), None -> assert (value_at b n1)
  | None, None -> ()
#pop-options

(* Round trip: for a well-formed schema, every conforming generic value is
   recovered by the generic ANY parser from its encoding. *)
let conforms_roundtrip (#s: _) (k: asn1_k s) (v: asn1_value)
: Lemma
  (requires (wf k /\ conforms k v == true))
  (ensures (parse parse_asn1_value (asn1_value_enc v) == Some (v, Seq.length (asn1_value_enc v))))
= let e = asn1_value_enc v in
  conformance_correct k e;
  parse_asn1_value_consumed' e;
  match parse parse_asn1_value e with
  | Some (v', n) ->
    Seq.lemma_eq_elim (Seq.slice e 0 n) e;
    asn1_value_enc_inj v' v
  | None -> ()

(* DER order of SET components: whenever the typed SET parser accepts some
   contents, the identifiers of the generic values in those contents are
   strictly increasing in the canonical order of tags (X.690 10.3.) *)

let asn1_value_id (v: asn1_value) : Tot asn1_id_t =
  match v with
  | ASN1_VALUE_PRIMITIVE id _ -> id
  | ASN1_VALUE_CONSTRUCTED id _ -> id

let rec value_ids_sorted (l: list asn1_value) : Tot bool =
  match l with
  | x :: y :: q -> asn1_tag_lt (asn1_value_id x) (asn1_value_id y) && value_ids_sorted (y :: q)
  | _ -> true

private
let synth_asn1_value_id
  (x : dtuple2 asn1_any_id_t (fun id -> RV.rec_vlgen_payload asn1_value asn1_octetstring_t))
: Lemma (asn1_value_id (synth_asn1_value x) == dfst x)
= match x with
  | (| _, RV.RNode _ |) -> ()
  | (| _, RV.RLeaf _ |) -> ()

let pv_value_id (b: bytes)
: Lemma
  (match parse pv b with
   | Some (v, _) -> (match parse parse_asn1_identifier_U32 b with
     | Some (id, _) -> asn1_value_id v == id
     | None -> False)
   | None -> True)
= RV.parse_rec_vlgen_eq asn1_value_param b;
  parse_any_identifier_consumed b;
  match RV.rec_vlgen_header asn1_value_param b with
  | None -> ()
  | Some (h, hs, len) ->
    if hs + len > Seq.length b then ()
    else match parse (RV.rec_vlgen_body asn1_value_param pv h) (Seq.slice b hs (hs + len)) with
    | None -> ()
    | Some (pl, _) -> synth_asn1_value_id (| h, pl |)

let choice_twin_tag (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind)) (id: asn1_id_t) (b: bytes)
: Lemma
  (match parse (parse_tagged_union_payload (project_tags lp) (make_gen_choice_strong_payload_parser lp) id) b with
   | Some (v, _) -> project_tags lp v == id
   | None -> True)
= LowParse.Spec.Combinators.parse_synth_eq #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser lp id) (synth_tagged_union_data (project_tags lp) id) b

#push-options "--fuel 1 --ifuel 1"
let any_twin_tag (id: asn1_id_t) (b: bytes)
: Lemma
  (match parse (parse_asn1_value_twin id) b with
   | Some (v, _) -> asn1_value_id v == id
   | None -> True)
= if asn1_any_id_valid id
  then begin
    let pp = RV.rec_vlgen_payload_parser asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id in
    parse_synth_eq pp (synth_asn1_value_twin id) b;
    match parse pp b with
    | Some (x, _) ->
      (match x with
       | RV.RNode _ -> ()
       | RV.RLeaf _ -> ())
    | None -> ()
  end
#pop-options

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let k_twin_tag (#s: _) (k: asn1_k s) (id: asn1_id_t) (b: bytes)
: Lemma
  (match parse (snd (asn1_as_parser_twin k) id) b with
   | Some (v, _) -> asn1_k_tag k v == id
   | None -> True)
= match k with
  | ASN1_ILC _ _ -> ()
  | ASN1_CHOICE_ILC lc pf ->
    let lp = asn1_lc_as_parser lc in
    assert (snd (asn1_as_parser_twin k) id == make_asn1_choice_parser_twin_cases lc pf k lp id);
    choice_twin_tag lp id b
  | ASN1_ANY_ILC ->
    assert (snd (asn1_as_parser_twin k) id == parse_asn1_value_twin id);
    any_twin_tag id b
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let dec_twin_tag (#s: _) (#d: _) (dk: asn1_decorated_k s d) (id: asn1_id_t) (b: bytes)
: Lemma
  (let item = asn1_decorated_as_parser_twin dk in
   match parse (parse_asn1_sequence_item_twin item id) b with
   | Some (v, _) -> decorated_tag (Mkgendcparser?.d item) v == Some id
   | None -> True)
= let item = asn1_decorated_as_parser_twin dk in
  match dk with
  | ASN1_PLAIN_ILC k -> k_twin_tag k id b
  | ASN1_OPTION_ILC k ->
    k_twin_tag k id b;
    parse_synth_eq (Mkgendcparser?.fp item id) Some b
  | ASN1_DEFAULT_TERMINAL id0 #k defv_l ->
    let defv = key_of_lit k defv_l in
    let fp = Mkgendcparser?.fp item in
    parse_synth_eq ((fp id) `parse_filter` (defaultv_filter defv)) (defaultv_synth defv) b;
    parse_filter_eq (fp id) (defaultv_filter defv) b
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv_l ->
    let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let fp = Mkgendcparser?.fp item in
    let d = Mkgendcparser?.d item in
    parse_synth_eq (((fp id) `parse_filter` (restriction_pred r)) `parse_filter` (defaultv_filter #(asn1_decorated_pure_t d) defv)) (defaultv_synth #(asn1_decorated_pure_t d) defv) b;
    parse_filter_eq ((fp id) `parse_filter` (restriction_pred r)) (defaultv_filter #(asn1_decorated_pure_t d) defv) b;
    parse_filter_eq (fp id) (restriction_pred r) b
#pop-options

let item_tagged (item: gen_decorated_parser_twin) : prop =
  forall id b. match parse (parse_asn1_sequence_item_twin item id) b with
  | Some (v, _) -> decorated_tag (Mkgendcparser?.d item) v == Some id
  | None -> True

let rec items_tagged (its: list gen_decorated_parser_twin) : Tot prop (decreases its) =
  match its with
  | [] -> True
  | hd :: tl -> item_tagged hd /\ items_tagged tl

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"
let rec items_tagged_intro (#ids: _) (ls: asn1_gen_items_l ids)
: Lemma
  (ensures (items_tagged (asn1_sequence_as_parser ls)))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    Classical.forall_intro_2 (dec_twin_tag dk);
    assert (item_tagged (asn1_decorated_as_parser_twin dk));
    items_tagged_intro tl;
    assert (asn1_sequence_as_parser ls == asn1_decorated_as_parser_twin dk :: asn1_sequence_as_parser tl)
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec set_elem_twin_tag (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (items_tagged its))
  (ensures (match parse (parse_set_elem_twin its id) b with
    | Some (e, _) -> elem_tag its e == Some id
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    assert (item_tagged hd);
    if FStar.Set.mem id s
    then begin
      parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b;
      match parse (parse_asn1_sequence_item_twin hd id) b with
      | Some (v, _) ->
        assert (decorated_tag (Mkgendcparser?.d hd) v == Some id);
        let e : set_elem_t its = Inl #_ #(set_elem_t tl) v in
        assert (elem_tag its e == decorated_tag (Mkgendcparser?.d hd) v)
      | None -> ()
    end
    else begin
      set_elem_twin_tag tl id b;
      parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b;
      match parse (parse_set_elem_twin tl id) b with
      | Some (e', _) ->
        let e : set_elem_t its = Inr #(asn1_decorated_t (Mkgendcparser?.d hd)) e' in
        assert (elem_tag its e == elem_tag tl e')
      | None -> ()
    end
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_elem_pv (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_sound its /\ items_tagged its))
  (ensures (match parse (parse_set_elem its) b with
    | Some (e, n) -> (match parse pv b with
      | Some (v, n') -> n' == n /\ elem_tag its e == Some (asn1_value_id v)
      | None -> False)
    | None -> True))
= set_elem_value_at its b;
  pv_value_id b;
  parse_set_elem_twin_cases_injective its;
  and_then_eq parse_asn1_identifier_U32 (parse_set_elem_twin its) b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id, c1) -> set_elem_twin_tag its id (Seq.slice b c1 (Seq.length b))
  | None -> ()
#pop-options

let value_tag (v: asn1_value) : Tot (option asn1_id_t) = Some (asn1_value_id v)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"
let rec set_list_pv (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_sound its /\ items_tagged its))
  (ensures (match parse (parse_list (parse_set_elem its)) b with
    | Some (le, _) -> (match parse (tot_parse_list pv) b with
      | Some (lv, _) -> List.Tot.map (elem_tag its) le == List.Tot.map value_tag lv
      | None -> False)
    | None -> True))
  (decreases (Seq.length b))
= tot_parse_list_eq (parse_set_elem its) b;
  tot_parse_list_eq pv b;
  if Seq.length b = 0 then ()
  else begin
    set_elem_pv its b;
    match parse (parse_set_elem its) b with
    | Some (e, c) ->
      if c = 0 then ()
      else begin
        let b' = Seq.slice b c (Seq.length b) in
        set_list_pv its b';
        match parse (tot_parse_list (parse_set_elem its)) b' with
        | Some (le', _) ->
          let Some (v, _) = parse pv b in
          let Some (lv', _) = parse (tot_parse_list pv) b' in
          assert (List.Tot.map (elem_tag its) (e :: le') == List.Tot.map value_tag (v :: lv'))
        | None -> ()
      end
    | None -> ()
  end
#pop-options

let rec tags_sorted_value_ids (#t: Type) (key: t -> Tot (option asn1_id_t)) (le: list t) (lv: list asn1_value)
: Lemma
  (requires (tags_sorted key le /\ List.Tot.map key le == List.Tot.map value_tag lv))
  (ensures (value_ids_sorted lv))
  (decreases lv)
= match le, lv with
  | _ :: y :: q, _ :: v :: r -> tags_sorted_value_ids key (y :: q) (v :: r)
  | _ -> ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let set_der_sorted (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (items_sound its /\ items_tagged its))
  (ensures (match parse (make_asn1_set_parser its) b with
    | Some (_, n) -> (match parse (tot_parse_list pv) (Seq.slice b 0 n) with
      | Some (l, _) -> value_ids_sorted l
      | None -> False)
    | None -> True))
= set_to_tuple_injective its;
  let pl = parse_list (parse_set_elem its) in
  let pf = pl `parse_filter` set_ok its in
  parse_synth_eq pf (set_to_tuple its) b;
  parse_filter_eq pl (set_ok its) b;
  set_list_pv its b;
  parser_kind_prop_equiv (parse_list_kind true) pl;
  match parse pl b with
  | Some (le, n) ->
    Seq.lemma_eq_elim b (Seq.slice b 0 n);
    (match parse (tot_parse_list pv) b with
     | Some (lv, _) -> if set_ok its le then tags_sorted_value_ids (elem_tag its) le lv
     | None -> ())
  | None -> ()
#pop-options

(* For a well-formed schema, the contents accepted by a SET are a list of
   generic values sorted in DER order *)
let set_content_der_sorted (ids: id_decs) (items: asn1_gen_items_l ids) (pf: squash (asn1_set_k_wf ids)) (b: bytes)
: Lemma
  (requires (wf_items items))
  (ensures (match parse (asn1_content_as_parser (ASN1_SET ids items pf)) b with
    | Some (_, n) -> (match parse (tot_parse_list pv) (Seq.slice b 0 n) with
      | Some (l, _) -> value_ids_sorted l
      | None -> False)
    | None -> True))
= items_lemma items;
  items_tagged_intro items;
  set_der_sorted (asn1_sequence_as_parser items) b
