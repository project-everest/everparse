module ASN1.Spec.Raw.Props

(* Properties of raw values (`ASN1.Spec.Raw`) used by the Pulse relation
   between Pulse representations and raw values
   (`ASN1.Pulse.RawValueRel`):
   - `raw_leaf_enc`: a content encoder for raw leaves, total on all raw
     values, which agrees with `leaf_enc` on typed values;
   - `forget` is injective (even on non-canonical values, unlike the
     `check (forget x) == Some x` round trip);
   - `parse_raw k`: the typed parser followed by `forget`. *)

open ASN1.Bytes
open ASN1.Base
open ASN1.Spec.Content.Enc
open ASN1.Spec.Raw
open ASN1.Spec.Interpreter
open LowParse.Tot.Base
open LowParse.Tot.Combinators

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module LPC = LowParse.Spec.Combinators

(* Raw leaf encoder *)

let raw_byte_enc (b: U8.t) : Tot bytes = Seq.create 1 b

(* A raw OBJECT IDENTIFIER that is not well-formed is encoded with a
   leading 0x80 byte, which never starts a (minimal) base-128 subidentifier:
   this makes `raw_oid_enc` injective, and its result is always rejected by
   the DER OBJECT IDENTIFIER parser. *)
let raw_oid_enc (l: list U32.t) : Tot bytes =
  if asn1_OID_wf l then oid_enc l else Seq.cons 0x80uy (list_enc enc_arc l)

let raw_leaf_enc (k: leaf_k) (x: asn1_raw_terminal_t k) : Tot bytes =
  match k with
  | ASN1_BOOLEAN -> boolean_enc x
  | ASN1_INTEGER _ -> let x : int = x in ASN1.Spec.Content.INTEGER.mk_bytes (ASN1.Spec.Content.INTEGER.domain_intro_gen x) x
  | ASN1_BITSTRING -> let x : (U8.t & asn1_bytes) = x in Seq.cons (fst x) (snd x)
  | ASN1_PRINTABLESTRING
  | ASN1_IA5STRING
  | ASN1_VISIBLESTRING
  | ASN1_NUMERICSTRING -> let x : list U8.t = x in list_enc raw_byte_enc x
  | ASN1_NULL -> Seq.empty
  | ASN1_OID -> raw_oid_enc x
  | ASN1_RELATIVE_OID -> list_enc enc_arc x
  | ASN1_OCTETSTRING
  | ASN1_UTF8STRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME -> (x <: bytes)

let rec raw_chars_enc (p: U8.t -> Tot bool) (l: list (char_t p))
: Lemma (list_enc raw_byte_enc (forget_chars p l) == list_enc (byte_enc #p) l)
= match l with
  | [] -> ()
  | _ :: q -> raw_chars_enc p q

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let raw_leaf_enc_forget (k: leaf_k) (y: asn1_terminal_t k)
: Lemma (raw_leaf_enc k (forget_terminal k y) == leaf_enc k y)
= match k with
  | ASN1_PRINTABLESTRING -> printable_eq (); raw_chars_enc is_printable_char (coerce_eq #asn1_printablestring_t #(list (char_t is_printable_char)) () y)
  | ASN1_IA5STRING -> ia5_eq (); raw_chars_enc is_ia5_char (coerce_eq #asn1_ia5string_t #(list (char_t is_ia5_char)) () y)
  | ASN1_VISIBLESTRING -> visible_eq (); raw_chars_enc is_visible_char (coerce_eq #asn1_visiblestring_t #(list (char_t is_visible_char)) () y)
  | ASN1_NUMERICSTRING -> numeric_eq (); raw_chars_enc is_numeric_char (coerce_eq #asn1_numericstring_t #(list (char_t is_numeric_char)) () y)
  | ASN1_BITSTRING -> ()
  | ASN1_INTEGER _ -> ()
  | _ -> ()
#pop-options

(* Injectivity of `forget` *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec forget_content_inj (k: asn1_content_k) (x1 x2: asn1_content_t k)
: Lemma (requires (forget_content k x1 == forget_content k x2)) (ensures (x1 == x2)) (decreases %[k; 3])
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> forget_terminal_inj k' x1 x2
  | ASN1_TERMINAL k' -> forget_terminal_inj k' x1 x2
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    forget_items_inj items x1 x2
  | ASN1_SET _ items _ -> forget_items_inj items x1 x2
  | ASN1_SEQUENCE_OF _ k' -> forget_list_inj k' x1 x2
  | ASN1_SET_OF _ k' -> forget_list_inj k' x1 x2
  | ASN1_PREFIXED k' -> forget_inj k' x1 x2
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let s1 : make_gen_choice_type (typed_any_t key_k ls) = items_any_sfx prefix x1 in
      let s2 : make_gen_choice_type (typed_any_t key_k ls) = items_any_sfx prefix x2 in
      let rs1 = forget_adb_sfx key_k ls s1 in
      let rs2 = forget_adb_sfx key_k ls s2 in
      raw_items_any_sfx_forget prefix #(make_gen_choice_type (typed_any_t key_k ls)) x1 rs1;
      raw_items_any_sfx_forget prefix #(make_gen_choice_type (typed_any_t key_k ls)) x2 rs2;
      forget_adb_sfx_inj key_k ls s1 s2;
      forget_items_any_inj prefix #(make_gen_choice_type (typed_any_t key_k ls)) x1 x2 rs1 rs2
    | Some fb ->
      let (| _, fbitems |) = fb in
      fb_precedes k;
      let s1 : make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems) = items_any_sfx prefix x1 in
      let s2 : make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems) = items_any_sfx prefix x2 in
      let rs1 = forget_adb_fb_sfx k key_k ls fbitems s1 in
      let rs2 = forget_adb_fb_sfx k key_k ls fbitems s2 in
      raw_items_any_sfx_forget prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) x1 rs1;
      raw_items_any_sfx_forget prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) x2 rs2;
      forget_adb_fb_sfx_inj k key_k ls fbitems s1 s2;
      forget_items_any_inj prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) x1 x2 rs1 rs2
    end

and forget_adb_sfx_inj (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (s1 s2: make_gen_choice_type (typed_any_t key_k ls))
: Lemma (requires (forget_adb_sfx key_k ls s1 == forget_adb_sfx key_k ls s2)) (ensures (s1 == s2)) (decreases %[ls; 1])
= let (| key1, y1 |) = s1 in
  let (| key2, y2 |) = s2 in
  forget_terminal_inj key_k key1 key2;
  forget_ls_inj key_k ls key1 y1 y2

and forget_adb_fb_sfx_inj (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (s1 s2: make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))
: Lemma (requires (forget_adb_fb_sfx k0 key_k ls fbitems s1 == forget_adb_fb_sfx k0 key_k ls fbitems s2)) (ensures (s1 == s2)) (decreases %[k0; 2])
= let (| key1, y1 |) = s1 in
  let (| key2, y2 |) = s2 in
  forget_terminal_inj key_k key1 key2;
  forget_ls_fb_inj k0 key_k ls fbitems key1 y1 y2

and forget_list_inj (#s: _) (k: asn1_k s) (l1 l2: list (asn1_t k))
: Lemma (requires (forget_list k l1 == forget_list k l2)) (ensures (l1 == l2)) (decreases %[k; 3; l1])
= match l1, l2 with
  | a1 :: q1, a2 :: q2 -> forget_inj k a1 a2; forget_list_inj k q1 q2
  | _ -> ()

and forget_inj (#s: _) (k: asn1_k s) (x1 x2: asn1_t k)
: Lemma (requires (forget k x1 == forget k x2)) (ensures (x1 == x2)) (decreases %[k; 2])
= match k with
  | ASN1_ILC _ k' -> forget_content_inj k' x1 x2
  | ASN1_CHOICE_ILC lc _ ->
    let x1' : make_gen_choice_type (asn1_lc_t lc) = x1 in
    let x2' : make_gen_choice_type (asn1_lc_t lc) = x2 in
    let (| id1, y1 |) = x1' in
    let (| id2, y2 |) = x2' in
    forget_choice_inj lc id1 y1 y2
  | ASN1_ANY_ILC -> ()

and forget_choice_inj (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y1 y2: idlookup_t id (asn1_lc_t lc))
: Lemma (requires (forget_choice lc id y1 == forget_choice lc id y2)) (ensures (y1 == y2)) (decreases %[lc; 0])
= match lc with
  | [] -> ()
  | (id', c) :: tl ->
    if id = id'
    then forget_content_inj c y1 y2
    else forget_choice_inj tl id y1 y2

and forget_ls_inj (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y1 y2: idlookup_t key (typed_any_t key_k ls))
: Lemma (requires (forget_ls key_k ls key y1 == forget_ls key_k ls key y2)) (ensures (y1 == y2)) (decreases %[ls; 0])
= match ls with
  | [] -> ()
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then forget_items_inj items y1 y2
    else begin
      forget_key_ne key_k key l;
      forget_ls_inj key_k tl key y1 y2
    end

and forget_ls_fb_inj (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y1 y2: idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))
: Lemma (requires (forget_ls_fb k0 key_k ls fbitems key y1 == forget_ls_fb k0 key_k ls fbitems key y2)) (ensures (y1 == y2)) (decreases %[k0; 1; ls])
= match ls with
  | [] -> forget_items_inj fbitems y1 y2
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then forget_items_inj items y1 y2
    else begin
      forget_key_ne key_k key l;
      forget_ls_fb_inj k0 key_k tl fbitems key y1 y2
    end

and forget_dec_inj (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x1 x2: asn1_decorated_t_core dk)
: Lemma (requires (forget_dec dk x1 == forget_dec dk x2)) (ensures (x1 == x2)) (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> forget_inj k x1 x2
  | ASN1_OPTION_ILC k ->
    let x1' : option (asn1_t k) = x1 in
    let x2' : option (asn1_t k) = x2 in
    (match x1', x2' with Some y1, Some y2 -> forget_inj k y1 y2 | _ -> ())
  | ASN1_DEFAULT_TERMINAL _ #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x1' : default_tv defv = x1 in
    let x2' : default_tv defv = x2 in
    (match x1', x2' with Nondefault y1, Nondefault y2 -> forget_terminal_inj k y1 y2 | _ -> ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r defv_l ->
    let defv : LPC.parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x1' : default_tv #(LPC.parse_filter_refine (restriction_pred r)) defv = x1 in
    let x2' : default_tv #(LPC.parse_filter_refine (restriction_pred r)) defv = x2 in
    (match x1', x2' with Nondefault y1, Nondefault y2 -> forget_terminal_inj k y1 y2 | _ -> ())

and forget_items_inj (#ids: _) (items: asn1_gen_items_l ids) (x1 x2: asn1_sequence_t_core items)
: Lemma (requires (forget_items items x1 == forget_items items x2)) (ensures (x1 == x2)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> forget_dec_inj dk x1 x2
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x1' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x1 in
    let x2' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x2 in
    forget_dec_inj dk (fst x1') (fst x2');
    forget_items_inj tl (snd x1') (snd x2')

and forget_items_any_inj (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t #rsfx_t: Type) (x1 x2: asn1_sequence_any_t_core items sfx_t) (rs1 rs2: rsfx_t)
: Lemma (requires (forget_items_any items x1 rs1 == forget_items_any items x2 rs2 /\ items_any_sfx items x1 == items_any_sfx items x2)) (ensures (x1 == x2)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x1' : asn1_decorated_t_core dk & sfx_t = x1 in
    let x2' : asn1_decorated_t_core dk & sfx_t = x2 in
    forget_dec_inj dk (fst x1') (fst x2')
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x1' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x1 in
    let x2' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x2 in
    forget_dec_inj dk (fst x1') (fst x2');
    forget_items_any_inj tl #sfx_t #rsfx_t (snd x1') (snd x2') rs1 rs2
#pop-options

let forget_injective (#s: _) (k: asn1_k s)
: Lemma (LPC.synth_injective (forget k))
= Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (forget_inj k x1) x2)

(* The raw element parser: the typed parser, followed by `forget` *)

let parse_raw (#s: _) (k: asn1_k s) : Tot (parser asn1_strong_parser_kind (asn1_raw_t k)) =
  forget_injective k;
  parse_synth #asn1_strong_parser_kind (asn1_as_parser k) (forget k)

let parse_raw_eq (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (parse (parse_raw k) b == (match parse (asn1_as_parser k) b with
    | Some (x, n) -> Some (forget k x, n)
    | None -> None))
= forget_injective k;
  parse_synth_eq #asn1_strong_parser_kind (asn1_as_parser k) (forget k) b
