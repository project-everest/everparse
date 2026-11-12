module ASN1.Pulse.Interpreter
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.ILC
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module ILC = ASN1.Pulse.ILC
module Term = ASN1.Pulse.Terminal
module C = ASN1.Pulse.Constructed
module SO = ASN1.Pulse.SetOf
module Rs = ASN1.Pulse.Restrict
module SC = ASN1.Pulse.SetComp
module Any = ASN1.Pulse.Any
module ADB = ASN1.Pulse.AnyDefinedBy
module AP = ASN1.Pulse.AdbPrefixed
module DL = ASN1.Pulse.DefaultLit
module SA = ASN1.Pulse.SeqAny
module PPFL = LowParse.PulseParse.FLData
module SCo = LowParse.Spec.Combinators
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SFL = LowParse.Spec.FLData

(* Definitions tagged with this attribute are unfolded when specializing
   the interpreter to a given schema. *)
irreducible let asn1_pulse_attr : unit = ()

[@@asn1_pulse_attr]
let rec items_len (#i: _) (ls: asn1_gen_items_l i) : Tot (n: nat { n == List.Tot.length (asn1_sequence_as_parser ls) }) (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> 0
  | ASN1_GEN_ITEMS_CONS _ _ _ _ tl -> 1 + items_len tl

(* Provably equal to `asn1_decorated_as_parser_twin dk` and
   `asn1_sequence_as_parser ls`, but with the item descriptor `d` exposed
   as a constructor argument, so that the value types of the sequence
   validators (`asn1_sequence_t (List.Tot.map Mkgendcparser?.d items)`)
   fully reduce at extraction time instead of leaving stuck projector
   chains that blow up extraction time. *)

[@@asn1_pulse_attr]
let twin_of (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Tot (gp: gen_decorated_parser_twin { gp == asn1_decorated_as_parser_twin dk })
= let item = (| s, d, dk |) in
  match dk with
  | ASN1_PLAIN_ILC k ->
    let pfp = asn1_as_parser_twin k in
    Mkgendcparser item (fst pfp) (snd pfp)
  | ASN1_OPTION_ILC k ->
    let pfp = asn1_as_parser_twin k in
    Mkgendcparser item (fst pfp) (snd pfp)
  | ASN1_DEFAULT_TERMINAL id #k defv ->
    let p = asn1_terminal_as_parser k in
    Mkgendcparser item (parse_asn1_ILC id #(ASN1_TERMINAL k) p) (parse_asn1_ILC_twin id #(ASN1_TERMINAL k) p)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv ->
    let p : asn1_weak_parser (asn1_decorated_pure_t item) = weaken _ ((asn1_terminal_as_parser k) `parse_filter` (restriction_pred r)) in
    Mkgendcparser item (parse_asn1_ILC id #(ASN1_RESTRICTED_TERMINAL k r) p) (parse_asn1_ILC_twin id #(ASN1_RESTRICTED_TERMINAL k r) p)

[@@asn1_pulse_attr]
let rec twins_of (#i: _) (ls: asn1_gen_items_l i)
: Tot (l: list gen_decorated_parser_twin { l == asn1_sequence_as_parser ls }) (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> []
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> twin_of dk :: twins_of tl

(* The subset of schemas currently supported *)

[@@asn1_pulse_attr]
let rec supported_terminal (k: asn1_terminal_k) : Tot bool (decreases k) =
  match k with
  | ASN1_INTEGER bound -> bound < 18446744073709551615
  | ASN1_PREFIXED_TERMINAL _ k' -> supported_terminal k'
  | _ -> true

[@@asn1_pulse_attr]
let supported_restriction (k: asn1_terminal_k) (r: asn1_restriction k) : Tot bool =
  match k with
  | ASN1_BOOLEAN -> RESTRICT_IN? r
  | ASN1_INTEGER bound -> bound < 18446744073709551615 && Rs.int_restriction_ok r
  | _ -> Rs.size_string_k k && Rs.size_restriction_ok r

(* ANY DEFINED BY: the kinds of keys that can be compared with a constant *)
[@@asn1_pulse_attr; FStar.Attributes.custard_compile_time]
let rec adb_key_supported (k: asn1_terminal_k) : Tot bool (decreases k) =
  match k with
  | ASN1_INTEGER _ -> supported_terminal k
  | ASN1_RELATIVE_OID -> false
  | ASN1_PREFIXED_TERMINAL _ k' -> adb_key_supported k'
  | _ -> true

let rec adb_key_supported_terminal (k: asn1_terminal_k)
: Lemma (requires adb_key_supported k) (ensures supported_terminal k) (decreases k)
  [SMTPat (adb_key_supported k)]
= match k with
  | ASN1_PREFIXED_TERMINAL _ k' -> adb_key_supported_terminal k'
  | _ -> ()

(* DEFAULT values are literals, compared like ANY DEFINED BY keys *)
[@@asn1_pulse_attr]
let supported_default (k: asn1_terminal_k) : Tot bool =
  adb_key_supported k

[@@asn1_pulse_attr]
let supported_default_restricted (k: asn1_terminal_k) (r: asn1_restriction k) : Tot bool =
  supported_restriction k r && adb_key_supported k

[@@asn1_pulse_attr]
let rec supported_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL k' -> supported_terminal k'
  | ASN1_RESTRICTED_TERMINAL k' r -> supported_restriction k' r
  | ASN1_SEQUENCE gitems -> supported_items (dsnd gitems)
  | ASN1_SEQUENCE_OF _ k' -> supported_k k'
  | ASN1_SET_OF _ k' -> supported_k k'
  | ASN1_SET _ items _ -> supported_items items && items_len items <= 64
  | ASN1_PREFIXED k' -> supported_k k'
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    supported_items prefix && adb_key_supported key_k && supported_ls ls &&
    (match ofb with None -> true | Some fb -> supported_items (dsnd fb))

and supported_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> supported_content k'
  | ASN1_CHOICE_ILC lc _ -> supported_lc lc
  | ASN1_ANY_ILC -> true

and supported_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (_, ck) :: tl -> supported_content ck && supported_lc tl

and supported_ls (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot bool (decreases ls) =
  match ls with
  | [] -> true
  | (_, y) :: tl -> supported_items (dsnd y) && supported_ls tl

and supported_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> supported_dec dk && supported_items tl

and supported_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> supported_k k
  | ASN1_OPTION_ILC k -> supported_k k
  | ASN1_DEFAULT_TERMINAL _ #k _ -> supported_default k
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r _ -> supported_default_restricted k r
  | _ -> false

(* Static information about sequence items *)

[@@asn1_pulse_attr; FStar.Attributes.custard_compile_time]
let rec all_defaultable (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ d _ _ tl -> not (PLAIN? d) && all_defaultable tl

let rec all_defaultable_correct (#i: _) (ls: asn1_gen_items_l i)
: Lemma
  (ensures (all_defaultable ls == Some? (generate_defaultable_items (asn1_sequence_as_parser ls))))
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ _ _ tl -> all_defaultable_correct tl

[@@asn1_pulse_attr]
let rec has_id_lc ([@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id (Set.as_set' (List.Tot.map fst lc)) })
  (decreases lc)
= match lc with
  | [] -> false
  | (id', _) :: tl -> ILC.asn1_id_eq id id' || has_id_lc tl id

[@@asn1_pulse_attr]
inline_for_extraction
let has_id_k (#s: _) (k: asn1_k s) (u: squash (supported_k k)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match k with
  | ASN1_ILC id0 _ -> ILC.asn1_id_eq id id0
  | ASN1_CHOICE_ILC lc _ -> has_id_lc lc id
  | ASN1_ANY_ILC -> true

inline_for_extraction
fn validate_fail
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: SB.parser k t)
  (u: squash (forall b . None? (SB.parse p b)))
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  false
}

[@@asn1_pulse_attr]
inline_for_extraction
let has_id_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (supported_dec dk)) (id: asn1_id_t)
: Tot (b: bool { b == Set.mem id s })
= match dk with
  | ASN1_PLAIN_ILC k -> has_id_k k () id
  | ASN1_OPTION_ILC k -> has_id_k k () id
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 _ _ -> ILC.asn1_id_eq id id0
  | ASN1_DEFAULT_TERMINAL id0 _ -> ILC.asn1_id_eq id id0

(* SET { ... }: static component lookup and final check *)

(* Not unfolded at specialization: the normalizer does not unfold recursive
   calls in the branches of a stuck match, so the recursive call must be
   an argument. *)
inline_for_extraction
let pick (b: bool) (j: U32.t) (r: option U32.t) : Tot (o: option U32.t { o == (if b then Some j else r) }) =
  if b then Some j else r

let comp_of_id_cons (#i: _) (ls: asn1_gen_items_l i { ASN1_GEN_ITEMS_CONS? ls }) (id: asn1_id_t)
: Lemma (let ASN1_GEN_ITEMS_CONS s _ _ _ tl = ls in
    SC.comp_of_id (asn1_sequence_as_parser ls) id ==
    (if Set.mem id s then Some 0 else match SC.comp_of_id (asn1_sequence_as_parser tl) id with None -> None | Some c -> Some (c + 1)))
= let ASN1_GEN_ITEMS_CONS s _ dk _ tl = ls in
  assert (asn1_sequence_as_parser ls == twin_of dk :: twins_of tl);
  assert (item_set (twin_of dk) == s)

let set_comp_cons (#i: _) (ls: asn1_gen_items_l i { ASN1_GEN_ITEMS_CONS? ls }) (j: U32.t) (id: asn1_id_t)
: Lemma (let ASN1_GEN_ITEMS_CONS s _ _ _ tl = ls in
    forall (r: option U32.t) .
    SC.opt_u32_v r == (match SC.comp_of_id (asn1_sequence_as_parser tl) id with None -> None | Some c -> Some (U32.v j + 1 + c)) ==>
    SC.opt_u32_v (if Set.mem id s then Some j else r) == (match SC.comp_of_id (asn1_sequence_as_parser ls) id with None -> None | Some c -> Some (U32.v j + c)))
= comp_of_id_cons ls id

[@@asn1_pulse_attr]
let rec set_comp (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (supported_items ls))
  (j: U32.t { U32.v j + items_len ls <= 64 }) (id: asn1_id_t)
: Tot (r: option U32.t { SC.opt_u32_v r == (match SC.comp_of_id (asn1_sequence_as_parser ls) id with None -> None | Some c -> Some (U32.v j + c)) })
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> None
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    set_comp_cons ls j id;
    pick (has_id_dec dk () id) j (set_comp tl () (U32.add j 1ul) id)

[@@asn1_pulse_attr]
let rec set_final (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i)
  (j: U32.t { U32.v j + items_len ls <= 64 }) (m: U64.t)
: Tot (b: bool { b == SC.final_ok' (asn1_sequence_as_parser ls) (U32.v j) m })
  (decreases ls)
= match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ d _ _ tl ->
    SC.test_bit_spec m j;
    (not (PLAIN? d) || SC.test_bit m j) && set_final tl (U32.add j 1ul) m

(* ANY DEFINED BY: equality of an OBJECT IDENTIFIER key with a constant *)

[@@asn1_pulse_attr]
let rec validate_subids_eq ([@@@FStar.Attributes.monomorphize] l: list U32.t)
: Tot (LPS.validator #_ #ADB.subids_kind (ADB.subids_eq_p l))
  (decreases l)
= match l with
  | [] -> ADB.validate_subids_eq_nil ()
  | h :: tl -> ADB.validate_subids_eq_cons h tl (validate_subids_eq tl)

[@@asn1_pulse_attr]
inline_for_extraction
let oid_enc (x: asn1_oid_t) : Tot (l: list U32.t { l == ADB.oid_enc x }) =
  match x with
  | a :: b :: tl ->
    (if a = 2ul then U32.add 80ul b else U32.add (U32.mul 40ul a) b) :: tl

[@@asn1_pulse_attr]
inline_for_extraction
let validate_key_eq (key_k: asn1_terminal_k) (u: squash (ASN1_OID? key_k)) (x: asn1_terminal_t key_k)
: Tot (LPS.validator #_ #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x)))
= match key_k with
  | ASN1_OID ->
    Classical.forall_intro (ADB.oid_filter_consumed x);
    validate_ext_consumed (validate_subids_eq (oid_enc x)) (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x))

(* ANY DEFINED BY: equality of other keys with a constant, on their DER
   content encoding, computed at extraction time from the key literal *)

[@@asn1_pulse_attr]
let rec char_list_bytes (#p: U8.t -> Tot bool) ([@@@FStar.Attributes.monomorphize] l: list (b: LowParse.Bytes.byte { p b })) : Tot (list U8.t) (decreases l) =
  match l with
  | [] -> []
  | c :: q -> (c <: U8.t) :: char_list_bytes q

let rec char_list_bytes_correct (#p: U8.t -> Tot bool) (l: list (b: LowParse.Bytes.byte { p b }))
: Lemma (Seq.seq_of_list (char_list_bytes l) == ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #p) l)
  (decreases l)
= match l with
  | [] ->
    assert_norm (char_list_bytes #p [] == []);
    assert_norm (ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #p) [] == Seq.empty);
    Seq.lemma_seq_of_list_induction #U8.t [];
    Seq.lemma_eq_elim (Seq.seq_of_list #U8.t []) Seq.empty
  | c :: q ->
    char_list_bytes_correct q;
    assert_norm (char_list_bytes (c :: q) == (c <: U8.t) :: char_list_bytes q);
    assert_norm (ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #p) (c :: q) == ASN1.Spec.Content.Enc.byte_enc #p c `Seq.append` ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #p) q);
    assert_norm (ASN1.Spec.Content.Enc.byte_enc #p c == Seq.create 1 (c <: U8.t));
    Seq.lemma_seq_of_list_induction ((c <: U8.t) :: char_list_bytes q);
    Seq.lemma_eq_elim (Seq.cons (c <: U8.t) (Seq.seq_of_list (char_list_bytes q))) (Seq.append (Seq.create 1 (c <: U8.t)) (Seq.seq_of_list (char_list_bytes q)))

[@@asn1_pulse_attr]
inline_for_extraction
let key_enc_list (k: asn1_terminal_k { adb_key_supported k /\ ~ (ASN1_OID? k) /\ ~ (ASN1_PREFIXED_TERMINAL? k) }) (x: asn1_key_lit k) : Tot (list U8.t) =
  match k with
  | ASN1_BOOLEAN -> let x : bool = x in [if x then 0xFFuy else 0x00uy]
  | ASN1_NULL -> []
  | ASN1_INTEGER bound -> let x : asn1_int_lit bound = x in (x <: list U8.t)
  | ASN1_BITSTRING -> let x : asn1_bitstring_lit = x in fst x :: snd x
  | ASN1_PRINTABLESTRING -> let x : asn1_printablestring_t = x in char_list_bytes x
  | ASN1_IA5STRING -> let x : asn1_ia5string_t = x in char_list_bytes x
  | ASN1_VISIBLESTRING -> let x : asn1_visiblestring_t = x in char_list_bytes x
  | ASN1_NUMERICSTRING -> let x : asn1_numericstring_t = x in char_list_bytes x
  | _ -> let x : list U8.t = x in x

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
let key_enc_list_correct (k: asn1_terminal_k { adb_key_supported k /\ ~ (ASN1_OID? k) /\ ~ (ASN1_PREFIXED_TERMINAL? k) }) (x: asn1_key_lit k)
: Lemma (Seq.seq_of_list (key_enc_list k x) == ASN1.Spec.Content.Enc.leaf_enc k (key_of_lit k x))
= match k with
  | ASN1_BOOLEAN ->
    let x : bool = x in
    let c = if x then 0xFFuy else 0x00uy in
    Seq.lemma_seq_of_list_induction [c];
    Seq.lemma_seq_of_list_induction #U8.t [];
    Seq.lemma_eq_elim (Seq.seq_of_list [c]) (Seq.create 1 c)
  | ASN1_NULL ->
    Seq.lemma_seq_of_list_induction #U8.t [];
    Seq.lemma_eq_elim (Seq.seq_of_list #U8.t []) Seq.empty
  | ASN1_INTEGER bound ->
    ASN1.Spec.Content.Enc.integer_enc_of_lit bound x
  | ASN1_BITSTRING ->
    let x : asn1_bitstring_lit = x in
    Seq.lemma_seq_of_list_induction (fst x :: snd x)
  | ASN1_PRINTABLESTRING ->
    let x' : asn1_printablestring_t = x in
    char_list_bytes_correct #is_printable_char x';
    assert_norm (key_enc_list ASN1_PRINTABLESTRING x == char_list_bytes #is_printable_char x');
    assert_norm (ASN1.Spec.Content.Enc.leaf_enc ASN1_PRINTABLESTRING (key_of_lit ASN1_PRINTABLESTRING x) == ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #is_printable_char) x')
  | ASN1_IA5STRING ->
    let x' : asn1_ia5string_t = x in
    char_list_bytes_correct #is_ia5_char x';
    assert_norm (key_enc_list ASN1_IA5STRING x == char_list_bytes #is_ia5_char x');
    assert_norm (ASN1.Spec.Content.Enc.leaf_enc ASN1_IA5STRING (key_of_lit ASN1_IA5STRING x) == ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #is_ia5_char) x')
  | ASN1_VISIBLESTRING ->
    let x' : asn1_visiblestring_t = x in
    char_list_bytes_correct #is_visible_char x';
    assert_norm (key_enc_list ASN1_VISIBLESTRING x == char_list_bytes #is_visible_char x');
    assert_norm (ASN1.Spec.Content.Enc.leaf_enc ASN1_VISIBLESTRING (key_of_lit ASN1_VISIBLESTRING x) == ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #is_visible_char) x')
  | ASN1_NUMERICSTRING ->
    let x' : asn1_numericstring_t = x in
    char_list_bytes_correct #is_numeric_char x';
    assert_norm (key_enc_list ASN1_NUMERICSTRING x == char_list_bytes #is_numeric_char x');
    assert_norm (ASN1.Spec.Content.Enc.leaf_enc ASN1_NUMERICSTRING (key_of_lit ASN1_NUMERICSTRING x) == ASN1.Spec.Content.Enc.list_enc (ASN1.Spec.Content.Enc.byte_enc #is_numeric_char) x')
  | _ -> ()
#pop-options

[@@asn1_pulse_attr]
let rec validate_bytes_eq ([@@@FStar.Attributes.monomorphize] l: list U8.t)
: Tot (LPS.validator #_ #(SCo.parse_filter_kind asn1_weak_parser_kind) (ADB.bytes_eq_p l))
  (decreases l)
= match l with
  | [] -> ADB.validate_bytes_eq_nil ()
  | h :: tl -> ADB.validate_bytes_eq_cons h tl (validate_bytes_eq tl)

[@@asn1_pulse_attr]
inline_for_extraction
let prefixed_lit (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_key_lit (ASN1_PREFIXED_TERMINAL id2 k2)) : Tot (asn1_key_lit k2) =
  assert_norm (asn1_key_lit (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_key_lit k2);
  coerce_eq () x

#push-options "--fuel 2 --ifuel 2"
let key_of_lit_prefixed (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_key_lit (ASN1_PREFIXED_TERMINAL id2 k2))
: Lemma (key_of_lit (ASN1_PREFIXED_TERMINAL id2 k2) x == AP.pt_val id2 k2 (key_of_lit k2 (prefixed_lit id2 k2 x)))
= ()
#pop-options

[@@asn1_pulse_attr]
let rec validate_key_eq_fl ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (u: squash (adb_key_supported key_k)) ([@@@FStar.Attributes.monomorphize] x: asn1_key_lit key_k) (l: SZ.t)
: Tot (LPS.validator #_ #(SFL.parse_fldata_kind (SZ.v l) (SCo.parse_filter_kind asn1_weak_parser_kind)) (ADB.key_eq_fldata key_k (key_of_lit key_k x) (SZ.v l)))
  (decreases key_k)
= match key_k with
  | ASN1_OID -> PPFL.validate_fldata (validate_key_eq key_k () x) l
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    let x2 = prefixed_lit id2 k2 x in
    key_of_lit_prefixed id2 k2 x;
    Classical.forall_intro (AP.prefixed_key_fldata_consumed id2 k2 (key_of_lit k2 x2) (SZ.v l));
    validate_ext_consumed
      (PPFL.validate_fldata (AP.validate_prefixed_key id2 (fun len -> validate_key_eq_fl k2 () x2 len)) l)
      (ADB.key_eq_fldata key_k (key_of_lit key_k x) (SZ.v l))
  | _ ->
    key_enc_list_correct key_k x;
    Classical.forall_intro (ADB.key_lit_fldata_consumed key_k (key_of_lit key_k x) (key_enc_list key_k x) (SZ.v l));
    validate_ext_consumed (PPFL.validate_fldata (validate_bytes_eq (key_enc_list key_k x)) l) (ADB.key_eq_fldata key_k (key_of_lit key_k x) (SZ.v l))

(* The interpreter *)

(* The recursive validators below take the arguments of `LPS.validator`
   explicitly: Custard (F* 4cb038ec6f) misclassifies the binders of a
   specialized definition that come from the lambdas of its body when the
   definition also has `monomorphize` binders followed by erased ones. *)
unfold
let vres (#t: Type0) (#k: SB.parser_kind) (p: SB.parser k t)
  (input: slice byte) (poffset: R.ref SZ.t) (offset: Ghost.erased SZ.t) (pm: perm) (v: Ghost.erased bytes)
: Type
= stt bool
    (pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v))
    (fun res -> pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (LPS.validator_postcond p offset v off res)))

[@@asn1_pulse_attr]
let validate_restricted ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] r: asn1_restriction k) (u: squash (supported_restriction k r))
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) vinput vpoffset voffset vpm vv)
= [@inline_let] let vf : LPS.validator #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) =
  (match k with
  | ASN1_BOOLEAN ->
    Rs.validate_boolean_in (RESTRICT_IN?.values r)
  | ASN1_INTEGER bound ->
    Rs.validate_integer_restricted (U64.uint_to_t bound) r
  | ASN1_OCTETSTRING -> Rs.validate_string_size k r Term.validate_octetstring
  | ASN1_UTF8STRING -> Rs.validate_string_size k r Term.validate_utf8
  | ASN1_BMPSTRING -> Rs.validate_string_size k r Term.validate_bmp
  | ASN1_UNIVERSALSTRING -> Rs.validate_string_size k r Term.validate_universal
  | ASN1_PRINTABLESTRING -> Rs.validate_string_size k r Term.validate_printable
  | ASN1_IA5STRING -> Rs.validate_string_size k r Term.validate_ia5
  | ASN1_VISIBLESTRING -> Rs.validate_string_size k r Term.validate_visible
  | ASN1_NUMERICSTRING -> Rs.validate_string_size k r Term.validate_numeric
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR -> Rs.validate_string_size k r (Term.validate_raw_string k))
  in vf vinput vpoffset #voffset #vpm #vv

[@@asn1_pulse_attr]
let rec validate_terminal ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) (u: squash (supported_terminal k))
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k) vinput vpoffset voffset vpm vv)
  (decreases k)
= [@inline_let] let vf : LPS.validator #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k) =
  (match k with
  | ASN1_BOOLEAN -> Term.validate_boolean
  | ASN1_INTEGER bound ->
    Term.validate_integer (U64.uint_to_t bound)
  | ASN1_BITSTRING -> Term.validate_bitstring
  | ASN1_OCTETSTRING -> Term.validate_octetstring
  | ASN1_UTF8STRING -> Term.validate_utf8
  | ASN1_PRINTABLESTRING -> Term.validate_printable
  | ASN1_IA5STRING -> Term.validate_ia5
  | ASN1_VISIBLESTRING -> Term.validate_visible
  | ASN1_BMPSTRING -> Term.validate_bmp
  | ASN1_UNIVERSALSTRING -> Term.validate_universal
  | ASN1_TELETEXSTRING -> Term.validate_raw_string k
  | ASN1_NUMERICSTRING -> Term.validate_numeric
  | ASN1_VIDEOTEXSTRING -> Term.validate_raw_string k
  | ASN1_GRAPHICSTRING -> Term.validate_raw_string k
  | ASN1_GENERALSTRING -> Term.validate_raw_string k
  | ASN1_OBJECTDESCRIPTOR -> Term.validate_raw_string k
  | ASN1_NULL -> Term.validate_null
  | ASN1_OID -> ASN1.Pulse.OID.validate_oid
  | ASN1_RELATIVE_OID -> ASN1.Pulse.OID.validate_relative_oid
  | ASN1_OID_IRI -> Term.validate_oid_iri
  | ASN1_RELATIVE_OID_IRI -> Term.validate_relative_oid_iri
  | ASN1_UTCTIME -> Term.validate_utctime
  | ASN1_GENERALIZEDTIME -> Term.validate_generalizedtime
  | ASN1_DATE -> Term.validate_date
  | ASN1_TIME_OF_DAY -> Term.validate_timeofday
  | ASN1_DATE_TIME -> Term.validate_datetime
  | ASN1_PREFIXED_TERMINAL id k' ->
    LPS.validate_weaken asn1_weak_parser_kind
      (ILC.validate_asn1_ILC id #(ASN1_TERMINAL k') #(asn1_terminal_as_parser k') (validate_terminal k' ())))
  in vf vinput vpoffset #voffset #vpm #vv

[@@asn1_pulse_attr]
let validate_default_lc ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] defl: asn1_key_lit k) (u: squash (supported_default k))
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres (DL.lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (defaultv_filter (key_of_lit k defl)))) vinput vpoffset voffset vpm vv)
= [@inline_let] let vf : LPS.validator (DL.lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (defaultv_filter (key_of_lit k defl)))) =
    DL.validate_lc_fl (fun len ->
      Classical.forall_intro (DL.neq_fl_consumed k (key_of_lit k defl) (SZ.v len));
      DL.validate_neq (validate_key_eq_fl k () defl len) (PPFL.validate_fldata (validate_terminal k ()) len)
        (SFL.parse_fldata (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (defaultv_filter (key_of_lit k defl))) (SZ.v len)))
  in vf vinput vpoffset #voffset #vpm #vv

[@@asn1_pulse_attr]
let validate_default_restricted_lc ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] r: asn1_restriction k) ([@@@FStar.Attributes.monomorphize] defl: asn1_key_lit k { restriction_pred r (key_of_lit k defl) }) (u: squash (supported_default_restricted k r))
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres (DL.lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (C.restricted_default_filter r (key_of_lit k defl)))) vinput vpoffset voffset vpm vv)
= [@inline_let] let vf : LPS.validator (DL.lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (C.restricted_default_filter r (key_of_lit k defl)))) =
    DL.validate_lc_fl (fun len ->
      Classical.forall_intro (DL.neq_fl_restricted_consumed k r (key_of_lit k defl) (SZ.v len));
      DL.validate_neq (validate_key_eq_fl k () defl len) (PPFL.validate_fldata (validate_restricted k r ()) len)
        (SFL.parse_fldata (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (C.restricted_default_filter r (key_of_lit k defl))) (SZ.v len)))
  in vf vinput vpoffset #voffset #vpm #vv

let rec validate_content ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (u: squash (supported_content k))
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #(asn1_content_t k) #asn1_weak_parser_kind (asn1_content_as_parser k) vinput vpoffset voffset vpm vv)
  (decreases %[k; 2])
= [@inline_let] let vf : LPS.validator #(asn1_content_t k) #asn1_weak_parser_kind (asn1_content_as_parser k) =
  (match k with
  | ASN1_TERMINAL k' -> validate_terminal k' ()
  | ASN1_RESTRICTED_TERMINAL k' r -> validate_restricted k' r ()
  | ASN1_SEQUENCE gitems ->
    LPS.validate_ext (validate_seq (dsnd gitems) () None) #asn1_weak_parser_kind (asn1_content_as_parser k)
  | ASN1_SEQUENCE_OF ne k' ->
    C.validate_sized_list ne (validate_k k' ())
  | ASN1_SET_OF ne k' ->
    SO.validate_sized_set ne (validate_k k' ())
  | ASN1_SET _ items _ ->
    ASN1.Spec.Conformance.items_tagged_intro items;
    LPS.validate_ext
      (SC.validate_set (Ghost.hide (twins_of items))
        (fun id -> set_comp items () 0ul id)
        (fun m -> set_final items 0ul m)
        (fun id -> validate_set_elem_twin items () id))
      #asn1_weak_parser_kind (asn1_content_as_parser k)
  | ASN1_PREFIXED k' ->
    LPS.validate_weaken asn1_weak_parser_kind (validate_k k' ())
  | ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls ofb pf pf' ->
    begin match prefix with
    | ASN1_GEN_ITEMS_NIL ->
      let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
      begin match ofb with
      | None ->
        Classical.forall_intro (ADB.adb_content_none kid key_k ls pf pf');
        validate_ext_consumed
          (ADB.validate_adb kid key_k
            (ASN1.Spec.Choice.tag_of_gen_choice_type (ASN1.Spec.Choice.extract_types lp))
            (ASN1.Spec.Any.make_gen_choice_weak_payload_parser lp)
            (fun l -> validate_disp key_k () ls () l))
          (asn1_content_as_parser k)
      | Some fb ->
        Classical.forall_intro (ADB.adb_content_some kid key_k ls fb pf pf');
        validate_ext_consumed
          (ADB.validate_adb kid key_k
            (ASN1.Spec.Any.tag_of_gen_choice_type_with_fallback (ASN1.Spec.Choice.extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb)))
            (ASN1.Spec.Any.make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb))
            (fun l -> validate_disp_fb key_k () ls () fb (Ghost.hide k) () l))
          (asn1_content_as_parser k)
      end
    | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
      let lp = asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls in
      begin match ofb with
      | None ->
        Classical.forall_intro (ADB.adb_prefix_content_none ipd prefix kid key_k ls pf pf');
        let sfx = ADB.adb_sfx_none kid key_k ls in
        Classical.forall_intro (ADB.adb_sfx_none_eq kid key_k ls None);
        Classical.forall_intro_2 (fun id -> ADB.adb_sfx_none_eq kid key_k ls (Some id));
        validate_ext_consumed
          (validate_seqa prefix () sfx
            (validate_ext_consumed
              (ADB.validate_adb kid key_k
                (ASN1.Spec.Choice.tag_of_gen_choice_type (ASN1.Spec.Choice.extract_types lp))
                (ASN1.Spec.Any.make_gen_choice_weak_payload_parser lp)
                (fun l -> validate_disp key_k () ls () l))
              (Mkparsertwin?.p sfx))
            (fun id -> validate_ext_consumed
              (ADB.validate_adb_twin kid key_k
                (ASN1.Spec.Choice.tag_of_gen_choice_type (ASN1.Spec.Choice.extract_types lp))
                (ASN1.Spec.Any.make_gen_choice_weak_payload_parser lp)
                (fun l -> validate_disp key_k () ls () l) id)
              (Mkparsertwin?.fp sfx id))
            None)
          (asn1_content_as_parser k)
      | Some fb ->
        Classical.forall_intro (ADB.adb_prefix_content_some ipd prefix kid key_k ls fb pf pf');
        let sfx = ADB.adb_sfx_some kid key_k ls fb in
        Classical.forall_intro (ADB.adb_sfx_some_eq kid key_k ls fb None);
        Classical.forall_intro_2 (fun id -> ADB.adb_sfx_some_eq kid key_k ls fb (Some id));
        validate_ext_consumed
          (validate_seqa prefix () sfx
            (validate_ext_consumed
              (ADB.validate_adb kid key_k
                (ASN1.Spec.Any.tag_of_gen_choice_type_with_fallback (ASN1.Spec.Choice.extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb)))
                (ASN1.Spec.Any.make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb))
                (fun l -> validate_disp_fb key_k () ls () fb (Ghost.hide k) () l))
              (Mkparsertwin?.p sfx))
            (fun id -> validate_ext_consumed
              (ADB.validate_adb_twin kid key_k
                (ASN1.Spec.Any.tag_of_gen_choice_type_with_fallback (ASN1.Spec.Choice.extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb)))
                (ASN1.Spec.Any.make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb))
                (fun l -> validate_disp_fb key_k () ls () fb (Ghost.hide k) () l) id)
              (Mkparsertwin?.fp sfx id))
            None)
          (asn1_content_as_parser k)
      end
    end)
  in vf vinput vpoffset #voffset #vpm #vv

and validate_disp ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (u: squash (adb_key_supported key_k))
  ([@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u': squash (supported_ls ls)) (l: SZ.t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #(ADB.disp_kind (SZ.v l)) (ADB.choice_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (SZ.v l)) vinput vpoffset voffset vpm vv)
  (decreases %[ls; 1])
= [@inline_let] let vf : LPS.validator #_ #(ADB.disp_kind (SZ.v l)) (ADB.choice_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (SZ.v l)) =
  (match ls with
  | [] ->
    Classical.forall_intro (ADB.choice_disp_nil key_k (SZ.v l));
    validate_fail (ADB.choice_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (SZ.v l)) ()
  | (x, y) :: tl ->
    Classical.forall_intro (ADB.choice_disp_cons key_k (key_of_lit key_k x) (ADB.adb_fb y) (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl) (SZ.v l));
    ADB.validate_try_else
      (validate_key_eq_fl key_k () x l)
      (LPS.validate_ext (validate_seq (dsnd y) () None) #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)))
      (validate_disp key_k () tl () l)
      (ADB.choice_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (SZ.v l)))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_disp_fb ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (u: squash (adb_key_supported key_k))
  ([@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (u': squash (supported_ls ls))
  ([@@@FStar.Attributes.monomorphize] fb: asn1_gen_items_lk)
  (kt: Ghost.erased asn1_content_k)
  (u'': squash (ls << Ghost.reveal kt /\ fb << Ghost.reveal kt /\ supported_items (dsnd fb)))
  (l: SZ.t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #(ADB.disp_kind (SZ.v l)) (ADB.choice_fb_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (ADB.adb_fb fb) (SZ.v l)) vinput vpoffset voffset vpm vv)
  (decreases %[Ghost.reveal kt; 1; ls])
= [@inline_let] let vf : LPS.validator #_ #(ADB.disp_kind (SZ.v l)) (ADB.choice_fb_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (ADB.adb_fb fb) (SZ.v l)) =
  (match ls with
  | [] ->
    Classical.forall_intro (ADB.choice_fb_disp_nil key_k (ADB.adb_fb fb) (SZ.v l));
    ADB.validate_then_consumed
      (PPFL.validate_fldata (validate_terminal key_k ()) l)
      (LPS.validate_ext (validate_seq (dsnd fb) () None) #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb fb)))
      (ADB.choice_fb_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (ADB.adb_fb fb) (SZ.v l))
  | (x, y) :: tl ->
    Classical.forall_intro (ADB.choice_fb_disp_cons key_k (key_of_lit key_k x) (ADB.adb_fb y) (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) tl) (ADB.adb_fb fb) (SZ.v l));
    ADB.validate_try_else
      (validate_key_eq_fl key_k () x l)
      (LPS.validate_ext (validate_seq (dsnd y) () None) #asn1_weak_parser_kind (Mkgenparser?.p (ADB.adb_fb y)))
      (validate_disp_fb key_k () tl () fb kt () l)
      (ADB.choice_fb_disp_p key_k (asn1_ls_as_parser (asn1_terminal_t key_k) (key_of_lit key_k) ls) (ADB.adb_fb fb) (SZ.v l)))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_k (#[@@@FStar.Attributes.monomorphize] s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (u: squash (supported_k k))
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k) vinput vpoffset voffset vpm vv)
  (decreases %[k; 1])
= [@inline_let] let vf : LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k) =
  ((match k with
  | ASN1_ILC id k' -> ILC.validate_asn1_ILC id (validate_content k' ())
  | ASN1_CHOICE_ILC lc pf ->
    C.asn1_choice_id_then lc pf;
    C.validate_id_then (asn1_as_parser k) (Ghost.hide (snd (asn1_as_parser_twin k))) (fun id -> validate_k_twin k () id) ()
  | ASN1_ANY_ILC -> Any.validate_any))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_k_twin (#[@@@FStar.Attributes.monomorphize] s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (u: squash (supported_k k)) (id: asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #(asn1_t k) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id) vinput vpoffset voffset vpm vv)
  (decreases %[k; 0])
= [@inline_let] let vf : LPS.validator #(asn1_t k) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id) =
  ((match k with
  | ASN1_ILC id0 k' ->
    LPS.ifthenelse_validator (snd (asn1_as_parser_twin k) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> LPS.validate_ext (ILC.validate_asn1_LC (validate_content k' ())) #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id))
      (fun _ -> validate_fail (snd (asn1_as_parser_twin k) id) ())
  | ASN1_CHOICE_ILC lc pf ->
    Classical.forall_intro (C.asn1_choice_twin_consumed lc pf id);
    validate_ext_consumed (validate_choice_payload lc () id) (snd (asn1_as_parser_twin k) id)
  | ASN1_ANY_ILC -> Any.validate_any_twin id))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_choice_payload ([@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (u: squash (supported_lc lc)) (id: asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_strong_parser_kind (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) vinput vpoffset voffset vpm vv)
  (decreases %[lc; 0])
= [@inline_let] let vf : LPS.validator #_ #asn1_strong_parser_kind (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) =
  (match lc with
  | [] -> validate_fail (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) ()
  | (id', ck) :: tl ->
    Classical.forall_intro (C.asn1_choice_payload_cons id' ck tl id);
    LPS.ifthenelse_validator (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) (ILC.asn1_id_eq id id')
      (fun _ -> validate_ext_consumed (ILC.validate_asn1_LC (validate_content ck ())) (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id))
      (fun _ -> validate_ext_consumed (validate_choice_payload tl () id) (ASN1.Spec.Choice.make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id)))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_dec_twin (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) ([@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (u: squash (supported_dec dk)) (id: asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (twin_of dk) id) vinput vpoffset voffset vpm vv)
  (decreases %[dk; 0])
= [@inline_let] let vf : LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (twin_of dk) id) =
  (match dk with
  | ASN1_PLAIN_ILC k ->
    validate_item_twin_plain (twin_of dk) id (validate_k_twin k () id)
  | ASN1_OPTION_ILC k ->
    validate_item_twin_option (twin_of dk) id (validate_k_twin k () id)
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    Classical.forall_intro (C.default_terminal_twin_consumed id0 #k defv id);
    Classical.forall_intro (DL.default_lc_consumed k (key_of_lit k defv));
    LPS.ifthenelse_validator (parse_asn1_sequence_item_twin (twin_of dk) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> validate_ext_consumed (validate_default_lc k defv ()) (parse_asn1_sequence_item_twin (twin_of dk) id))
      (fun _ -> validate_fail (parse_asn1_sequence_item_twin (twin_of dk) id) ())
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    Classical.forall_intro (C.default_restricted_twin_consumed id0 #k r defv id);
    Classical.forall_intro (DL.default_restricted_lc_consumed k r (key_of_lit k defv));
    LPS.ifthenelse_validator (parse_asn1_sequence_item_twin (twin_of dk) id) (ILC.asn1_id_eq id0 id)
      (fun _ -> validate_ext_consumed (validate_default_restricted_lc k r defv ()) (parse_asn1_sequence_item_twin (twin_of dk) id))
      (fun _ -> validate_fail (parse_asn1_sequence_item_twin (twin_of dk) id) ()))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_seq (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (supported_items ls)) (st: option asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_weak_parser_kind (seq_p (twins_of ls) st) vinput vpoffset voffset vpm vv)
  (decreases %[ls; 1])
= [@inline_let] let vf : LPS.validator #_ #asn1_weak_parser_kind (seq_p (twins_of ls) st) =
  (match ls with
  | ASN1_GEN_ITEMS_NIL -> validate_seq_nil st
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    all_defaultable_correct ls;
    validate_seq_cons (twins_of ls) (all_defaultable ls) (validate_seq_body ls ()) st)
  in vf vinput vpoffset #voffset #vpm #vv

and validate_seq_body (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (supported_items ls /\ Cons? (twins_of ls))) (id: asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_weak_parser_kind (seq_p (twins_of ls) (Some id)) vinput vpoffset voffset vpm vv)
  (decreases %[ls; 0])
= [@inline_let] let vf : LPS.validator #_ #asn1_weak_parser_kind (seq_p (twins_of ls) (Some id)) =
  (match ls with
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    let hd = Ghost.hide (twin_of dk) in
    match tl with
    | ASN1_GEN_ITEMS_NIL ->
      validate_seq_single_body hd id (validate_dec_twin dk () id)
    | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
      validate_seq_cons_cons_body hd (twins_of tl) id
        (has_id_dec dk () id)
        (PLAIN? d)
        (validate_dec_twin dk () id)
        (validate_seq tl ()))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_seqa (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (supported_items ls)) (#t: Type0)
  (sfx: Ghost.erased (parser_twin asn1_weak_parser_kind t))
  ([@@@FStar.Attributes.monomorphize] vp: LPS.validator #t #asn1_weak_parser_kind (Mkparsertwin?.p sfx))
  ([@@@FStar.Attributes.monomorphize] vfp: (id: asn1_id_t) -> LPS.validator #t #asn1_weak_parser_kind (Mkparsertwin?.fp sfx id))
  (st: option asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_weak_parser_kind (SA.seqa_p (twins_of ls) sfx st) vinput vpoffset voffset vpm vv)
  (decreases %[ls; 1])
= [@inline_let] let vf : LPS.validator #_ #asn1_weak_parser_kind (SA.seqa_p (twins_of ls) sfx st) =
  (match ls with
  | ASN1_GEN_ITEMS_NIL -> SA.validate_seqa_nil sfx vp vfp st
  | ASN1_GEN_ITEMS_CONS _ _ _ _ _ ->
    SA.validate_seqa_cons (Ghost.hide (twins_of ls)) sfx (validate_seqa_body ls () sfx vp vfp) st)
  in vf vinput vpoffset #voffset #vpm #vv

and validate_seqa_body (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (supported_items ls /\ Cons? (twins_of ls))) (#t: Type0)
  (sfx: Ghost.erased (parser_twin asn1_weak_parser_kind t))
  ([@@@FStar.Attributes.monomorphize] vp: LPS.validator #t #asn1_weak_parser_kind (Mkparsertwin?.p sfx))
  ([@@@FStar.Attributes.monomorphize] vfp: (id: asn1_id_t) -> LPS.validator #t #asn1_weak_parser_kind (Mkparsertwin?.fp sfx id))
  (id: asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_weak_parser_kind (SA.seqa_body (twins_of ls) sfx id) vinput vpoffset voffset vpm vv)
  (decreases %[ls; 0])
= [@inline_let] let vf : LPS.validator #_ #asn1_weak_parser_kind (SA.seqa_body (twins_of ls) sfx id) =
  (match ls with
  | ASN1_GEN_ITEMS_CONS s d dk _ tl ->
    SA.validate_seqa_body (Ghost.hide (twin_of dk)) (Ghost.hide (twins_of tl)) sfx id
      (has_id_dec dk () id)
      (PLAIN? d)
      (validate_dec_twin dk () id)
      (validate_seqa tl () sfx vp vfp))
  in vf vinput vpoffset #voffset #vpm #vv

and validate_set_elem_twin (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (supported_items ls)) (id: asn1_id_t)
  (vinput: slice byte) (vpoffset: R.ref SZ.t) (#voffset: Ghost.erased SZ.t) (#vpm: perm) (#vv: Ghost.erased bytes)
: Tot (vres #_ #asn1_strong_parser_kind (ASN1.Spec.SetComponents.parse_set_elem_twin (twins_of ls) id) vinput vpoffset voffset vpm vv)
  (decreases %[ls; 0])
= [@inline_let] let vf : LPS.validator #_ #asn1_strong_parser_kind (ASN1.Spec.SetComponents.parse_set_elem_twin (twins_of ls) id) =
  (match ls with
  | ASN1_GEN_ITEMS_NIL -> validate_fail (ASN1.Spec.SetComponents.parse_set_elem_twin (twins_of ls) id) ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let p = ASN1.Spec.SetComponents.parse_set_elem_twin (twins_of ls) id in
    Classical.forall_intro (SC.set_elem_twin_cons_consumed (twin_of dk) (twins_of tl) id);
    LPS.ifthenelse_validator p (has_id_dec dk () id)
      (fun _ -> validate_ext_consumed (validate_dec_twin dk () id) #_ #asn1_strong_parser_kind p)
      (fun _ -> validate_ext_consumed (validate_set_elem_twin tl () id) #_ #asn1_strong_parser_kind p)
)
  in vf vinput vpoffset #voffset #vpm #vv