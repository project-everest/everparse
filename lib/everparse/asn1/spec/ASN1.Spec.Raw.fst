module ASN1.Spec.Raw

(* Raw values of ASN.1 DER schemas: the type `asn1_raw_t k` has the same
   structure as `asn1_t k`, but without any value conditions: no character
   sets, integer bounds, restrictions, sizes, or exclusion of DEFAULT
   values.

   `forget k` maps a typed value to its raw value, and `check k` maps a raw
   value back to a typed value if possible:
   - leaf values, restrictions and SIZE (1..MAX) constraints are checked;
   - a DEFAULT component explicitly set to its default value becomes
     `Default`;
   - the elements of a SET OF are sorted by the lexicographic order of
     their encodings (X.690 11.6.)
   `check_ser k` additionally checks that the resulting value is
   encodable.

   Round trip: `check k (forget k x) == Some x` for every typed value `x`
   whose SET OF elements are sorted (`canonical k x`), and
   `check_ser k (forget k x) == Some x` for every encodable such `x`. *)

open ASN1.Bytes
open ASN1.Spec.Time
open ASN1.Spec.IRI
open ASN1.Base
open ASN1.Spec.Serializer

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module List = FStar.List.Tot
module Set = FStar.Set
module LPC = LowParse.Spec.Combinators
module Conf = ASN1.Spec.Conformance
module Inj = ASN1.Spec.ToValue.Inj
module Set_ = ASN1.Spec.Set

(* Leaves *)

let rec asn1_raw_terminal_t (k: asn1_terminal_k) : Tot eqtype (decreases k) =
  match k with
  | ASN1_BOOLEAN -> bool
  | ASN1_NULL -> unit
  | ASN1_INTEGER _ -> int
  | ASN1_BITSTRING -> (U8.t & asn1_bytes)
  | ASN1_PRINTABLESTRING
  | ASN1_IA5STRING
  | ASN1_VISIBLESTRING
  | ASN1_NUMERICSTRING -> list U8.t
  | ASN1_OID
  | ASN1_RELATIVE_OID -> list U32.t
  | ASN1_PREFIXED_TERMINAL _ k' -> asn1_raw_terminal_t k'
  | _ -> asn1_bytes

let char_t (p: U8.t -> Tot bool) = (b: U8.t { p b })

let rec forget_chars (p: U8.t -> Tot bool) (l: list (char_t p)) : Tot (list U8.t) =
  match l with
  | [] -> []
  | a :: q -> (a <: U8.t) :: forget_chars p q

let rec check_chars (p: U8.t -> Tot bool) (l: list U8.t) : Tot (option (list (char_t p))) =
  match l with
  | [] -> Some []
  | a :: q ->
    if p a
    then match check_chars p q with
      | Some q' -> Some ((a <: char_t p) :: q')
      | None -> None
    else None

let rec check_forget_chars (p: U8.t -> Tot bool) (l: list (char_t p))
: Lemma (check_chars p (forget_chars p l) == Some l)
= match l with
  | [] -> ()
  | _ :: q -> check_forget_chars p q

let rec forget_check_chars (p: U8.t -> Tot bool) (l: list U8.t)
: Lemma (match check_chars p l with
    | Some l' -> forget_chars p l' == l
    | None -> True)
= match l with
  | [] -> ()
  | _ :: q -> forget_check_chars p q

let printable_eq () : Lemma (asn1_printablestring_t == list (char_t is_printable_char)) =
  assert_norm (asn1_printablestring_t == list (char_t is_printable_char))

let ia5_eq () : Lemma (asn1_ia5string_t == list (char_t is_ia5_char)) =
  assert_norm (asn1_ia5string_t == list (char_t is_ia5_char))

let visible_eq () : Lemma (asn1_visiblestring_t == list (char_t is_visible_char)) =
  assert_norm (asn1_visiblestring_t == list (char_t is_visible_char))

let numeric_eq () : Lemma (asn1_numericstring_t == list (char_t is_numeric_char)) =
  assert_norm (asn1_numericstring_t == list (char_t is_numeric_char))

let interval_b (bound: pos) (x: int) : Tot (b: bool { b <==> ASN1.Spec.Content.INTEGER.interval bound x }) =
  let a = pow2 (8 * bound - 1) in
  0 - a <= x && x < a

let bitstring_ok (u: U8.t) (b: asn1_bytes) : Tot bool =
  U8.v u <= 7 &&
  (let _ = pow2_le (U8.v u) in
   U8.v u = 0 ||
   (Seq.length b > 0 &&
    FStar.UInt.mod (U8.v (Seq.index b (Seq.length b - 1))) (pow2 (U8.v u)) = 0))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec forget_terminal (k: asn1_terminal_k) (x: asn1_terminal_t k) : Tot (asn1_raw_terminal_t k) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id' k' ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_terminal_t k');
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_raw_terminal_t k');
    let x' : asn1_terminal_t k' = coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k') () x in
    coerce_eq #(asn1_raw_terminal_t k') #(asn1_raw_terminal_t k) () (forget_terminal k' x')
  | ASN1_BOOLEAN -> x
  | ASN1_NULL -> x
  | ASN1_INTEGER _ -> x
  | ASN1_BITSTRING ->
    let x' : asn1_bitstring_t = x in
    Mktuple2 #U8.t #asn1_bytes (BYTES_WITH_UNUSEDBITS?.unused x') (BYTES_WITH_UNUSEDBITS?.b x')
  | ASN1_PRINTABLESTRING -> printable_eq (); forget_chars is_printable_char (coerce_eq #asn1_printablestring_t #(list (char_t is_printable_char)) () x)
  | ASN1_IA5STRING -> ia5_eq (); forget_chars is_ia5_char (coerce_eq #asn1_ia5string_t #(list (char_t is_ia5_char)) () x)
  | ASN1_VISIBLESTRING -> visible_eq (); forget_chars is_visible_char (coerce_eq #asn1_visiblestring_t #(list (char_t is_visible_char)) () x)
  | ASN1_NUMERICSTRING -> numeric_eq (); forget_chars is_numeric_char (coerce_eq #asn1_numericstring_t #(list (char_t is_numeric_char)) () x)
  | ASN1_OID -> let x' : asn1_oid_t = x in (x' <: list U32.t)
  | ASN1_RELATIVE_OID -> let x' : asn1_relative_oid_t = x in (x' <: list U32.t)
  | ASN1_OCTETSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_UTF8STRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME -> (x <: asn1_bytes)

let rec check_terminal (k: asn1_terminal_k) (x: asn1_raw_terminal_t k) : Tot (option (asn1_terminal_t k)) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL id' k' ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_terminal_t k');
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_raw_terminal_t k');
    let x' : asn1_raw_terminal_t k' = coerce_eq #(asn1_raw_terminal_t k) #(asn1_raw_terminal_t k') () x in
    coerce_eq #(option (asn1_terminal_t k')) #(option (asn1_terminal_t k)) () (check_terminal k' x')
  | ASN1_BOOLEAN -> Some x
  | ASN1_NULL -> Some x
  | ASN1_INTEGER bound -> let x' : int = x in if interval_b bound x' then Some x' else None
  | ASN1_BITSTRING ->
    let x' : (U8.t & asn1_bytes) = x in
    let (u, b) = x' in
    if bitstring_ok u b then Some (BYTES_WITH_UNUSEDBITS u b) else None
  | ASN1_PRINTABLESTRING -> printable_eq (); coerce_eq #(option (list (char_t is_printable_char))) #(option asn1_printablestring_t) () (check_chars is_printable_char x)
  | ASN1_IA5STRING -> ia5_eq (); coerce_eq #(option (list (char_t is_ia5_char))) #(option asn1_ia5string_t) () (check_chars is_ia5_char x)
  | ASN1_VISIBLESTRING -> visible_eq (); coerce_eq #(option (list (char_t is_visible_char))) #(option asn1_visiblestring_t) () (check_chars is_visible_char x)
  | ASN1_NUMERICSTRING -> numeric_eq (); coerce_eq #(option (list (char_t is_numeric_char))) #(option asn1_numericstring_t) () (check_chars is_numeric_char x)
  | ASN1_OID -> let x' : list U32.t = x in if asn1_OID_wf x' then Some x' else None
  | ASN1_RELATIVE_OID -> let x' : list U32.t = x in if asn1_relative_oid_wf x' then Some x' else None
  | ASN1_UTF8STRING -> let x' : asn1_bytes = x in if LowParse.Spec.UTF8.correct x' then Some x' else None
  | ASN1_BMPSTRING -> let x' : asn1_bytes = x in if is_valid_bmp x' then Some x' else None
  | ASN1_UNIVERSALSTRING -> let x' : asn1_bytes = x in if is_valid_universal x' then Some x' else None
  | ASN1_OID_IRI -> let x' : asn1_bytes = x in if is_valid_oid_iri x' then Some x' else None
  | ASN1_RELATIVE_OID_IRI -> let x' : asn1_bytes = x in if is_valid_relative_oid_iri x' then Some x' else None
  | ASN1_UTCTIME -> let x' : asn1_bytes = x in if is_valid_ASN1UTCTIME x' then Some x' else None
  | ASN1_GENERALIZEDTIME -> let x' : asn1_bytes = x in if is_valid_ASN1GENERALIZEDTIME x' then Some x' else None
  | ASN1_DATE -> let x' : asn1_bytes = x in if is_valid_ASN1DATE x' then Some x' else None
  | ASN1_TIME_OF_DAY -> let x' : asn1_bytes = x in if is_valid_ASN1TIMEOFDAY x' then Some x' else None
  | ASN1_DATE_TIME -> let x' : asn1_bytes = x in if is_valid_ASN1DATETIME x' then Some x' else None
  | ASN1_OCTETSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR -> Some x

let rec check_forget_terminal (k: asn1_terminal_k) (x: asn1_terminal_t k)
: Lemma (ensures (check_terminal k (forget_terminal k x) == Some x)) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id' k' ->
    assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_terminal_t k');
    check_forget_terminal k' (coerce_eq #(asn1_terminal_t k) #(asn1_terminal_t k') () x)
  | ASN1_PRINTABLESTRING -> printable_eq (); check_forget_chars is_printable_char (coerce_eq #asn1_printablestring_t #(list (char_t is_printable_char)) () x)
  | ASN1_IA5STRING -> ia5_eq (); check_forget_chars is_ia5_char (coerce_eq #asn1_ia5string_t #(list (char_t is_ia5_char)) () x)
  | ASN1_VISIBLESTRING -> visible_eq (); check_forget_chars is_visible_char (coerce_eq #asn1_visiblestring_t #(list (char_t is_visible_char)) () x)
  | ASN1_NUMERICSTRING -> numeric_eq (); check_forget_chars is_numeric_char (coerce_eq #asn1_numericstring_t #(list (char_t is_numeric_char)) () x)
  | ASN1_INTEGER bound -> ASN1.Spec.Content.INTEGER.interval_equiv bound x
  | _ -> ()

let rec forget_check_terminal (k: asn1_terminal_k) (x: asn1_raw_terminal_t k)
: Lemma (ensures (match check_terminal k x with
    | Some y -> forget_terminal k y == x
    | None -> True)) (decreases k)
= match k with
  | ASN1_PREFIXED_TERMINAL id' k' ->
    assert_norm (asn1_raw_terminal_t (ASN1_PREFIXED_TERMINAL id' k') == asn1_raw_terminal_t k');
    forget_check_terminal k' (coerce_eq #(asn1_raw_terminal_t k) #(asn1_raw_terminal_t k') () x)
  | ASN1_PRINTABLESTRING -> printable_eq (); forget_check_chars is_printable_char x
  | ASN1_IA5STRING -> ia5_eq (); forget_check_chars is_ia5_char x
  | ASN1_VISIBLESTRING -> visible_eq (); forget_check_chars is_visible_char x
  | ASN1_NUMERICSTRING -> numeric_eq (); forget_check_chars is_numeric_char x
  | _ -> ()
#pop-options

let forget_terminal_inj (k: asn1_terminal_k) (x1 x2: asn1_terminal_t k)
: Lemma (requires (forget_terminal k x1 == forget_terminal k x2)) (ensures (x1 == x2))
= check_forget_terminal k x1;
  check_forget_terminal k x2

let raw_key_of_lit (k: asn1_terminal_k) (l: asn1_key_lit k) : Tot (asn1_raw_terminal_t k) =
  forget_terminal k (key_of_lit k l)

(* Raw values *)

let rec asn1_raw_content_t (k: asn1_content_k) : Tot Type (decreases k) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> asn1_raw_terminal_t k'
  | ASN1_TERMINAL k' -> asn1_raw_terminal_t k'
  | ASN1_SEQUENCE gitems -> raw_items_t (dsnd gitems)
  | ASN1_SET _ items _ -> raw_items_t items
  | ASN1_SEQUENCE_OF _ k' -> list (asn1_raw_t k')
  | ASN1_SET_OF _ k' -> list (asn1_raw_t k')
  | ASN1_PREFIXED k' -> asn1_raw_t k'
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    let suffix_t =
      (match ofb with
      | None -> make_gen_choice_type (raw_any_t_core key_k ls)
      | Some fb -> make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t (dsnd fb))) in
    raw_items_any_t prefix suffix_t

and raw_any_t_core (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Tot (list (asn1_raw_terminal_t key_k & Type)) (decreases ls) =
  match ls with
  | [] -> []
  | h :: tl ->
    let (x, y) = h in
    (raw_key_of_lit key_k x, raw_items_t (dsnd y)) :: raw_any_t_core key_k tl

and raw_lc_t (lc: list (asn1_id_t & asn1_content_k)) : Tot (list (asn1_id_t & Type)) (decreases lc) =
  match lc with
  | [] -> []
  | h :: t ->
    let (x, y) = h in
    (x, asn1_raw_content_t y) :: raw_lc_t t

and asn1_raw_t (#s: _) (k: asn1_k s) : Tot Type (decreases k) =
  match k with
  | ASN1_ILC _ k' -> asn1_raw_content_t k'
  | ASN1_CHOICE_ILC lc _ -> make_gen_choice_type (raw_lc_t lc)
  | ASN1_ANY_ILC -> asn1_value

and raw_dec_t (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot Type (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> asn1_raw_t k
  | ASN1_OPTION_ILC k -> option (asn1_raw_t k)
  | ASN1_DEFAULT_TERMINAL _ #k _ -> option (asn1_raw_terminal_t k)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k _ _ -> option (asn1_raw_terminal_t k)

and raw_items_t (#ids: _) (items: asn1_gen_items_l ids) : Tot Type (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> unit
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> raw_dec_t dk
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> raw_dec_t dk & raw_items_t tl

and raw_items_any_t (#ids: _) (items: asn1_gen_items_l ids) (suffix_t: Type) : Tot Type (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> suffix_t
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> raw_dec_t dk & suffix_t
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> raw_dec_t dk & raw_items_any_t tl suffix_t

let typed_any_t (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) : Tot (list (asn1_terminal_t key_k & Type)) =
  asn1_any_t_core (asn1_terminal_t key_k) (key_of_lit key_k) ls

let forget_key_ne (key_k: asn1_terminal_k) (key: asn1_terminal_t key_k) (l: asn1_key_lit key_k)
: Lemma (requires (~ (key == key_of_lit key_k l)))
  (ensures (~ (forget_terminal key_k key == raw_key_of_lit key_k l)))
= FStar.Classical.move_requires (forget_terminal_inj key_k key) (key_of_lit key_k l)

(* Sorting by encodings (X.690 11.6) *)

let rec insert_enc (#t: Type) (enc: t -> Tot asn1_bytes) (a: t) (l: list t) : Tot (list t) (decreases l) =
  match l with
  | [] -> [a]
  | h :: q ->
    if Set_.lex_byte_order (enc a) (enc h)
    then a :: l
    else h :: insert_enc enc a q

let rec sort_enc (#t: Type) (enc: t -> Tot asn1_bytes) (l: list t) : Tot (list t) (decreases l) =
  match l with
  | [] -> []
  | a :: q -> insert_enc enc a (sort_enc enc q)

let rec sorted_enc (#t: Type) (enc: t -> Tot asn1_bytes) (l: list t) : Tot bool (decreases l) =
  match l with
  | a :: b :: q -> Set_.lex_byte_order (enc a) (enc b) && sorted_enc enc (b :: q)
  | _ -> true

let rec sort_enc_sorted (#t: Type) (enc: t -> Tot asn1_bytes) (l: list t)
: Lemma (requires (sorted_enc enc l)) (ensures (sort_enc enc l == l)) (decreases l)
= match l with
  | [] -> ()
  | [_] -> ()
  | a :: q -> sort_enc_sorted enc q

(* The suffix of a value of a sequence with an ANY DEFINED BY suffix *)

let rec items_any_sfx (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (x: asn1_sequence_any_t_core items sfx_t) : Tot sfx_t (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    snd x'
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    items_any_sfx tl (snd x')

let rec raw_items_any_sfx (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (x: raw_items_any_t items sfx_t) : Tot sfx_t (decreases items) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : raw_dec_t dk & sfx_t = x in
    snd x'
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : raw_dec_t dk & raw_items_any_t tl sfx_t = x in
    raw_items_any_sfx tl (snd x')

let fb_precedes (k: asn1_content_k)
: Lemma
  (requires (ASN1_ANY_DEFINED_BY? k /\ Some? (ASN1_ANY_DEFINED_BY?.fallback k)))
  (ensures (dsnd (Some?.v (ASN1_ANY_DEFINED_BY?.fallback k)) << k))
= match k with
  | ASN1_ANY_DEFINED_BY _ _ _ _ _ (Some fb) _ _ -> ()

(* From typed values to raw values *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec forget_content (k: asn1_content_k) (x: asn1_content_t k) : Tot (asn1_raw_content_t k) (decreases %[k; 3]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> forget_terminal k' x
  | ASN1_TERMINAL k' -> forget_terminal k' x
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    forget_items items x
  | ASN1_SET _ items _ -> forget_items items x
  | ASN1_SEQUENCE_OF _ k' -> forget_list k' x
  | ASN1_SET_OF _ k' -> forget_list k' x
  | ASN1_PREFIXED k' -> forget k' x
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let s : make_gen_choice_type (typed_any_t key_k ls) = items_any_sfx prefix x in
      forget_items_any prefix #(make_gen_choice_type (typed_any_t key_k ls)) x (forget_adb_sfx key_k ls s)
    | Some fb ->
      let (| _, fbitems |) = fb in
      fb_precedes k;
      let s : make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems) = items_any_sfx prefix x in
      forget_items_any prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) x (forget_adb_fb_sfx k key_k ls fbitems s)
    end

and forget_adb_sfx (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (s: make_gen_choice_type (typed_any_t key_k ls)) : Tot (make_gen_choice_type (raw_any_t_core key_k ls)) (decreases %[ls; 1]) =
  let (| key, y |) = s in
  (| forget_terminal key_k key, forget_ls key_k ls key y |)

and forget_adb_fb_sfx (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (s: make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) : Tot (make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) (decreases %[k0; 2]) =
  let (| key, y |) = s in
  (| forget_terminal key_k key, forget_ls_fb k0 key_k ls fbitems key y |)

and forget_list (#s: _) (k: asn1_k s) (l: list (asn1_t k)) : Tot (list (asn1_raw_t k)) (decreases %[k; 3; l]) =
  match l with
  | [] -> []
  | a :: q -> forget k a :: forget_list k q

and forget (#s: _) (k: asn1_k s) (x: asn1_t k) : Tot (asn1_raw_t k) (decreases %[k; 2]) =
  match k with
  | ASN1_ILC _ k' -> forget_content k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, y |) = x' in
    let r : make_gen_choice_type (raw_lc_t lc) = (| id, forget_choice lc id y |) in
    r
  | ASN1_ANY_ILC -> x

and forget_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (asn1_lc_t lc)) : Tot (idlookup_t id (raw_lc_t lc)) (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then forget_content c y
    else forget_choice tl id y

and forget_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y: idlookup_t key (typed_any_t key_k ls)) : Tot (idlookup_t (forget_terminal key_k key) (raw_any_t_core key_k ls)) (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then forget_items items y
    else begin
      forget_key_ne key_k key l;
      forget_ls key_k tl key y
    end

and forget_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y: idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) : Tot (idlookup_with_fallback_t (forget_terminal key_k key) (raw_any_t_core key_k ls) (raw_items_t fbitems)) (decreases %[k0; 1; ls]) =
  match ls with
  | [] -> forget_items fbitems y
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then forget_items items y
    else begin
      forget_key_ne key_k key l;
      forget_ls_fb k0 key_k tl fbitems key y
    end

and forget_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk) : Tot (raw_dec_t dk) (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> forget k x
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> None #(asn1_raw_t k) | Some y -> Some (forget k y))
  | ASN1_DEFAULT_TERMINAL _ #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x' : default_tv defv = x in
    (match x' with Default -> None #(asn1_raw_terminal_t k) | Nondefault y -> Some (forget_terminal k y))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r defv_l ->
    let defv : LPC.parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x' : default_tv #(LPC.parse_filter_refine (restriction_pred r)) defv = x in
    (match x' with Default -> None #(asn1_raw_terminal_t k) | Nondefault y -> Some (forget_terminal k y))

and forget_items (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items) : Tot (raw_items_t items) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> forget_dec dk x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    (forget_dec dk a, forget_items tl b)

(* forget the prefix, replacing the suffix with `rs` *)
and forget_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t #rsfx_t: Type) (x: asn1_sequence_any_t_core items sfx_t) (rs: rsfx_t) : Tot (raw_items_any_t items rsfx_t) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> rs
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    let (a, _) = x' in
    (forget_dec dk a, rs)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    let (a, b) = x' in
    (forget_dec dk a, forget_items_any tl b rs)
#pop-options

(* From raw values to typed values *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec check_content (k: asn1_content_k) (x: asn1_raw_content_t k) : Tot (option (asn1_content_t k)) (decreases %[k; 3]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL k' r ->
    begin match check_terminal k' x with
    | Some y -> if restriction_pred r y then Some (y <: LPC.parse_filter_refine (restriction_pred r)) else None
    | None -> None
    end
  | ASN1_TERMINAL k' -> check_terminal k' x
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    check_items items x
  | ASN1_SET _ items _ -> check_items items x
  | ASN1_SEQUENCE_OF ne k' ->
    begin match check_list k' x with
    | Some l -> if list_size_ok ne l then Some (l <: sized_list ne (asn1_t k')) else None
    | None -> None
    end
  | ASN1_SET_OF ne k' ->
    begin match check_list k' x with
    | Some l ->
      let l' = sort_enc (asn1_enc k') l in
      if list_size_ok ne l' then Some (l' <: sized_list ne (asn1_t k')) else None
    | None -> None
    end
  | ASN1_PREFIXED k' -> check k' x
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      begin match check_adb_sfx key_k ls (raw_items_any_sfx prefix #(make_gen_choice_type (raw_any_t_core key_k ls)) x) with
      | None -> None
      | Some s -> check_items_any prefix #(make_gen_choice_type (typed_any_t key_k ls)) #(make_gen_choice_type (raw_any_t_core key_k ls)) x s
      end
    | Some fb ->
      let (| _, fbitems |) = fb in
      fb_precedes k;
      begin match check_adb_fb_sfx k key_k ls fbitems (raw_items_any_sfx prefix #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) x) with
      | None -> None
      | Some s -> check_items_any prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) x s
      end
    end

and check_adb_sfx (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (rs: make_gen_choice_type (raw_any_t_core key_k ls)) : Tot (option (make_gen_choice_type (typed_any_t key_k ls))) (decreases %[ls; 1]) =
  let (| rkey, ry |) = rs in
  match check_terminal key_k rkey with
  | None -> None
  | Some key ->
    forget_check_terminal key_k rkey;
    match check_ls key_k ls key ry with
    | None -> None
    | Some y -> Some (| key, y |)

and check_adb_fb_sfx (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (rs: make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (option (make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))) (decreases %[k0; 2]) =
  let (| rkey, ry |) = rs in
  match check_terminal key_k rkey with
  | None -> None
  | Some key ->
    forget_check_terminal key_k rkey;
    match check_ls_fb k0 key_k ls fbitems key ry with
    | None -> None
    | Some y -> Some (| key, y |)

and check_list (#s: _) (k: asn1_k s) (l: list (asn1_raw_t k)) : Tot (option (list (asn1_t k))) (decreases %[k; 3; l]) =
  match l with
  | [] -> Some []
  | a :: q ->
    begin match check k a with
    | None -> None
    | Some a' ->
      match check_list k q with
      | None -> None
      | Some q' -> Some (a' :: q')
    end

and check (#s: _) (k: asn1_k s) (x: asn1_raw_t k) : Tot (option (asn1_t k)) (decreases %[k; 2]) =
  match k with
  | ASN1_ILC _ k' -> check_content k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (raw_lc_t lc) = x in
    let (| id, y |) = x' in
    begin match check_choice lc id y with
    | None -> None
    | Some y' -> let r : make_gen_choice_type (asn1_lc_t lc) = (| id, y' |) in Some r
    end
  | ASN1_ANY_ILC -> Some x

and check_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (raw_lc_t lc)) : Tot (option (idlookup_t id (asn1_lc_t lc))) (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then check_content c y
    else check_choice tl id y

and check_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y: idlookup_t (forget_terminal key_k key) (raw_any_t_core key_k ls)) : Tot (option (idlookup_t key (typed_any_t key_k ls))) (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then check_items items y
    else begin
      forget_key_ne key_k key l;
      check_ls key_k tl key y
    end

and check_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y: idlookup_with_fallback_t (forget_terminal key_k key) (raw_any_t_core key_k ls) (raw_items_t fbitems)) : Tot (option (idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))) (decreases %[k0; 1; ls]) =
  match ls with
  | [] -> check_items fbitems y
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then check_items items y
    else begin
      forget_key_ne key_k key l;
      check_ls_fb k0 key_k tl fbitems key y
    end

and check_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: raw_dec_t dk) : Tot (option (asn1_decorated_t_core dk)) (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> check k x
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_raw_t k) = x in
    begin match x' with
    | None -> Some (None #(asn1_t k))
    | Some y ->
      match check k y with
      | None -> None
      | Some y' -> Some (Some y')
    end
  | ASN1_DEFAULT_TERMINAL _ #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x' : option (asn1_raw_terminal_t k) = x in
    begin match x' with
    | None -> Some (Default #_ #defv)
    | Some y ->
      match check_terminal k y with
      | None -> None
      | Some v -> if v = defv then Some (Default #_ #defv) else Some (Nondefault #_ #defv v)
    end
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r defv_l ->
    let defv : LPC.parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x' : option (asn1_raw_terminal_t k) = x in
    begin match x' with
    | None -> Some (Default #_ #defv)
    | Some y ->
      match check_terminal k y with
      | None -> None
      | Some v ->
        if restriction_pred r v
        then
          let v : LPC.parse_filter_refine (restriction_pred r) = v in
          if v = defv then Some (Default #_ #defv) else Some (Nondefault #_ #defv v)
        else None
    end

and check_items (#ids: _) (items: asn1_gen_items_l ids) (x: raw_items_t items) : Tot (option (asn1_sequence_t_core items)) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> Some ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> check_dec dk x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : raw_dec_t dk & raw_items_t tl = x in
    let (a, b) = x' in
    begin match check_dec dk a with
    | None -> None
    | Some a' ->
      match check_items tl b with
      | None -> None
      | Some b' -> Some ((a', b') <: (asn1_decorated_t_core dk & asn1_sequence_t_core tl))
    end

(* check the prefix, replacing the suffix with `s` *)
and check_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t #rsfx_t: Type) (x: raw_items_any_t items rsfx_t) (s: sfx_t) : Tot (option (asn1_sequence_any_t_core items sfx_t)) (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> Some s
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : raw_dec_t dk & rsfx_t = x in
    let (a, _) = x' in
    begin match check_dec dk a with
    | None -> None
    | Some a' -> Some ((a', s) <: (asn1_decorated_t_core dk & sfx_t))
    end
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : raw_dec_t dk & raw_items_any_t tl rsfx_t = x in
    let (a, b) = x' in
    begin match check_dec dk a with
    | None -> None
    | Some a' ->
      match check_items_any tl #sfx_t #rsfx_t b s with
      | None -> None
      | Some b' -> Some ((a', b') <: (asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t))
    end
#pop-options

(* Canonical values: the elements of each SET OF are sorted by their
   encodings *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec canonical_content (k: asn1_content_k) (x: asn1_content_t k) : Tot bool (decreases %[k; 3]) =
  match k with
  | ASN1_RESTRICTED_TERMINAL _ _
  | ASN1_TERMINAL _ -> true
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    canonical_items items x
  | ASN1_SET _ items _ -> canonical_items items x
  | ASN1_SEQUENCE_OF _ k' -> canonical_list k' x
  | ASN1_SET_OF _ k' -> sorted_enc (asn1_enc k') x && canonical_list k' x
  | ASN1_PREFIXED k' -> canonical k' x
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let s : make_gen_choice_type (typed_any_t key_k ls) = items_any_sfx prefix x in
      canonical_items_any prefix #(make_gen_choice_type (typed_any_t key_k ls)) x &&
      canonical_adb_sfx key_k ls s
    | Some fb ->
      let (| _, fbitems |) = fb in
      fb_precedes k;
      let s : make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems) = items_any_sfx prefix x in
      canonical_items_any prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) x &&
      canonical_adb_fb_sfx k key_k ls fbitems s
    end

and canonical_adb_sfx (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (s: make_gen_choice_type (typed_any_t key_k ls)) : Tot bool (decreases %[ls; 1]) =
  let (| key, y |) = s in
  canonical_ls key_k ls key y

and canonical_adb_fb_sfx (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (s: make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) : Tot bool (decreases %[k0; 2]) =
  let (| key, y |) = s in
  canonical_ls_fb k0 key_k ls fbitems key y

and canonical_list (#s: _) (k: asn1_k s) (l: list (asn1_t k)) : Tot bool (decreases %[k; 3; l]) =
  match l with
  | [] -> true
  | a :: q -> canonical k a && canonical_list k q

and canonical (#s: _) (k: asn1_k s) (x: asn1_t k) : Tot bool (decreases %[k; 2]) =
  match k with
  | ASN1_ILC _ k' -> canonical_content k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, y |) = x' in
    canonical_choice lc id y
  | ASN1_ANY_ILC -> true

and canonical_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (asn1_lc_t lc)) : Tot bool (decreases %[lc; 0]) =
  match lc with
  | [] -> false_elim ()
  | (id', c) :: tl ->
    if id = id'
    then canonical_content c y
    else canonical_choice tl id y

and canonical_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y: idlookup_t key (typed_any_t key_k ls)) : Tot bool (decreases %[ls; 0]) =
  match ls with
  | [] -> false_elim ()
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then canonical_items items y
    else canonical_ls key_k tl key y

and canonical_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y: idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) : Tot bool (decreases %[k0; 1; ls]) =
  match ls with
  | [] -> canonical_items fbitems y
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then canonical_items items y
    else canonical_ls_fb k0 key_k tl fbitems key y

and canonical_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk) : Tot bool (decreases %[dk; 0]) =
  match dk with
  | ASN1_PLAIN_ILC k -> canonical k x
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> true | Some y -> canonical k y)
  | _ -> true

and canonical_items (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items) : Tot bool (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> canonical_dec dk x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    canonical_dec dk a && canonical_items tl b

(* the prefix only *)
and canonical_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t: Type) (x: asn1_sequence_any_t_core items sfx_t) : Tot bool (decreases %[items; 0]) =
  match items with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    let (a, _) = x' in
    canonical_dec dk a
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    let (a, b) = x' in
    canonical_dec dk a && canonical_items_any tl b
#pop-options

(* Round trip *)

#push-options "--fuel 2 --ifuel 2"
let rec raw_items_any_sfx_forget (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t #rsfx_t: Type) (x: asn1_sequence_any_t_core items sfx_t) (rs: rsfx_t)
: Lemma (ensures (raw_items_any_sfx items (forget_items_any items x rs) == rs)) (decreases items)
= match items with
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    begin match tl with
    | ASN1_GEN_ITEMS_NIL -> ()
    | _ ->
      let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
      raw_items_any_sfx_forget tl #sfx_t #rsfx_t (snd x') rs
    end
  | _ -> ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec check_forget_content (k: asn1_content_k) (x: asn1_content_t k)
: Lemma (requires (canonical_content k x)) (ensures (check_content k (forget_content k x) == Some x)) (decreases %[k; 3])
= match k with
  | ASN1_RESTRICTED_TERMINAL k' _ -> check_forget_terminal k' x
  | ASN1_TERMINAL k' -> check_forget_terminal k' x
  | ASN1_SEQUENCE gitems ->
    let (| _, items |) = gitems in
    check_forget_items items x
  | ASN1_SET _ items _ -> check_forget_items items x
  | ASN1_SEQUENCE_OF _ k' -> check_forget_list k' x
  | ASN1_SET_OF _ k' ->
    check_forget_list k' x;
    sort_enc_sorted (asn1_enc k') x
  | ASN1_PREFIXED k' -> check_forget k' x
  | ASN1_ANY_DEFINED_BY _ prefix _ key_k ls ofb _ _ ->
    begin match ofb with
    | None ->
      let s : make_gen_choice_type (typed_any_t key_k ls) = items_any_sfx prefix x in
      let rs = forget_adb_sfx key_k ls s in
      raw_items_any_sfx_forget prefix #(make_gen_choice_type (typed_any_t key_k ls)) x rs;
      check_forget_adb_sfx key_k ls s;
      check_forget_items_any prefix #(make_gen_choice_type (typed_any_t key_k ls)) #(make_gen_choice_type (raw_any_t_core key_k ls)) x rs
    | Some fb ->
      let (| _, fbitems |) = fb in
      fb_precedes k;
      let s : make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems) = items_any_sfx prefix x in
      let rs = forget_adb_fb_sfx k key_k ls fbitems s in
      raw_items_any_sfx_forget prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) x rs;
      check_forget_adb_fb_sfx k key_k ls fbitems s;
      check_forget_items_any prefix #(make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems)) #(make_gen_choice_type_with_fallback (raw_any_t_core key_k ls) (raw_items_t fbitems)) x rs
    end

and check_forget_adb_sfx (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (s: make_gen_choice_type (typed_any_t key_k ls))
: Lemma (requires (canonical_adb_sfx key_k ls s)) (ensures (check_adb_sfx key_k ls (forget_adb_sfx key_k ls s) == Some s)) (decreases %[ls; 1])
= let (| key, y |) = s in
  check_forget_terminal key_k key;
  check_forget_ls key_k ls key y

and check_forget_adb_fb_sfx (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (s: make_gen_choice_type_with_fallback (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))
: Lemma (requires (canonical_adb_fb_sfx k0 key_k ls fbitems s)) (ensures (check_adb_fb_sfx k0 key_k ls fbitems (forget_adb_fb_sfx k0 key_k ls fbitems s) == Some s)) (decreases %[k0; 2])
= let (| key, y |) = s in
  check_forget_terminal key_k key;
  check_forget_ls_fb k0 key_k ls fbitems key y

and check_forget_list (#s: _) (k: asn1_k s) (l: list (asn1_t k))
: Lemma (requires (canonical_list k l)) (ensures (check_list k (forget_list k l) == Some l)) (decreases %[k; 3; l])
= match l with
  | [] -> ()
  | a :: q -> check_forget k a; check_forget_list k q

and check_forget (#s: _) (k: asn1_k s) (x: asn1_t k)
: Lemma (requires (canonical k x)) (ensures (check k (forget k x) == Some x)) (decreases %[k; 2])
= match k with
  | ASN1_ILC _ k' -> check_forget_content k' x
  | ASN1_CHOICE_ILC lc _ ->
    let x' : make_gen_choice_type (asn1_lc_t lc) = x in
    let (| id, y |) = x' in
    check_forget_choice lc id y
  | ASN1_ANY_ILC -> ()

and check_forget_choice (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (y: idlookup_t id (asn1_lc_t lc))
: Lemma (requires (canonical_choice lc id y)) (ensures (check_choice lc id (forget_choice lc id y) == Some y)) (decreases %[lc; 0])
= match lc with
  | [] -> ()
  | (id', c) :: tl ->
    if id = id'
    then check_forget_content c y
    else check_forget_choice tl id y

and check_forget_ls (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (key: asn1_terminal_t key_k) (y: idlookup_t key (typed_any_t key_k ls))
: Lemma (requires (canonical_ls key_k ls key y)) (ensures (check_ls key_k ls key (forget_ls key_k ls key y) == Some y)) (decreases %[ls; 0])
= match ls with
  | [] -> ()
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then check_forget_items items y
    else begin
      forget_key_ne key_k key l;
      check_forget_ls key_k tl key y
    end

and check_forget_ls_fb (k0: asn1_content_k) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk) { ls << k0 }) (#fbids: _) (fbitems: asn1_gen_items_l fbids { fbitems << k0 }) (key: asn1_terminal_t key_k) (y: idlookup_with_fallback_t key (typed_any_t key_k ls) (asn1_sequence_t_core fbitems))
: Lemma (requires (canonical_ls_fb k0 key_k ls fbitems key y)) (ensures (check_ls_fb k0 key_k ls fbitems key (forget_ls_fb k0 key_k ls fbitems key y) == Some y)) (decreases %[k0; 1; ls])
= match ls with
  | [] -> check_forget_items fbitems y
  | (l, it) :: tl ->
    let (| _, items |) = it in
    if key = key_of_lit key_k l
    then check_forget_items items y
    else begin
      forget_key_ne key_k key l;
      check_forget_ls_fb k0 key_k tl fbitems key y
    end

and check_forget_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) (x: asn1_decorated_t_core dk)
: Lemma (requires (canonical_dec dk x)) (ensures (check_dec dk (forget_dec dk x) == Some x)) (decreases %[dk; 0])
= match dk with
  | ASN1_PLAIN_ILC k -> check_forget k x
  | ASN1_OPTION_ILC k ->
    let x' : option (asn1_t k) = x in
    (match x' with None -> () | Some y -> check_forget k y)
  | ASN1_DEFAULT_TERMINAL _ #k defv_l ->
    let defv = key_of_lit k defv_l in
    let x' : default_tv defv = x in
    (match x' with Default -> () | Nondefault y -> check_forget_terminal k y)
  | ASN1_DEFAULT_RESTRICTED_TERMINAL _ #k r defv_l ->
    let defv : LPC.parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
    let x' : default_tv #(LPC.parse_filter_refine (restriction_pred r)) defv = x in
    (match x' with Default -> () | Nondefault y -> check_forget_terminal k y)

and check_forget_items (#ids: _) (items: asn1_gen_items_l ids) (x: asn1_sequence_t_core items)
: Lemma (requires (canonical_items items x)) (ensures (check_items items (forget_items items x) == Some x)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL -> check_forget_dec dk x
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_t_core tl = x in
    let (a, b) = x' in
    check_forget_dec dk a;
    check_forget_items tl b

and check_forget_items_any (#ids: _) (items: asn1_gen_items_l ids) (#sfx_t #rsfx_t: Type) (x: asn1_sequence_any_t_core items sfx_t) (rs: rsfx_t)
: Lemma (requires (canonical_items_any items x)) (ensures (check_items_any items #sfx_t #rsfx_t (forget_items_any items x rs) (items_any_sfx items x) == Some x)) (decreases %[items; 0])
= match items with
  | ASN1_GEN_ITEMS_NIL -> ()
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    let x' : asn1_decorated_t_core dk & sfx_t = x in
    let (a, _) = x' in
    check_forget_dec dk a
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl ->
    let x' : asn1_decorated_t_core dk & asn1_sequence_any_t_core tl sfx_t = x in
    let (a, b) = x' in
    check_forget_dec dk a;
    check_forget_items_any tl #sfx_t #rsfx_t b rs
#pop-options

(* Raw values to encodable typed values *)

let check_ser (#s: _) (k: asn1_k s) (u: squash (Conf.wf k)) (r: asn1_raw_t k) : Tot (option (x: asn1_t k { encodable k x })) =
  match check k r with
  | None -> None
  | Some x ->
    if Conf.conforms k (ASN1.Spec.ToValue.to_value k x)
    then begin
      Inj.encodable_iff_conforms k x;
      Some x
    end
    else None

let check_ser_forget (#s: _) (k: asn1_k s) (u: squash (Conf.wf k)) (x: asn1_t k)
: Lemma (requires (encodable k x /\ canonical k x)) (ensures (check_ser k u (forget k x) == Some x))
= check_forget k x;
  encodable_conforms k x
