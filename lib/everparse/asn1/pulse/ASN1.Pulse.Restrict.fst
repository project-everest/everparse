module ASN1.Pulse.Restrict
#lang-pulse
(* Validators for restricted terminals (asn1_restriction): INTEGER value
   sets and ranges, BOOLEAN value sets, OCTET STRING sizes.

   INTEGER values are never materialized as unbounded integers: the
   content bytes are summarized as a sign, a "big" flag (the value does
   not fit in 64 bits, sign included) and, if not big, a 64-bit
   magnitude, which are then compared against the constants of the
   restriction, which must fit in 64 bits. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.INTEGER

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SCmp = LowParse.Pulse.SizeComparison
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module E = FStar.Endianness
module T = LowParse.Tot.Combinators
module C = ASN1.Pulse.Checkers
module Term = ASN1.Pulse.Terminal
module LPS = LowParse.Pulse.Base

irreducible let asn1_restrict_attr : unit = ()

(* Summary of an integer *)

let int_view_ok (neg big: bool) (mag: U64.t) (x: int) : prop =
  (neg == (x < 0)) /\
  (big == true ==> (x >= pow2 63 \/ x < 0 - pow2 63)) /\
  (big == false ==> U64.v mag == (if x < 0 then 0 - x else x))

[@@asn1_restrict_attr]
let int_fits (c: int) : Tot bool =
  -9223372036854775808 < c && c < 9223372036854775808

let int_fits_eq (c: int) : Lemma (int_fits c <==> (0 - pow2 63 < c /\ c < pow2 63))
= assert_norm (pow2 63 == 9223372036854775808)

let fits_u64 (c: nat { c < 9223372036854775808 }) : Lemma (c < pow2 64)
= assert_norm (pow2 64 == 18446744073709551616)

inline_for_extraction
[@@asn1_restrict_attr]
let int_le (neg big: bool) (mag: U64.t) (c: int { int_fits c }) : Tot bool =
  if big then neg
  else if neg then (if c >= 0 then true else (fits_u64 (0 - c); U64.gte mag (U64.uint_to_t (0 - c))))
  else (if c < 0 then false else (fits_u64 c; U64.lte mag (U64.uint_to_t c)))

inline_for_extraction
[@@asn1_restrict_attr]
let int_ge (neg big: bool) (mag: U64.t) (c: int { int_fits c }) : Tot bool =
  if big then not neg
  else if neg then (if c >= 0 then false else (fits_u64 (0 - c); U64.lte mag (U64.uint_to_t (0 - c))))
  else (if c < 0 then true else (fits_u64 c; U64.gte mag (U64.uint_to_t c)))

inline_for_extraction
[@@asn1_restrict_attr]
let int_eq (neg big: bool) (mag: U64.t) (c: int { int_fits c }) : Tot bool =
  if big then false
  else if c < 0 then (fits_u64 (0 - c); neg && U64.eq mag (U64.uint_to_t (0 - c)))
  else (fits_u64 c; not neg && U64.eq mag (U64.uint_to_t c))

let int_cmp_correct (neg big: bool) (mag: U64.t) (x: int) (c: int { int_fits c }) : Lemma
  (requires int_view_ok neg big mag x)
  (ensures
    int_le neg big mag c == (x <= c) /\
    int_ge neg big mag c == (x >= c) /\
    int_eq neg big mag c == (x = c))
= int_fits_eq c

[@@asn1_restrict_attr]
let rec all_fit (l: list int) : Tot bool =
  match l with
  | [] -> true
  | c :: tl -> int_fits c && all_fit tl

[@@asn1_restrict_attr]
let opt_fits (o: option int) : Tot bool =
  match o with
  | None -> true
  | Some c -> int_fits c

[@@asn1_restrict_attr]
let rec int_in (neg big: bool) (mag: U64.t) ([@@@FStar.Attributes.monomorphize] l: list int { all_fit l }) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | c :: tl -> int_eq neg big mag c || int_in neg big mag tl

let rec int_in_correct (neg big: bool) (mag: U64.t) (x: int) (l: list int { all_fit l }) : Lemma
  (requires int_view_ok neg big mag x)
  (ensures int_in neg big mag l == List.Tot.mem x l)
  (decreases l)
= match l with
  | [] -> ()
  | c :: tl -> int_cmp_correct neg big mag x c; int_in_correct neg big mag x tl

(* Supported INTEGER restrictions *)

[@@asn1_restrict_attr]
let int_restriction_ok (#k: asn1_terminal_k) (r: asn1_restriction k) : Tot bool =
  match r with
  | RESTRICT_INT_IN l -> all_fit l
  | RESTRICT_INT_RANGE lo hi -> opt_fits lo && opt_fits hi
  | _ -> false

let int_pred (#k: asn1_terminal_k) (r: asn1_restriction k) (x: int) : Tot bool =
  match r with
  | RESTRICT_INT_IN l -> List.Tot.mem x l
  | RESTRICT_INT_RANGE lo hi -> int_in_range lo hi x
  | _ -> false

inline_for_extraction
[@@asn1_restrict_attr]
let int_check (#[@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] r: asn1_restriction k { int_restriction_ok r }) (neg big: bool) (mag: U64.t) : Tot bool =
  match r with
  | RESTRICT_INT_IN l -> int_in neg big mag l
  | RESTRICT_INT_RANGE lo hi ->
    (match lo with None -> true | Some c -> int_ge neg big mag c) &&
    (match hi with None -> true | Some c -> int_le neg big mag c)

let int_check_correct (#k: asn1_terminal_k) (r: asn1_restriction k { int_restriction_ok r }) (neg big: bool) (mag: U64.t) (x: int) : Lemma
  (requires int_view_ok neg big mag x)
  (ensures int_check r neg big mag == int_pred r x)
= match r with
  | RESTRICT_INT_IN l -> int_in_correct neg big mag x l
  | RESTRICT_INT_RANGE lo hi ->
    (match lo with None -> () | Some c -> int_cmp_correct neg big mag x c);
    (match hi with None -> () | Some c -> int_cmp_correct neg big mag x c)

(* From the content bytes to the summary *)

let int_accept (bound: nat) (f: int -> bool) (b: bytes) : GTot bool =
  Seq.length b <= bound && valid_unsigned_repr b && f (mk_integer' b)

let acc_spec (neg: bool) (s: bytes) : GTot int =
  if neg then pow2 (8 * Seq.length s) - 1 - E.be_to_n s else E.be_to_n s

#push-options "--z3rlimit 32"

let acc_step (neg: bool) (s: bytes) (b: U8.t) : Lemma
  (ensures (
    0 <= acc_spec neg s /\ acc_spec neg s < pow2 (8 * Seq.length s) /\
    acc_spec neg (Seq.snoc s b) == acc_spec neg s * 256 + (if neg then 255 - U8.v b else U8.v b)))
= let s' = Seq.snoc s b in
  E.reveal_be_to_n s';
  assert (Seq.slice s' 0 (Seq.length s) `Seq.equal` s);
  E.lemma_be_to_n_is_bounded s;
  FStar.Math.Lemmas.pow2_plus (8 * Seq.length s) 8;
  assert_norm (pow2 8 == 256)

let acc_empty (neg: bool) (s: bytes) : Lemma
  (requires Seq.length s == 0)
  (ensures acc_spec neg s == 0)
= E.reveal_be_to_n s

let int_view_neg (b: bytes) : Lemma
  (requires valid_unsigned_repr b)
  (ensures (mk_integer' b < 0 <==> U8.v (Seq.index b 0) >= 128))
= be_to_n_msb b;
  E.lemma_be_to_n_is_bounded b

let int_view_big (b: bytes) : Lemma
  (requires valid_unsigned_repr b /\ Seq.length b > 8)
  (ensures (mk_integer' b >= pow2 63 \/ mk_integer' b < 0 - pow2 63))
= let n = Seq.length b in
  let Some x = mk_integer n b in
  assert (x == mk_integer' b);
  if 0 - pow2 63 <= x && x < pow2 63
  then begin
    assert (interval 8 x);
    let n' = interval_elim 8 x in
    domain_unique n n' x
  end

let int_view_small (b: bytes) (neg: bool) (acc: nat) : Lemma
  (requires
    valid_unsigned_repr b /\ Seq.length b <= 8 /\
    neg == (U8.v (Seq.index b 0) >= 128) /\
    acc == acc_spec neg b)
  (ensures (
    let x = mk_integer' b in
    (neg == true ==> acc + 1 < pow2 64) /\
    acc < pow2 64 /\
    (if x < 0 then 0 - x else x) == (if neg then acc + 1 else acc)))
= let n = Seq.length b in
  int_view_neg b;
  be_to_n_msb b;
  E.lemma_be_to_n_is_bounded b;
  FStar.Math.Lemmas.pow2_plus (8 * n - 1) 1;
  FStar.Math.Lemmas.pow2_le_compat 64 (8 * n);
  FStar.Math.Lemmas.pow2_le_compat 63 (8 * n - 1)

#pop-options

let int_view_big_ok (b: bytes) (neg: bool) : Lemma
  (requires valid_unsigned_repr b /\ Seq.length b > 8 /\ neg == (U8.v (Seq.index b 0) >= 128))
  (ensures int_view_ok neg true 0UL (mk_integer' b))
= int_view_neg b;
  int_view_big b

let int_view_small_ok (b: bytes) (neg: bool) (acc: U64.t) : Lemma
  (requires
    valid_unsigned_repr b /\ Seq.length b <= 8 /\
    neg == (U8.v (Seq.index b 0) >= 128) /\
    U64.v acc == acc_spec neg b)
  (ensures (
    (neg == true ==> U64.v acc + 1 < pow2 64) /\
    int_view_ok neg false (if neg then U64.uint_to_t (U64.v acc + 1) else acc) (mk_integer' b)))
= int_view_neg b;
  int_view_small b neg (U64.v acc)

let snoc_slice (v: bytes) (i: nat { i < Seq.length v }) : Lemma
  (Seq.slice v 0 (i + 1) == Seq.snoc (Seq.slice v 0 i) (Seq.index v i))
= assert (Seq.slice v 0 (i + 1) `Seq.equal` Seq.snoc (Seq.slice v 0 i) (Seq.index v i))

#push-options "--z3rlimit 64"

inline_for_extraction
fn check_integer_restricted
  (bound: U64.t { U64.v bound < 18446744073709551615 })
  (f: Ghost.erased (int -> bool))
  (chk: (bool -> bool -> U64.t -> bool))
  (chk_ok: squash (forall neg big mag x . int_view_ok neg big mag x ==> chk neg big mag == Ghost.reveal f x))
: C.slice_checker (int_accept (U64.v bound) f)
=
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  pts_to_len s;
  let n = S.len s;
  let big = SCmp.u64_lte_sizet (U64.add bound 1UL) n;
  if (big || n = 0sz) {
    false
  } else {
    let c0 = s.(0sz);
    let i1 = (if n = 1sz then 0sz else 1sz);
    let c1 = s.(i1);
    let minimal = (n = 1sz || not ((c0 = 0uy && U8.lt c1 128uy) || (c0 = 255uy && U8.lt 127uy c1)));
    assert (pure (minimal == valid_unsigned_repr v));
    if (not minimal) {
      false
    } else {
      let neg = U8.gte c0 128uy;
      if (SZ.gt n 8sz) {
        int_view_big_ok v neg;
        chk neg true 0UL
      } else {
        let mut pacc = 0UL;
        let mut pi = 0sz;
        acc_empty neg (Seq.slice v 0 0);
        while (
          let i = !pi;
          SZ.lt i n
        ) invariant exists* i acc .
          R.pts_to pi i **
          R.pts_to pacc acc **
          S.pts_to s #pm v **
          pure (
            SZ.v i <= SZ.v n /\
            U64.v acc == acc_spec neg (Seq.slice v 0 (SZ.v i))
          )
          decreases (SZ.v n - SZ.v (!pi))
        {
          let i = !pi;
          let b = s.(i);
          let acc = !pacc;
          acc_step neg (Seq.slice v 0 (SZ.v i)) b;
          snoc_slice v (SZ.v i);
          FStar.Math.Lemmas.pow2_le_compat 64 (8 * (SZ.v i + 1));
          FStar.Math.Lemmas.pow2_plus (8 * SZ.v i) 8;
          let d = (if neg then U8.sub 255uy b else b);
          pacc := U64.add (U64.mul acc 256UL) (FStar.Int.Cast.uint8_to_uint64 d);
          pi := SZ.add i 1sz
        };
        let acc = !pacc;
        assert (pure (Seq.slice v 0 (SZ.v n) `Seq.equal` v));
        int_view_small_ok v neg acc;
        let mag = (if neg then U64.add acc 1UL else acc);
        chk neg false mag
      }
    }
  }
}

#pop-options

(* Restricted content parsers only depend on the restriction predicate
   pointwise *)

let restricted_consumed_ext
  (k: asn1_terminal_k) (r: asn1_restriction k) (g: asn1_terminal_t k -> bool)
  (sq: squash (forall x . g x == restriction_pred r x))
: Lemma (ASN1.Pulse.Sequence.consumed_ext_prop
    #(LowParse.Spec.Combinators.parse_filter_kind asn1_weak_parser_kind)
    (T.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) g)
    #asn1_weak_parser_kind
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)))
= Classical.forall_intro (T.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) g);
  Classical.forall_intro (T.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred r))

(* BOOLEAN DEFAULT defv: the encoding must not be the default value
   (X.690 11.5) *)
inline_for_extraction
let validate_boolean_neq (defv: asn1_terminal_t ASN1_BOOLEAN)
: LPS.validator
    #(asn1_content_t (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (RESTRICT_CUSTOM (ASN1.Spec.Sequence.defaultv_filter defv))))
    #asn1_weak_parser_kind
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (RESTRICT_CUSTOM (ASN1.Spec.Sequence.defaultv_filter defv))))
= restricted_consumed_ext ASN1_BOOLEAN (RESTRICT_CUSTOM (ASN1.Spec.Sequence.defaultv_filter defv)) (ASN1.Spec.Sequence.defaultv_filter defv) ();
  ASN1.Pulse.Sequence.validate_ext_consumed
    (Term.validate_boolean_filter (ASN1.Spec.Sequence.defaultv_filter defv))
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (RESTRICT_CUSTOM (ASN1.Spec.Sequence.defaultv_filter defv))))

(* BOOLEAN value sets *)

[@@asn1_restrict_attr]
let rec bool_in ([@@@FStar.Attributes.monomorphize] l: list bool) (x: bool) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | c :: tl -> (x = c) || bool_in tl x

let rec bool_in_correct (l: list bool) (x: bool) : Lemma (bool_in l x == List.Tot.mem x l)
= match l with
  | [] -> ()
  | _ :: tl -> bool_in_correct tl x

inline_for_extraction
[@@asn1_restrict_attr]
let validate_boolean_in (l: list bool)
: LPS.validator
    #(asn1_content_t (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (RESTRICT_IN l)))
    #asn1_weak_parser_kind
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (RESTRICT_IN l)))
= Classical.forall_intro (bool_in_correct l);
  restricted_consumed_ext ASN1_BOOLEAN (RESTRICT_IN l) (bool_in l) ();
  ASN1.Pulse.Sequence.validate_ext_consumed
    (Term.validate_boolean_filter (bool_in l))
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (RESTRICT_IN l)))

(* INTEGER value sets and ranges *)

#push-options "--z3rlimit 32"

let int_restricted_pred (bound: pos) (r: asn1_restriction (ASN1_INTEGER bound) { int_restriction_ok r })
: Lemma (Term.all_bytes_pred (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL (ASN1_INTEGER bound) r)) (int_accept bound (int_pred r)))
= let p = asn1_terminal_as_parser (ASN1_INTEGER bound) in
  assert (forall (x: asn1_terminal_t (ASN1_INTEGER bound)) . restriction_pred r x == int_pred r x);
  Classical.forall_intro (T.parse_filter_eq #asn1_weak_parser_kind p (restriction_pred r))

#pop-options

let int_chk_ok (bound: pos) (r: asn1_restriction (ASN1_INTEGER bound) { int_restriction_ok r })
: Lemma (forall neg big mag x . int_view_ok neg big mag x ==> int_check r neg big mag == int_pred r x)
= Classical.forall_intro_4 (fun neg big mag x -> Classical.move_requires (int_check_correct r neg big mag) x)

inline_for_extraction
[@@asn1_restrict_attr]
let validate_integer_restricted (bound: U64.t { U64.v bound > 0 /\ U64.v bound < 18446744073709551615 }) (r: asn1_restriction (ASN1_INTEGER (U64.v bound)) { int_restriction_ok r })
: LPS.validator
    #(asn1_content_t (ASN1_RESTRICTED_TERMINAL (ASN1_INTEGER (U64.v bound)) r))
    #asn1_weak_parser_kind
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL (ASN1_INTEGER (U64.v bound)) r))
= int_chk_ok (U64.v bound) r;
  Term.validate_all_bytes_pred
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL (ASN1_INTEGER (U64.v bound)) r))
    (int_accept (U64.v bound) (int_pred r))
    (check_integer_restricted bound (int_pred r) (int_check r) ())
    (int_restricted_pred (U64.v bound) r)

(* SIZE on OCTET STRING and character strings *)

[@@asn1_restrict_attr]
let size_restriction_ok (#k: asn1_terminal_k) (r: asn1_restriction k) : Tot bool =
  match r with
  | RESTRICT_SIZE lo hi -> lo < 65536 && (match hi with None -> true | Some h -> h < 65536)
  | _ -> false

(* `f` computes, from the content bytes, the size of the value they parse
   to; the base parser consumes all its input *)
let count_pred (k: asn1_terminal_k) (f: bytes -> GTot nat) : prop =
  forall (b: bytes) . match parse (asn1_terminal_as_parser k) b with
  | None -> True
  | Some (x, n) -> n == Seq.length b /\ asn1_char_count #k x == Some (f b)

inline_for_extraction
fn check_count
  (#f: Ghost.erased (bytes -> GTot nat))
  (cnt: C.slice_counter f)
  (lo: SZ.t) (has_hi: bool) (hi: SZ.t)
  (hi': Ghost.erased (option nat) { Ghost.reveal hi' == (if has_hi then Some (SZ.v hi) else None) })
: C.slice_checker (fun b -> size_in_range (SZ.v lo) hi' (Ghost.reveal f b))
=
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let n = cnt s;
  (SZ.lte lo n && (not has_hi || SZ.lte n hi))
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_size_gen
  (k: Ghost.erased asn1_terminal_k)
  (r: Ghost.erased (asn1_restriction k) { RESTRICT_SIZE? r })
  (w: LPS.validator #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k))
  (f: Ghost.erased (bytes -> GTot nat))
  (c: C.slice_checker (fun b -> size_in_range (RESTRICT_SIZE?.lo r) (RESTRICT_SIZE?.hi r) (Ghost.reveal f b)))
  (sq: squash (count_pred k f))
: LPS.validator #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  pts_to_len input;
  reveal_opaque (`%size_pred) (size_pred #(Ghost.reveal k) (RESTRICT_SIZE?.lo r) (RESTRICT_SIZE?.hi r));
  T.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser k) (restriction_pred #(Ghost.reveal k) r) (Seq.slice v (SZ.v offset) (Seq.length v));
  let off = !poffset;
  let ok = w input poffset;
  if (ok) {
    let s1, s2 = S.split input off;
    let res = c s2;
    S.join s1 s2 input;
    Seq.lemma_split v (SZ.v off);
    res
  } else {
    false
  }
}

#pop-options

let rec char_list_count (f: U8.t -> bool) (b: bytes)
: Lemma (ensures (match parse (LowParse.Tot.List.parse_list (T.parse_filter LowParse.Tot.Int.parse_u8 f)) b with
    | None -> True
    | Some (x, n) -> n == Seq.length b /\ List.length x == Seq.length b))
  (decreases (Seq.length b))
= let p = T.parse_filter LowParse.Tot.Int.parse_u8 f in
  LowParse.Spec.List.tot_parse_list_eq p b;
  if Seq.length b = 0 then ()
  else begin
    LowParse.Spec.Base.parser_kind_prop_equiv (LowParse.Spec.Combinators.parse_filter_kind LowParse.Spec.Int.parse_u8_kind) p;
    match parse p b with
    | None -> ()
    | Some (_, n) -> char_list_count f (Seq.slice b n (Seq.length b))
  end

let count_bytes (b: bytes) : GTot nat = Seq.length b
let count_bmp (b: bytes) : GTot nat = Seq.length b / 2
let count_universal (b: bytes) : GTot nat = Seq.length b / 4
let count_utf8 (b: bytes) : GTot nat = utf8_count b

inline_for_extraction
fn len_div (d: SZ.t { SZ.v d > 0 }) (#f: Ghost.erased (bytes -> GTot nat) { forall b . Ghost.reveal f b == Seq.length b / SZ.v d })
: C.slice_counter f
=
  (s: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  pts_to_len s;
  SZ.div (S.len s) d
}

[@@asn1_restrict_attr]
let raw_string_k (k: asn1_terminal_k) : Tot bool =
  match k with
  | ASN1_OCTETSTRING | ASN1_TELETEXSTRING | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING | ASN1_GENERALSTRING | ASN1_OBJECTDESCRIPTOR -> true
  | _ -> false

let raw_count_pred (k: asn1_terminal_k { raw_string_k k }) : Lemma (count_pred k count_bytes)
= reveal_opaque (`%asn1_char_count) (asn1_char_count #k)

let bmp_count_pred () : Lemma (count_pred ASN1_BMPSTRING count_bmp)
= reveal_opaque (`%asn1_char_count) (asn1_char_count #ASN1_BMPSTRING);
  Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes is_valid_bmp)

let universal_count_pred () : Lemma (count_pred ASN1_UNIVERSALSTRING count_universal)
= reveal_opaque (`%asn1_char_count) (asn1_char_count #ASN1_UNIVERSALSTRING);
  Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes is_valid_universal)

let utf8_count_pred () : Lemma (count_pred ASN1_UTF8STRING count_utf8)
= reveal_opaque (`%asn1_char_count) (asn1_char_count #ASN1_UTF8STRING);
  Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes LowParse.Spec.UTF8.correct)

[@@asn1_restrict_attr]
let char_list_k (k: asn1_terminal_k) : Tot bool =
  match k with
  | ASN1_PRINTABLESTRING | ASN1_IA5STRING | ASN1_VISIBLESTRING | ASN1_NUMERICSTRING -> true
  | _ -> false

let char_list_count_pred (k: asn1_terminal_k { char_list_k k }) : Lemma (count_pred k count_bytes)
= reveal_opaque (`%asn1_char_count) (asn1_char_count #k);
  match k with
  | ASN1_PRINTABLESTRING -> Classical.forall_intro (char_list_count is_printable_char)
  | ASN1_IA5STRING -> Classical.forall_intro (char_list_count is_ia5_char)
  | ASN1_VISIBLESTRING -> Classical.forall_intro (char_list_count is_visible_char)
  | ASN1_NUMERICSTRING -> Classical.forall_intro (char_list_count is_numeric_char)

[@@asn1_restrict_attr]
let size_string_k (k: asn1_terminal_k) : Tot bool =
  raw_string_k k || char_list_k k ||
  (match k with
   | ASN1_UTF8STRING | ASN1_BMPSTRING | ASN1_UNIVERSALSTRING -> true
   | _ -> false)

inline_for_extraction
[@@asn1_restrict_attr]
let validate_string_size
  (k: asn1_terminal_k { size_string_k k })
  (r: asn1_restriction k { size_restriction_ok r })
  (w: LPS.validator #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k))
: LPS.validator
    #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
    #asn1_weak_parser_kind
    (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))
= [@inline_let] let lo = RESTRICT_SIZE?.lo r in
  [@inline_let] let hi = RESTRICT_SIZE?.hi r in
  SZ.fits_at_least_16 lo;
  [@inline_let] let lo_sz = SZ.uint_to_t lo in
  [@inline_let] let hi_sz : SZ.t = (if Some? hi then (SZ.fits_at_least_16 (Some?.v hi); SZ.uint_to_t (Some?.v hi)) else 0sz) in
  match k with
  | ASN1_UTF8STRING ->
    validate_size_gen k r w count_utf8
      (check_count #(Ghost.hide count_utf8) C.count_utf8 lo_sz (Some? hi) hi_sz (Ghost.hide hi)) (utf8_count_pred ())
  | ASN1_BMPSTRING ->
    validate_size_gen k r w count_bmp
      (check_count (len_div 2sz #count_bmp) lo_sz (Some? hi) hi_sz (Ghost.hide hi)) (bmp_count_pred ())
  | ASN1_UNIVERSALSTRING ->
    validate_size_gen k r w count_universal
      (check_count (len_div 4sz #count_universal) lo_sz (Some? hi) hi_sz (Ghost.hide hi)) (universal_count_pred ())
  | ASN1_PRINTABLESTRING | ASN1_IA5STRING | ASN1_VISIBLESTRING | ASN1_NUMERICSTRING ->
    validate_size_gen k r w count_bytes
      (check_count (len_div 1sz #count_bytes) lo_sz (Some? hi) hi_sz (Ghost.hide hi)) (char_list_count_pred k)
  | _ ->
    validate_size_gen k r w count_bytes
      (check_count (len_div 1sz #count_bytes) lo_sz (Some? hi) hi_sz (Ghost.hide hi)) (raw_count_pred k)

(* BOOLEAN (restricted to a value set) DEFAULT defv *)

inline_for_extraction
[@@asn1_restrict_attr]
let bool_in_neq ([@@@FStar.Attributes.monomorphize] l: list bool) (defv: bool) (x: bool) : Tot bool =
  bool_in l x && not (x = defv)

inline_for_extraction
[@@asn1_restrict_attr]
let validate_boolean_in_neq (l: list bool) (defv: asn1_terminal_t ASN1_BOOLEAN { restriction_pred (RESTRICT_IN #ASN1_BOOLEAN l) defv })
: LPS.validator
    #(asn1_content_t (ASN1.Pulse.Constructed.default_restricted_content ASN1_BOOLEAN (RESTRICT_IN l) defv))
    #asn1_weak_parser_kind
    (asn1_content_as_parser (ASN1.Pulse.Constructed.default_restricted_content ASN1_BOOLEAN (RESTRICT_IN l) defv))
= Classical.forall_intro (bool_in_correct l);
  restricted_consumed_ext ASN1_BOOLEAN (RESTRICT_CUSTOM (ASN1.Pulse.Constructed.restricted_default_filter (RESTRICT_IN #ASN1_BOOLEAN l) defv)) (bool_in_neq l defv) ();
  ASN1.Pulse.Sequence.validate_ext_consumed
    (Term.validate_boolean_filter (bool_in_neq l defv))
    (asn1_content_as_parser (ASN1.Pulse.Constructed.default_restricted_content ASN1_BOOLEAN (RESTRICT_IN l) defv))
