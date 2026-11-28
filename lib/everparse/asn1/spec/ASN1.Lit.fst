module ASN1.Lit

(* Decision procedures on lists for the refinements of the literals of
   `ASN1.Base.asn1_key_lit` (DEFAULT values and ANY DEFINED BY keys), so
   that generated literals are proved by normalization (`assert_norm`)
   instead of SMT unfolding of the recursive predicates on sequences. *)

open ASN1.Base
module U8 = FStar.UInt8
module Seq = FStar.Seq
module L = FStar.List.Tot
module UTF8 = LowParse.Spec.UTF8

let rec drop (#a: Type) (n: nat) (l: list a)
: Tot (l': list a { L.length l' == (if n <= L.length l then L.length l - n else 0) })
= if n = 0 then l else match l with [] -> [] | _ :: t -> drop (n - 1) t

let rec index_drop (#a: Type) (n: nat) (l: list a) (j: nat)
: Lemma (requires n + j < L.length l)
  (ensures L.index (drop n l) j == L.index l (n + j))
= if n = 0 then () else match l with _ :: t -> index_drop (n - 1) t j

let rec drop_index (#a: Type) (n: nat) (l: list a)
: Lemma (requires n < L.length l)
  (ensures drop n l == L.index l n :: drop (n + 1) l)
= if n = 0 then () else match l with _ :: t -> drop_index (n - 1) t

let slice_seq_of_list (#a: Type) (l: list a) (n: nat { n <= L.length l })
: Lemma (Seq.slice (Seq.seq_of_list l) n (L.length l) == Seq.seq_of_list (drop n l))
= let s = Seq.slice (Seq.seq_of_list l) n (L.length l) in
  let s' = Seq.seq_of_list (drop n l) in
  let aux (j: nat { j < Seq.length s }) : Lemma (Seq.index s j == Seq.index s' j) =
    index_drop n l j
  in
  FStar.Classical.forall_intro aux;
  assert (Seq.equal s s')

(* UTF8String: `UTF8.fetch'` and `UTF8.check` on lists *)

let fetch_l (l: list U8.t { Cons? l }) : Tot (option pos) =
  let byte1 = U8.v (L.index l 0) in
  if byte1 <= 0x7F
  then Some 1
  else if L.length l = 1
  then None
  else
    let byte2 = U8.v (L.index l 1) in
    if 0xC2 <= byte1 && byte1 <= 0xDF && UTF8.byte_in_80_BF byte2
    then Some 2
    else if L.length l = 2
    then None
    else if not (UTF8.byte_in_80_BF (U8.v (L.index l 2)))
    then None
    else if byte1 = 0xE0
    then
      if 0xA0 <= byte2 && byte2 <= 0xBF
      then Some 3
      else None
    else if byte1 = 0xED
    then
      if 0x80 <= byte2 && byte2 <= 0x9F
      then Some 3
      else None
    else if (0xE1 <= byte1 && byte1 <= 0xEF) && UTF8.byte_in_80_BF byte2
    then Some 3
    else if L.length l = 3
    then None
    else if not (UTF8.byte_in_80_BF (U8.v (L.index l 3)))
    then None
    else if byte1 = 0xF0 && 0x90 <= byte2 && byte2 <= 0xBF
    then Some 4
    else if 0xF1 <= byte1 && byte1 <= 0xF3 && UTF8.byte_in_80_BF byte2
    then Some 4
    else if byte1 = 0xF4
    then
      if 0x80 <= byte2 && byte2 <= 0x8F
      then Some 4
      else None
    else None

let fetch_l_correct (l: list U8.t { Cons? l })
: Lemma (fetch_l l == UTF8.fetch' (Seq.seq_of_list l))
= ()

let rec utf8_l (l: list U8.t) : Tot bool (decreases (L.length l)) =
  match l with
  | [] -> true
  | _ ->
    match fetch_l l with
    | None -> false
    | Some n -> n <= L.length l && utf8_l (drop n l)

let rec utf8_l_correct (l: list U8.t)
: Lemma (requires utf8_l l) (ensures UTF8.correct (Seq.seq_of_list l))
  (decreases (L.length l))
= match l with
  | [] -> ()
  | _ ->
    fetch_l_correct l;
    let Some n = fetch_l l in
    slice_seq_of_list l n;
    utf8_l_correct (drop n l)

(* BMPString and UniversalString *)

let rec bmp_l (l: list U8.t) : Tot bool =
  match l with
  | [] -> true
  | hi :: _ :: t -> not (0xD8 <= U8.v hi && U8.v hi <= 0xDF) && bmp_l t
  | _ -> false

let rec bmp_l_correct (l: list U8.t) (i: nat { i <= L.length l })
: Lemma (ensures is_valid_bmp_from (Seq.seq_of_list l) i == bmp_l (drop i l))
  (decreases (L.length l - i))
= if i = L.length l then ()
  else if i + 2 > L.length l then ()
  else begin
    drop_index i l;
    drop_index (i + 1) l;
    bmp_l_correct l (i + 2)
  end

let rec universal_l (l: list U8.t) : Tot bool =
  match l with
  | [] -> true
  | b0 :: b1 :: b2 :: _ :: t ->
    U8.v b0 = 0 && U8.v b1 <= 0x10 && not (U8.v b1 = 0 && 0xD8 <= U8.v b2 && U8.v b2 <= 0xDF) &&
    universal_l t
  | _ -> false

let rec universal_l_correct (l: list U8.t) (i: nat { i <= L.length l })
: Lemma (ensures is_valid_universal_from (Seq.seq_of_list l) i == universal_l (drop i l))
  (decreases (L.length l - i))
= if i = L.length l then ()
  else if i + 4 > L.length l then begin
    drop_index i l;
    if i + 1 < L.length l then drop_index (i + 1) l;
    if i + 2 < L.length l then drop_index (i + 2) l
  end else begin
    drop_index i l;
    drop_index (i + 1) l;
    drop_index (i + 2) l;
    drop_index (i + 3) l;
    universal_l_correct l (i + 4)
  end

(* BIT STRING *)

let bitstring_l (unused: U8.t) (l: list U8.t) : Tot bool =
  U8.v unused <= 7 &&
  (U8.v unused = 0 ||
   (Cons? l && U8.v (L.index l (L.length l - 1)) % pow2 (U8.v unused) = 0))

let bitstring_l_correct (unused: U8.t) (l: list U8.t)
: Lemma (requires bitstring_l unused l)
  (ensures asn1_bitstring_lit_wf unused (Seq.seq_of_list l))
= ()

(* The literals, for generated code: `utf8_lit l ()` etc. *)

let utf8_lit (l: list U8.t) (_: squash (utf8_l l)) : asn1_key_lit ASN1_UTF8STRING =
  utf8_l_correct l; l

let bmp_lit (l: list U8.t) (_: squash (bmp_l l)) : asn1_key_lit ASN1_BMPSTRING =
  bmp_l_correct l 0; l

let universal_lit (l: list U8.t) (_: squash (universal_l l)) : asn1_key_lit ASN1_UNIVERSALSTRING =
  universal_l_correct l 0; l

let bitstring_lit (unused: U8.t) (l: list U8.t) (_: squash (bitstring_l unused l)) : asn1_key_lit ASN1_BITSTRING =
  bitstring_l_correct unused l; (unused, l)

(* Restrictions of literals (DEFAULT values of restricted types): those
   of `ASN1.Base.restriction_pred_lit`, and the SIZE of the strings that
   are byte sequences *)

let rec utf8_count_l (l: list U8.t) : Tot nat =
  match l with
  | [] -> 0
  | c :: t -> (if is_utf8_lead c then 1 else 0) + utf8_count_l t

let rec utf8_count_l_correct (l: list U8.t) (i: nat { i <= L.length l })
: Lemma (ensures utf8_count_from (Seq.seq_of_list l) i == utf8_count_l (drop i l))
  (decreases (L.length l - i))
= if i = L.length l then ()
  else begin
    drop_index i l;
    utf8_count_l_correct l (i + 1)
  end

let restriction_lit (#k: asn1_terminal_k) (r: asn1_restriction k) (x: asn1_key_lit k) : Tot bool =
  match k with
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR ->
    let x : list U8.t = x in
    (match r with RESTRICT_SIZE lo hi -> size_in_range lo hi (L.length x) | _ -> false)
  | ASN1_UTF8STRING ->
    let x : list U8.t = x in
    (match r with RESTRICT_SIZE lo hi -> size_in_range lo hi (utf8_count_l x) | _ -> false)
  | ASN1_BMPSTRING ->
    let x : list U8.t = x in
    (match r with RESTRICT_SIZE lo hi -> size_in_range lo hi (L.length x / 2) | _ -> false)
  | ASN1_UNIVERSALSTRING ->
    let x : list U8.t = x in
    (match r with RESTRICT_SIZE lo hi -> size_in_range lo hi (L.length x / 4) | _ -> false)
  | _ -> restriction_pred_lit r x

#push-options "--fuel 2 --ifuel 2"
let restriction_lit_correct (#k: asn1_terminal_k) (r: asn1_restriction k) (x: asn1_key_lit k)
: Lemma (requires (restriction_lit r x)) (ensures (restriction_pred r (key_of_lit k x)))
= reveal_opaque (`%asn1_char_count) (asn1_char_count #k);
  (match r with RESTRICT_SIZE lo hi -> reveal_opaque (`%size_pred) (size_pred #k lo hi) | _ -> ());
  match k with
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING -> ()
  | ASN1_UTF8STRING -> utf8_count_l_correct x 0
  | _ -> restriction_pred_lit_correct r x
#pop-options

(* Times (ASN1.Spec.Time) *)

module T = ASN1.Spec.Time
module I = ASN1.Spec.IRI
module U32 = FStar.UInt32

let rec digits_l (l: list U8.t) (s: nat) (n: nat { s + n <= L.length l }) : Tot bool (decreases n) =
  if n = 0 then true
  else T.is_valid_digit (L.index l (s + n - 1)) && digits_l l s (n - 1)

let rec digits_l_correct (l: list U8.t) (s: nat) (n: nat { s + n <= L.length l })
: Lemma (ensures digits_l l s n == T.is_valid_digit_range (Seq.seq_of_list l) s n) (decreases n)
= if n = 0 then () else digits_l_correct l s (n - 1)

let rec digits_l_index (l: list U8.t) (s: nat) (n: nat { s + n <= L.length l }) (i: nat { i < n })
: Lemma (requires digits_l l s n) (ensures T.is_valid_digit (L.index l (s + i))) (decreases n)
= if i = n - 1 then () else digits_l_index l s (n - 1) i

let digits_l_6 (l: list U8.t) (s: nat { s + 6 <= L.length l })
: Lemma (requires digits_l l s 6)
  (ensures T.is_valid_digit (L.index l s) /\ T.is_valid_digit (L.index l (s + 1)) /\
    T.is_valid_digit (L.index l (s + 2)) /\ T.is_valid_digit (L.index l (s + 3)) /\
    T.is_valid_digit (L.index l (s + 4)) /\ T.is_valid_digit (L.index l (s + 5)))
= digits_l_index l s 6 0; digits_l_index l s 6 1; digits_l_index l s 6 2;
  digits_l_index l s 6 3; digits_l_index l s 6 4; digits_l_index l s 6 5

let digits_l_8 (l: list U8.t) (s: nat { s + 8 <= L.length l })
: Lemma (requires digits_l l s 8)
  (ensures T.is_valid_digit (L.index l s) /\ T.is_valid_digit (L.index l (s + 1)) /\
    T.is_valid_digit (L.index l (s + 2)) /\ T.is_valid_digit (L.index l (s + 3)) /\
    T.is_valid_digit (L.index l (s + 4)) /\ T.is_valid_digit (L.index l (s + 5)) /\
    T.is_valid_digit (L.index l (s + 6)) /\ T.is_valid_digit (L.index l (s + 7)))
= digits_l_6 l s; digits_l_index l s 8 6; digits_l_index l s 8 7

let digits_l_4 (l: list U8.t) (s: nat { s + 4 <= L.length l })
: Lemma (requires digits_l l s 4)
  (ensures T.is_valid_digit (L.index l s) /\ T.is_valid_digit (L.index l (s + 1)) /\
    T.is_valid_digit (L.index l (s + 2)) /\ T.is_valid_digit (L.index l (s + 3)))
= digits_l_index l s 4 0; digits_l_index l s 4 1; digits_l_index l s 4 2; digits_l_index l s 4 3

#push-options "--fuel 0 --ifuel 0"

let yymmdd_l (l: list U8.t) (s: nat { s + 6 <= L.length l }) : Tot bool =
  if digits_l l s 6 then begin
    digits_l_6 l s;
    let yy = T.read_2dnum (L.index l s) (L.index l (s + 1)) in
    let mm = T.read_2dnum (L.index l (s + 2)) (L.index l (s + 3)) in
    let dd = T.read_2dnum (L.index l (s + 4)) (L.index l (s + 5)) in
    T.is_valid_calendar_date2dy yy mm dd
  end else false

let yyyymmdd_l (l: list U8.t) (s: nat { s + 8 <= L.length l }) : Tot bool =
  if digits_l l s 8 then begin
    digits_l_8 l s;
    let yyyy = T.read_4dnum (L.index l s) (L.index l (s + 1)) (L.index l (s + 2)) (L.index l (s + 3)) in
    let mm = T.read_2dnum (L.index l (s + 4)) (L.index l (s + 5)) in
    let dd = T.read_2dnum (L.index l (s + 6)) (L.index l (s + 7)) in
    T.is_valid_calendar_date4dy yyyy mm dd
  end else false

let hhmmss_l (utc: bool) (l: list U8.t) (s: nat { s + 6 <= L.length l }) : Tot bool =
  if digits_l l s 6 then begin
    digits_l_6 l s;
    let hh = T.read_2dnum (L.index l s) (L.index l (s + 1)) in
    let mm = T.read_2dnum (L.index l (s + 2)) (L.index l (s + 3)) in
    let ss = T.read_2dnum (L.index l (s + 4)) (L.index l (s + 5)) in
    T.is_valid_time_hhmmss utc hh mm ss
  end else false

let basic_year_l (l: list U8.t) (s: nat { s + 4 <= L.length l }) : Tot bool =
  digits_l l s 4 &&
  (digits_l_4 l s;
   U32.lte 1582ul (T.read_4dnum (L.index l s) (L.index l (s + 1)) (L.index l (s + 2)) (L.index l (s + 3))))

#pop-options

#push-options "--fuel 8"

let yymmdd_l_correct (l: list U8.t) (s: nat { s + 6 <= L.length l /\ s <= 8 })
: Lemma (yymmdd_l l s == T.is_valid_yymmdd (Seq.seq_of_list l) (U32.uint_to_t s))
= digits_l_correct l s 6; assert (U32.v (U32.uint_to_t s) == s)

let yyyymmdd_l_correct (l: list U8.t) (s: nat { s + 8 <= L.length l /\ s <= 8 })
: Lemma (yyyymmdd_l l s == T.is_valid_yyyymmdd (Seq.seq_of_list l) (U32.uint_to_t s))
= digits_l_correct l s 8; assert (U32.v (U32.uint_to_t s) == s)

let hhmmss_l_correct (utc: bool) (l: list U8.t) (s: nat { s + 6 <= L.length l /\ s <= 8 })
: Lemma (hhmmss_l utc l s == T.is_valid_hhmmss utc (Seq.seq_of_list l) (U32.uint_to_t s))
= digits_l_correct l s 6; assert (U32.v (U32.uint_to_t s) == s)

let basic_year_l_correct (l: list U8.t) (s: nat { s + 4 <= L.length l /\ s <= 8 })
: Lemma (basic_year_l l s == T.is_valid_basic_year (Seq.seq_of_list l) (U32.uint_to_t s))
= digits_l_correct l s 4; assert (U32.v (U32.uint_to_t s) == s)

#pop-options

let utctime_l (l: list U8.t) : Tot bool =
  L.length l = 13 && yymmdd_l l 0 && hhmmss_l true l 6 && L.index l 12 = 90uy

let gentime_l (l: list U8.t) : Tot bool =
  let len = L.length l in
  if len = 15 then
    yyyymmdd_l l 0 && hhmmss_l true l 8 && L.index l 14 = 90uy
  else if len >= 17 then
    yyyymmdd_l l 0 && hhmmss_l true l 8 &&
    L.index l 14 = 46uy &&
    digits_l l 15 (len - 16) &&
    L.index l (len - 2) <> 48uy &&
    L.index l (len - 1) = 90uy
  else false

let date_l (l: list U8.t) : Tot bool =
  L.length l = 8 && yyyymmdd_l l 0 && basic_year_l l 0

let tod_l (l: list U8.t) : Tot bool =
  L.length l = 6 && hhmmss_l false l 0

let datetime_l (l: list U8.t) : Tot bool =
  L.length l = 14 && yyyymmdd_l l 0 && basic_year_l l 0 && hhmmss_l false l 8

let utctime_l_correct (l: list U8.t)
: Lemma (requires utctime_l l) (ensures T.is_valid_ASN1UTCTIME (Seq.seq_of_list l))
= yymmdd_l_correct l 0; hhmmss_l_correct true l 6

let gentime_l_correct (l: list U8.t)
: Lemma (requires gentime_l l) (ensures T.is_valid_ASN1GENERALIZEDTIME (Seq.seq_of_list l))
= yyyymmdd_l_correct l 0; hhmmss_l_correct true l 8;
  if L.length l >= 17 then digits_l_correct l 15 (L.length l - 16)

let date_l_correct (l: list U8.t)
: Lemma (requires date_l l) (ensures T.is_valid_ASN1DATE (Seq.seq_of_list l))
= yyyymmdd_l_correct l 0; basic_year_l_correct l 0

let tod_l_correct (l: list U8.t)
: Lemma (requires tod_l l) (ensures T.is_valid_ASN1TIMEOFDAY (Seq.seq_of_list l))
= hhmmss_l_correct false l 0

let datetime_l_correct (l: list U8.t)
: Lemma (requires datetime_l l) (ensures T.is_valid_ASN1DATETIME (Seq.seq_of_list l))
= yyyymmdd_l_correct l 0; basic_year_l_correct l 0; hhmmss_l_correct false l 8

(* OID-IRI and RELATIVE-OID-IRI (ASN1.Spec.IRI) *)

let rec iri_l (l: list U8.t) (start: nat) (i: nat { start <= i /\ i <= L.length l }) (digits: bool)
: Tot bool (decreases (L.length l - i))
= if i = L.length l || L.index l i = I.iri_slash
  then
    i > start &&
    (not digits || i = start + 1 || L.index l start <> 48uy) &&
    (i = L.length l || iri_l l (i + 1) (i + 1) true)
  else
    I.is_iri_label_char (L.index l i) &&
    iri_l l start (i + 1) (digits && I.is_iri_digit (L.index l i))

let rec iri_l_correct (l: list U8.t) (start: nat) (i: nat { start <= i /\ i <= L.length l }) (digits: bool)
: Lemma (ensures iri_l l start i digits == I.iri_labels_ok (Seq.seq_of_list l) start i digits)
  (decreases (L.length l - i))
= if i = L.length l then ()
  else if L.index l i = I.iri_slash then iri_l_correct l (i + 1) (i + 1) true
  else iri_l_correct l start (i + 1) (digits && I.is_iri_digit (L.index l i))

let rel_oid_iri_l (l: list U8.t) : Tot bool =
  utf8_l l && iri_l l 0 0 true

let oid_iri_l (l: list U8.t) : Tot bool =
  utf8_l l && L.length l > 0 && L.index l 0 = I.iri_slash && iri_l l 1 1 true

let rel_oid_iri_l_correct (l: list U8.t)
: Lemma (requires rel_oid_iri_l l) (ensures I.is_valid_relative_oid_iri (Seq.seq_of_list l))
= utf8_l_correct l; iri_l_correct l 0 0 true

let oid_iri_l_correct (l: list U8.t)
: Lemma (requires oid_iri_l l) (ensures I.is_valid_oid_iri (Seq.seq_of_list l))
= utf8_l_correct l; iri_l_correct l 1 1 true

(* The literals, for generated code:
   `(let l = [...] in assert_norm (ASN1.Lit.utctime_l [...]); ASN1.Lit.utctime_lit l ())` *)

let bytes_lit_of (p: ASN1.Bytes.asn1_bytes -> Tot bool) (k: asn1_terminal_k { asn1_key_lit k == asn1_bytes_lit p })
  (l: list U8.t) (_: squash (p (Seq.seq_of_list l)))
: Tot (asn1_key_lit k)
= let x : asn1_bytes_lit p = l in x

let utctime_lit (l: list U8.t) (_: squash (utctime_l l)) : asn1_key_lit ASN1_UTCTIME =
  utctime_l_correct l;
  assert_norm (asn1_key_lit ASN1_UTCTIME == asn1_bytes_lit T.is_valid_ASN1UTCTIME);
  bytes_lit_of T.is_valid_ASN1UTCTIME ASN1_UTCTIME l ()

let gentime_lit (l: list U8.t) (_: squash (gentime_l l)) : asn1_key_lit ASN1_GENERALIZEDTIME =
  gentime_l_correct l;
  assert_norm (asn1_key_lit ASN1_GENERALIZEDTIME == asn1_bytes_lit T.is_valid_ASN1GENERALIZEDTIME);
  bytes_lit_of T.is_valid_ASN1GENERALIZEDTIME ASN1_GENERALIZEDTIME l ()

let date_lit (l: list U8.t) (_: squash (date_l l)) : asn1_key_lit ASN1_DATE =
  date_l_correct l;
  assert_norm (asn1_key_lit ASN1_DATE == asn1_bytes_lit T.is_valid_ASN1DATE);
  bytes_lit_of T.is_valid_ASN1DATE ASN1_DATE l ()

let tod_lit (l: list U8.t) (_: squash (tod_l l)) : asn1_key_lit ASN1_TIME_OF_DAY =
  tod_l_correct l;
  assert_norm (asn1_key_lit ASN1_TIME_OF_DAY == asn1_bytes_lit T.is_valid_ASN1TIMEOFDAY);
  bytes_lit_of T.is_valid_ASN1TIMEOFDAY ASN1_TIME_OF_DAY l ()

let datetime_lit (l: list U8.t) (_: squash (datetime_l l)) : asn1_key_lit ASN1_DATE_TIME =
  datetime_l_correct l;
  assert_norm (asn1_key_lit ASN1_DATE_TIME == asn1_bytes_lit T.is_valid_ASN1DATETIME);
  bytes_lit_of T.is_valid_ASN1DATETIME ASN1_DATE_TIME l ()

let oid_iri_lit (l: list U8.t) (_: squash (oid_iri_l l)) : asn1_key_lit ASN1_OID_IRI =
  oid_iri_l_correct l;
  assert_norm (asn1_key_lit ASN1_OID_IRI == asn1_bytes_lit I.is_valid_oid_iri);
  bytes_lit_of I.is_valid_oid_iri ASN1_OID_IRI l ()

let rel_oid_iri_lit (l: list U8.t) (_: squash (rel_oid_iri_l l)) : asn1_key_lit ASN1_RELATIVE_OID_IRI =
  rel_oid_iri_l_correct l;
  assert_norm (asn1_key_lit ASN1_RELATIVE_OID_IRI == asn1_bytes_lit I.is_valid_relative_oid_iri);
  bytes_lit_of I.is_valid_relative_oid_iri ASN1_RELATIVE_OID_IRI l ()
