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
