module ASN1.Pulse.SetComp
#lang-pulse
(* Validators for SET { ... }: a list of elements, each of which is the
   encoding of one component, strictly sorted by tag, each component
   appearing at most once and each mandatory component at least once
   (ASN1.Spec.SetComponents.set_ok.) The loop keeps the previous tag and a
   bitmask of the components seen so far (at most 64 components.) *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Tot.Base
open LowParse.Tot.List
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module T = LowParse.Tot.Combinators
module I = ASN1.Pulse.Identifier
module L = FStar.List.Tot
module Conf = ASN1.Spec.Conformance

(* Component index of an element *)

let rec elem_comp (its: list gen_decorated_parser_twin) (e: set_elem_t its)
: Tot (i: nat { i < L.length its }) (decreases its)
= match its with
  | hd :: tl ->
    let e0 : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
    match e0 with
    | Inl _ -> 0
    | Inr e' -> 1 + elem_comp tl e'

let rec count_comp (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) (i: nat) : Tot nat =
  match l with
  | [] -> 0
  | e :: q -> (if elem_comp its e = i then 1 else 0) + count_comp its q i

let defaultable (its: list gen_decorated_parser_twin) (i: nat { i < L.length its }) : Tot bool =
  Some? (generate_defaultable_item (L.index its i))

#push-options "--fuel 2 --ifuel 2"
let rec heads_tails_count
  (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (l: list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)))
: Lemma
  (ensures (
    L.length (heads l) == count_comp (hd :: tl) l 0 /\
    (forall (i: nat) . count_comp tl (tails l) i == count_comp (hd :: tl) l (i + 1))))
  (decreases l)
= match l with
  | [] -> ()
  | x :: q ->
    heads_tails_count hd tl q;
    let its = hd :: tl in
    let x' : set_elem_t its = x in
    match x with
    | Inl _ ->
      assert (elem_comp its x' == 0);
      assert (tails l == tails q);
      let prf (i: nat) : Lemma (count_comp tl (tails l) i == count_comp (hd :: tl) l (i + 1))
      = assert (count_comp its l (i + 1) == (if elem_comp its x' = i + 1 then 1 else 0) + count_comp its q (i + 1))
      in
      Classical.forall_intro prf
    | Inr y ->
      assert (elem_comp its x' == 1 + elem_comp tl y);
      assert (tails l == y :: tails q);
      assert (heads l == heads q);
      let prf (i: nat) : Lemma (count_comp tl (tails l) i == count_comp (hd :: tl) l (i + 1))
      = assert (count_comp tl (y :: tails q) i == (if elem_comp tl y = i then 1 else 0) + count_comp tl (tails q) i);
        assert (count_comp its l (i + 1) == (if elem_comp its x' = i + 1 then 1 else 0) + count_comp its q (i + 1))
      in
      Classical.forall_intro prf;
      assert (count_comp its l 0 == (if elem_comp its x' = 0 then 1 else 0) + count_comp its q 0)
#pop-options

let comps_q (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) (i: nat) : prop =
  i < L.length its ==> (count_comp its l i <= 1 /\ (count_comp its l i == 0 ==> defaultable its i))

let comps_spec (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) : prop =
  forall (i: nat) . comps_q its l i

let forall_nat_split (q: nat -> prop)
: Lemma ((forall (i: nat) . q i) <==> (q 0 /\ (forall (j: nat) . q (j + 1))))
= let aux (i: nat) : Lemma (requires (q 0 /\ (forall (j: nat) . q (j + 1)))) (ensures (q i))
  = if i = 0 then () else assert (q ((i - 1) + 1))
  in
  Classical.forall_intro (Classical.move_requires aux)

let comp_ok_iff (hd: gen_decorated_parser_twin) (h: list (asn1_decorated_t (Mkgendcparser?.d hd)))
: Lemma (comp_ok hd h <==> (L.length h <= 1 /\ (L.length h == 0 ==> Some? (generate_defaultable_item hd))))
= match h with
  | [] -> ()
  | [_] -> ()
  | _ :: _ :: _ -> ()

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let rec comps_ok_iff (its: list gen_decorated_parser_twin) (l: list (set_elem_t its))
: Lemma (ensures (comps_ok its l <==> comps_spec its l)) (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
    heads_tails_count hd tl l';
    comps_ok_iff tl (tails l');
    comp_ok_iff hd (heads l');
    forall_nat_split (comps_q its l);
    let prf (j: nat) : Lemma (comps_q its l (j + 1) <==> comps_q tl (tails l') j)
    = if j < L.length tl then assert (L.index its (j + 1) == L.index tl j) else ()
    in
    Classical.forall_intro prf;
    assert (comps_q its l 0 <==> comp_ok hd (heads l'))
#pop-options

(* Bitmasks *)

let bit (m: U64.t) (i: nat { i < 64 }) : Tot bool = FStar.UInt.nth #64 (U64.v m) (63 - i)

inline_for_extraction
let set_bit (m: U64.t) (i: U32.t { U32.v i < 64 }) : Tot U64.t = U64.logor m (U64.shift_left 1uL i)

inline_for_extraction
let test_bit (m: U64.t) (i: U32.t { U32.v i < 64 }) : Tot bool = not (U64.logand m (U64.shift_left 1uL i) = 0uL)

let one_shift_nth (i: nat { i < 64 }) (j: nat { j < 64 })
: Lemma (FStar.UInt.nth #64 (U64.v (U64.shift_left 1uL (U32.uint_to_t i))) j == (j = 63 - i))
= FStar.UInt.shift_left_value_lemma #64 1 i;
  if j < 64 - i
  then begin
    FStar.UInt.shift_left_lemma_2 #64 1 i j;
    FStar.UInt.one_nth_lemma #64 (j + i)
  end
  else FStar.UInt.shift_left_lemma_1 #64 1 i j

let bit' (m: U64.t) (i: nat) : Tot bool = i < 64 && bit m i

let set_bit_spec (m: U64.t) (i: U32.t { U32.v i < 64 }) (j: nat { j < 64 })
: Lemma (bit (set_bit m i) j == (bit m j || j = U32.v i))
= FStar.UInt.logor_definition #64 (U64.v m) (U64.v (U64.shift_left 1uL i)) (63 - j);
  one_shift_nth (U32.v i) (63 - j)

let test_bit_spec (m: U64.t) (i: U32.t { U32.v i < 64 })
: Lemma (test_bit m i == bit m (U32.v i))
= let a = U64.v (U64.logand m (U64.shift_left 1uL i)) in
  let prf (j: nat { j < 64 }) : Lemma (FStar.UInt.nth #64 a j == (FStar.UInt.nth #64 (U64.v m) j && j = 63 - U32.v i))
  = FStar.UInt.logand_definition #64 (U64.v m) (U64.v (U64.shift_left 1uL i)) j;
    one_shift_nth (U32.v i) j
  in
  Classical.forall_intro prf;
  if bit m (U32.v i)
  then FStar.UInt.zero_nth_lemma #64 (63 - U32.v i)
  else begin
    Classical.forall_intro (FStar.UInt.zero_nth_lemma #64);
    FStar.UInt.nth_lemma #64 a (FStar.UInt.zero 64)
  end

let bit_zero (j: nat { j < 64 }) : Lemma (bit 0uL j == false)
= FStar.UInt.zero_nth_lemma #64 (63 - j)

(* Final check: each component not seen is defaultable *)

let rec final_ok' (its: list gen_decorated_parser_twin) (j: nat) (m: U64.t) : Tot bool (decreases its) =
  match its with
  | [] -> true
  | hd :: tl -> ((j < 64 && bit m j) || Some? (generate_defaultable_item hd)) && final_ok' tl (j + 1) m

let final_ok (its: list gen_decorated_parser_twin) (m: U64.t) : Tot bool = final_ok' its 0 m

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let rec final_ok'_iff (its: list gen_decorated_parser_twin) (j: nat) (m: U64.t)
: Lemma
  (requires (j + L.length its <= 64))
  (ensures (final_ok' its j m <==> (forall (i: nat) . i < L.length its ==> (bit m (i + j) \/ defaultable its i))))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    final_ok'_iff tl (j + 1) m;
    assert (forall (i: nat) . i < L.length tl ==> L.index its (i + 1) == L.index tl i);
    assert ((forall (i: nat) . i < L.length its ==> (bit m (i + j) \/ defaultable its i)) <==> (
      (bit m j \/ defaultable its 0) /\
      (forall (i: nat) . i < L.length tl ==> (bit m ((i + 1) + j) \/ defaultable its (i + 1)))))
#pop-options

(* The loop, as a fold over the list of elements *)

let prev_ok (prev: option asn1_id_t) (t: asn1_id_t) : Tot bool =
  match prev with
  | None -> true
  | Some p -> asn1_tag_lt p t

let rec set_loop (its: list gen_decorated_parser_twin) (prev: option asn1_id_t) (m: U64.t) (l: list (set_elem_t its))
: Tot bool (decreases l)
= match l with
  | [] -> final_ok its m
  | e :: q ->
    begin match elem_tag its e with
    | None -> false
    | Some t ->
      let c = elem_comp its e in
      prev_ok prev t && c < 64 && not (bit m c) && set_loop its (Some t) (set_bit m (U32.uint_to_t c)) q
    end

let sorted_from (its: list gen_decorated_parser_twin) (prev: option asn1_id_t) (l: list (set_elem_t its)) : Tot bool =
  tags_sorted (elem_tag its) l &&
  (match prev, l with
   | Some p, x :: _ -> opt_tag_lt (Some p) (elem_tag its x)
   | _ -> true)

let loop_spec (its: list gen_decorated_parser_twin) (prev: option asn1_id_t) (m: U64.t) (l: list (set_elem_t its)) : prop =
  sorted_from its prev l /\
  (forall (i: nat) . i < L.length its ==>
    (count_comp its l i + (if bit' m i then 1 else 0) <= 1 /\
     ((count_comp its l i == 0 /\ bit' m i == false) ==> defaultable its i)))

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec set_loop_iff (its: list gen_decorated_parser_twin) (prev: option asn1_id_t) (m: U64.t) (l: list (set_elem_t its))
: Lemma
  (requires (L.length its <= 64))
  (ensures (set_loop its prev m l <==> loop_spec its prev m l))
  (decreases l)
= match l with
  | [] -> final_ok'_iff its 0 m
  | e :: q ->
    begin match elem_tag its e with
    | None -> ()
    | Some t ->
      let c = elem_comp its e in
      let m' = set_bit m (U32.uint_to_t c) in
      Classical.forall_intro (set_bit_spec m (U32.uint_to_t c));
      set_loop_iff its (Some t) m' q;
      assert (sorted_from its prev l <==> (prev_ok prev t /\ sorted_from its (Some t) q));
      assert (forall (i: nat) . count_comp its l i == count_comp its q i + (if i = c then 1 else 0));
      if bit m c then begin
        assert (~ (count_comp its l c + (if bit' m c then 1 else 0) <= 1))
      end else begin
        assert (forall (i: nat) . i < L.length its ==> (if bit' m' i then 1 else 0) == (if bit' m i then 1 else 0) + (if i = c then 1 else 0))
      end
    end
#pop-options

let set_ok_iff (its: list gen_decorated_parser_twin) (l: list (set_elem_t its))
: Lemma
  (requires (L.length its <= 64))
  (ensures (set_ok its l == set_loop its None 0uL l))
= comps_ok_iff its l;
  set_loop_iff its None 0uL l;
  Classical.forall_intro bit_zero

(* Component index of an identifier *)

let rec comp_of_id (its: list gen_decorated_parser_twin) (id: asn1_id_t)
: Tot (o: option nat { match o with None -> True | Some i -> i < L.length its }) (decreases its) =
  match its with
  | [] -> None
  | hd :: tl ->
    if Set.mem id (item_set hd)
    then Some 0
    else match comp_of_id tl id with
    | None -> None
    | Some i -> Some (i + 1)

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
let rec comp_of_id_correct (its: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (ensures (match SB.parse (parse_set_elem_twin its id) b with
    | Some (e, _) -> comp_of_id its id == Some (elem_comp its e)
    | None -> True))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    if Set.mem id s
    then T.parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b
    else begin
      comp_of_id_correct tl id b;
      T.parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b
    end
#pop-options

(* The content parser *)

let rest_ok (its: list gen_decorated_parser_twin) (prev: option asn1_id_t) (m: U64.t) (b: bytes) : GTot bool =
  match SB.parse (parse_list (parse_set_elem its)) b with
  | None -> false
  | Some (l, _) -> set_loop its prev m l

let rec parse_list_consumes_all (#t: Type) (p: parser asn1_strong_parser_kind t) (b: bytes)
: Lemma
  (ensures (match SB.parse (parse_list p) b with
    | None -> True
    | Some (_, n) -> n == Seq.length b))
  (decreases (Seq.length b))
= LowParse.Spec.List.tot_parse_list_eq p b;
  if Seq.length b = 0
  then ()
  else match SB.parse p b with
  | None -> ()
  | Some (_, n) ->
    if n = 0 then ()
    else parse_list_consumes_all p (Seq.slice b n (Seq.length b))

let set_content_eq (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (L.length its <= 64))
  (ensures (consumed #asn1_weak_parser_kind (make_asn1_set_parser its) b ==
    (if rest_ok its None 0uL b then Some (Seq.length b) else None)))
= set_to_tuple_injective its;
  T.parse_synth_eq (parse_list (parse_set_elem its) `T.parse_filter` set_ok its) (set_to_tuple its) b;
  T.parse_filter_eq (parse_list (parse_set_elem its)) (set_ok its) b;
  parse_list_consumes_all (parse_set_elem its) b;
  match SB.parse (parse_list (parse_set_elem its)) b with
  | None -> ()
  | Some (l, _) -> set_ok_iff its l

let set_elem_eq (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (Conf.items_tagged its))
  (ensures (match SB.parse (parse_set_elem its) b with
    | None -> True
    | Some (e, n) ->
      begin match SB.parse parse_asn1_identifier_U32 b with
      | None -> False
      | Some (id, n1) ->
        elem_tag its e == Some id /\
        comp_of_id its id == Some (elem_comp its e) /\
        n1 <= n /\
        consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice b n1 (Seq.length b)) == Some (n - n1 <: nat)
      end))
= parse_set_elem_twin_cases_injective its;
  T.and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t its) (parse_set_elem_twin its) b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, n1) ->
    let b' = Seq.slice b n1 (Seq.length b) in
    Conf.set_elem_twin_tag its id b';
    comp_of_id_correct its id b'

let set_elem_fail (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (ensures (match SB.parse parse_asn1_identifier_U32 b with
    | None -> None? (SB.parse (parse_set_elem its) b)
    | Some (id, n1) ->
      (None? (consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice b n1 (Seq.length b))) ==> None? (SB.parse (parse_set_elem its) b)) /\
      (match consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice b n1 (Seq.length b)) with
       | None -> True
       | Some n2 -> consumed #asn1_strong_parser_kind (parse_set_elem its) b == Some (n1 + n2))))
= parse_set_elem_twin_cases_injective its;
  T.and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t its) (parse_set_elem_twin its) b

let opt_u32_v (o: option U32.t) : Tot (option nat) =
  match o with
  | None -> None
  | Some i -> Some (U32.v i)

(* One step of the loop: [rest_ok] on a nonempty input *)

let slice_tail (v: bytes) (off: nat) (k: nat)
: Lemma
  (requires (off + k <= Seq.length v))
  (ensures (Seq.slice (Seq.slice v off (Seq.length v)) k (Seq.length v - off) == Seq.slice v (off + k) (Seq.length v)))
= assert (Seq.slice (Seq.slice v off (Seq.length v)) k (Seq.length v - off) `Seq.equal` Seq.slice v (off + k) (Seq.length v))

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rest_step
  (its: list gen_decorated_parser_twin)
  (prev: option asn1_id_t) (m: U64.t)
  (v: bytes) (off: nat) (id: asn1_id_t) (off1: nat) (c: nat { c < 64 }) (off2: nat)
: Lemma
  (requires (
    Conf.items_tagged its /\
    off <= off1 /\ off < off2 /\ off1 <= off2 /\ off2 <= Seq.length v /\
    SB.parse parse_asn1_identifier_U32 (Seq.slice v off (Seq.length v)) == Some (id, (off1 - off <: nat)) /\
    comp_of_id its id == Some c /\
    consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice v off1 (Seq.length v)) == Some (off2 - off1 <: nat)))
  (ensures (
    rest_ok its prev m (Seq.slice v off (Seq.length v)) ==
      (prev_ok prev id && not (bit m c) && rest_ok its (Some id) (set_bit m (U32.uint_to_t c)) (Seq.slice v off2 (Seq.length v)))))
= let b = Seq.slice v off (Seq.length v) in
  let n1 : nat = off1 - off in
  slice_tail v off n1;
  set_elem_fail its b;
  assert (consumed #asn1_strong_parser_kind (parse_set_elem its) b == Some (off2 - off <: nat));
  let Some (e, n) = SB.parse (parse_set_elem its) b in
  assert (n == off2 - off);
  set_elem_eq its b;
  assert (elem_tag its e == Some id);
  assert (elem_comp its e == c);
  slice_tail v off n;
  let b' = Seq.slice v off2 (Seq.length v) in
  assert (Seq.length b > 0);
  LowParse.Spec.List.tot_parse_list_eq (parse_set_elem its) b;
  assert (SB.parse (parse_list (parse_set_elem its)) b == (match SB.parse (parse_list (parse_set_elem its)) b' with
    | None -> None
    | Some (l, n') -> Some (e :: l, (n + n' <: SB.consumed_length b))));
  match SB.parse (parse_list (parse_set_elem its)) b' with
  | None -> ()
  | Some (l, _) ->
    assert (set_loop its prev m (e :: l) == (prev_ok prev id && c < 64 && not (bit m c) && set_loop its (Some id) (set_bit m (U32.uint_to_t c)) l))
#pop-options

let rest_step_fail
  (its: list gen_decorated_parser_twin)
  (prev: option asn1_id_t) (m: U64.t)
  (v: bytes) (off: nat)
: Lemma
  (requires (
    off < Seq.length v /\
    (match SB.parse parse_asn1_identifier_U32 (Seq.slice v off (Seq.length v)) with
     | None -> True
     | Some (id, n1) ->
       Conf.items_tagged its /\
       (None? (comp_of_id its id) \/ None? (consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice v (off + n1) (Seq.length v)))))))
  (ensures (rest_ok its prev m (Seq.slice v off (Seq.length v)) == false))
= let b = Seq.slice v off (Seq.length v) in
  LowParse.Spec.List.tot_parse_list_eq (parse_set_elem its) b;
  set_elem_fail its b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, n1) ->
    slice_tail v off n1;
    set_elem_eq its b;
    assert (None? (SB.parse (parse_set_elem its) b));
    assert (SB.parse (parse_list (parse_set_elem its)) b == None)

let rest_step_empty
  (its: list gen_decorated_parser_twin)
  (prev: option asn1_id_t) (m: U64.t)
  (v: bytes) (off: nat) (id: asn1_id_t)
: Lemma
  (requires (
    off < Seq.length v /\
    SB.parse parse_asn1_identifier_U32 (Seq.slice v off (Seq.length v)) == Some (id, 0) /\
    consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice v off (Seq.length v)) == Some 0))
  (ensures (rest_ok its prev m (Seq.slice v off (Seq.length v)) == false))
= let b = Seq.slice v off (Seq.length v) in
  LowParse.Spec.List.tot_parse_list_eq (parse_set_elem its) b;
  set_elem_fail its b;
  slice_tail v off 0;
  assert (consumed #asn1_strong_parser_kind (parse_set_elem its) b == Some 0);
  assert (SB.parse (parse_list (parse_set_elem its)) b == None)

let rest_empty (its: list gen_decorated_parser_twin) (prev: option asn1_id_t) (m: U64.t) (b: bytes)
: Lemma
  (requires (Seq.length b == 0))
  (ensures (rest_ok its prev m b == final_ok its m))
= LowParse.Spec.List.tot_parse_list_eq (parse_set_elem its) b

let set_elem_twin_cons_consumed
  (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (consumed #asn1_strong_parser_kind (parse_set_elem_twin (hd :: tl) id) b ==
    (if Set.mem id (item_set hd)
     then consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b
     else consumed #asn1_strong_parser_kind (parse_set_elem_twin tl id) b))
= T.parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b;
  T.parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b

inline_for_extraction
let class_rank (c: asn1_id_class_t) : Tot (r: U32.t { U32.v r == asn1_id_class_rank c }) =
  match c with
  | UNIVERSAL -> 0ul
  | APPLICATION -> 1ul
  | CONTEXT_SPECIFIC -> 2ul
  | PRIVATE -> 3ul

inline_for_extraction
let tag_lt (a b: asn1_id_t) : Tot (r: bool { r == asn1_tag_lt a b }) =
  match a, b with
  | MK_ASN1_ID ca _ va, MK_ASN1_ID cb _ vb ->
    let ra = class_rank ca in
    let rb = class_rank cb in
    U32.lt ra rb || (ra = rb && U32.lt va vb)

(* The validator *)

let set_ready (its: list gen_decorated_parser_twin) : prop =
  Conf.items_tagged its /\ L.length its <= 64

#push-options "--z3rlimit 128"
inline_for_extraction
fn validate_set
  (its: Ghost.erased (list gen_decorated_parser_twin) { set_ready its })
  (comp: (id: asn1_id_t) -> Tot (r: option U32.t { opt_u32_v r == comp_of_id its id }))
  (final: (m: U64.t) -> Tot (b: bool { b == final_ok its m }))
  (vtwin: (id: asn1_id_t) -> LPS.validator #(set_elem_t its) #asn1_strong_parser_kind (parse_set_elem_twin its id))
: LPS.validator #(asn1_sequence_t (List.Tot.map Mkgendcparser?.d its)) #asn1_weak_parser_kind (make_asn1_set_parser its)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  S.pts_to_len input;
  let input_len = S.len input;
  set_content_eq its (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  let mut pcontinue = true;
  let mut pfirst = true;
  let mut pprev = MK_ASN1_ID UNIVERSAL PRIMITIVE 0ul;
  let mut pmask = 0uL;
  while (
    let c = !pcontinue;
    let off = !poffset;
    (c && SZ.lt off input_len)
  ) invariant exists* c first prev m off .
    R.pts_to pcontinue c **
    R.pts_to pfirst first **
    R.pts_to pprev prev **
    R.pts_to pmask m **
    R.pts_to poffset off **
    S.pts_to input #pm v_bytes **
    pure (
      SZ.v offset <= Seq.length v_bytes /\ SZ.v off <= Seq.length v_bytes /\
      (c == true ==> SZ.v offset <= SZ.v off) /\
      (c == true ==>
        rest_ok its None 0uL (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes)) ==
        rest_ok its (if first then None else Some prev) m (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes))) /\
      (c == false ==> rest_ok its None 0uL (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes)) == false)
    )
    decreases %[(if !pcontinue then 1 else 0); (SZ.v input_len - SZ.v (!poffset))]
  {
    let off = !poffset;
    let first = !pfirst;
    let prev = !pprev;
    let m = !pmask;
    let oid = I.vread_identifier input poffset;
    match oid {
      None -> {
        rest_step_fail its (if first then None else Some prev) m v_bytes (SZ.v off);
        pcontinue := false
      }
      Some id -> {
        with off1 . assert (R.pts_to poffset off1);
        Seq.slice_slice v_bytes (SZ.v off) (Seq.length v_bytes) (SZ.v off1 - SZ.v off) (Seq.length v_bytes - SZ.v off);
        match comp id {
          None -> {
            rest_step_fail its (if first then None else Some prev) m v_bytes (SZ.v off);
            pcontinue := false
          }
          Some c -> {
            let is_valid = vtwin id input poffset;
            if is_valid {
              let off2 = !poffset;
              if (off2 = off) {
                assert (pure (SZ.v off1 == SZ.v off));
                assert (pure (SB.parse parse_asn1_identifier_U32 (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes)) == Some (id, 0)));
                assert (pure (consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes)) == Some 0));
                rest_step_empty its (if first then None else Some prev) m v_bytes (SZ.v off) id;
                pcontinue := false
              } else {
                assert (pure (SZ.v off <= SZ.v off1 /\ SZ.v off1 <= SZ.v off2 /\ SZ.v off <> SZ.v off2));
                assert (pure (comp_of_id its id == Some (U32.v c) /\ U32.v c < 64));
                assert (pure (SB.parse parse_asn1_identifier_U32 (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes)) == Some (id, (SZ.v off1 - SZ.v off <: nat))));
                assert (pure (consumed #asn1_strong_parser_kind (parse_set_elem_twin its id) (Seq.slice v_bytes (SZ.v off1) (Seq.length v_bytes)) == Some (SZ.v off2 - SZ.v off1 <: nat)));
                rest_step its (if first then None else Some prev) m v_bytes (SZ.v off) id (SZ.v off1) (U32.v c) (SZ.v off2);
                test_bit_spec m c;
                let ok = ((first || tag_lt prev id) && not (test_bit m c));
                if ok {
                  pfirst := false;
                  pprev := id;
                  pmask := set_bit m c
                } else {
                  pcontinue := false
                }
              }
            } else {
              rest_step_fail its (if first then None else Some prev) m v_bytes (SZ.v off);
              pcontinue := false
            }
          }
        }
      }
    }
  };
  let c = !pcontinue;
  if c {
    let m = !pmask;
    with first prev . assert (R.pts_to pfirst first ** R.pts_to pprev prev);
    rest_empty its (if first then None else Some prev) m (Seq.slice v_bytes (SZ.v input_len) (Seq.length v_bytes));
    final m
  } else {
    false
  }
}
#pop-options
