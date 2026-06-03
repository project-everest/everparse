module CBOR.Spec.Raw.MapLexInsert

(* Lexicographic (key-then-value) strict total order on map entries, and its
   correspondence with the key-only sorted insertion [CBOR.Spec.Raw.Map.map_insert].

   Rationale: the generic sorted-insert engine
   [LowParse.PulseParse.Iterator.Sorted.mixed_list_insert_sorted] requires a
   comparator satisfying [cmp_t], i.e. a strict TOTAL order whose equality case is
   FULL element (pair) equality. The key-only entry order [map_entry_order] is only
   a strict PARTIAL order on pairs (equal keys / different values are incomparable),
   so it cannot instantiate [cmp_t]. We use the lexicographic total order
   [entry_lex_order] for the engine, and bridge its result back to the key-sorted
   [map_insert] semantics (which is what a valid CBOR map requires) under the
   hypothesis that the inserted key is absent. *)

open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.Valid           // map_entry_order
open CBOR.Spec.Raw.Map             // map_insert, map_entry_compare, map_insert_sorted, map_insert_mem
open CBOR.Spec.Raw.Format          // cbor_compare, cbor_compare_correct, deterministically_encoded_cbor_map_key_order, lemma_compare_prop
open CBOR.Spec.Raw.Sort            // compare_prop

module L = FStar.List.Tot
module U = CBOR.Spec.Util
module It = LowParse.PulseParse.Iterator   // list_narrow, list_narrow_split

let order0 : (raw_data_item -> raw_data_item -> bool) = deterministically_encoded_cbor_map_key_order

(* Lexicographic comparison on entries: compare keys, breaking ties by value. *)
let entry_lex_compare (a b: (raw_data_item & raw_data_item)) : Tot int =
  let c = cbor_compare (fst a) (fst b) in
  if c <> 0 then c else cbor_compare (snd a) (snd b)

let entry_lex_order (a b: (raw_data_item & raw_data_item)) : Tot bool =
  entry_lex_compare a b < 0

(* The strict-total-order properties of [entry_lex_order]/[entry_lex_compare] over
   entry pairs (the pair analogue of [CBOR.Spec.Raw.Sort.compare_prop], which is
   specialized to [raw_data_item]). These are exactly the facts the sorted-insert
   engine's [cmp_t] and [list_sorted_ext_eq] need. *)
let entry_compare_prop : prop =
  (forall (x: (raw_data_item & raw_data_item)). entry_lex_order x x == false) /\
  (forall (x y z: (raw_data_item & raw_data_item)). (entry_lex_order x y /\ entry_lex_order y z) ==> entry_lex_order x z) /\
  (forall (x y: (raw_data_item & raw_data_item)). entry_lex_order x y == (entry_lex_compare x y < 0)) /\
  (forall (x y: (raw_data_item & raw_data_item)). entry_lex_compare x y == 0 <==> x == y) /\
  (forall (x y: (raw_data_item & raw_data_item)). (entry_lex_compare x y < 0 <==> entry_lex_compare y x > 0))

(* [entry_lex_order]/[entry_lex_compare] form a strict total order with full-pair
   equality. Derived from [lemma_compare_prop : compare_prop order0 cbor_compare]. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let entry_lex_compare_prop : squash entry_compare_prop =
  let _ : squash (compare_prop order0 cbor_compare) = lemma_compare_prop in
  // The base facts (clauses of compare_prop) are now in context for SMT.
  introduce forall (x: (raw_data_item & raw_data_item)). entry_lex_order x x == false
  with ();
  introduce forall (x y z: (raw_data_item & raw_data_item)).
    (entry_lex_order x y /\ entry_lex_order y z) ==> entry_lex_order x z
  with introduce _ ==> _
  with _. ();
  introduce forall (x y: (raw_data_item & raw_data_item)).
    entry_lex_compare x y == 0 <==> x == y
  with begin
    let (x1, x2) = x in
    let (y1, y2) = y in
    ()
  end;
  introduce forall (x y: (raw_data_item & raw_data_item)).
    (entry_lex_compare x y < 0 <==> entry_lex_compare y x > 0)
  with begin
    let (x1, x2) = x in
    let (y1, y2) = y in
    ()
  end
#pop-options

(* A key-sorted entry list is also lexicographically sorted: consecutive entries
   have strictly key-ordered (hence distinct) keys, so the lexicographic order
   agrees with the key order on them. *)
let rec sorted_key_implies_lex
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (L.sorted (map_entry_order order0 _) l == true))
  (ensures (L.sorted entry_lex_order l == true))
  (decreases l)
= let _ : squash (compare_prop order0 cbor_compare) = lemma_compare_prop in
  let _ = entry_lex_compare_prop in
  match l with
  | [] -> ()
  | [_] -> ()
  | a :: b :: q ->
    sorted_key_implies_lex (b :: q);
    // From sorted: order0 (fst a) (fst b) == true, i.e. cbor_compare (fst a) (fst b) < 0,
    // hence cbor_compare (fst a) (fst b) <> 0, so entry_lex_compare a b == cbor_compare (fst a) (fst b) < 0,
    // i.e. entry_lex_order a b == true.
    assert (order0 (fst a) (fst b) == true);
    assert (cbor_compare (fst a) (fst b) < 0);
    assert (entry_lex_order a b == true)

(* Main correspondence: if [l] is key-sorted, the inserted key [fst y] is absent
   from [l], and [l_result] is [l] with [y] spliced at some position [kpos] while
   being lexicographically sorted, then [l_result] is exactly the key-sorted
   insertion [map_insert cbor_compare l y], and is itself key-sorted (hence a valid
   CBOR map shape). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let map_insert_lex_correct
  (l: list (raw_data_item & raw_data_item))
  (y: (raw_data_item & raw_data_item))
  (kpos: nat)
  (l_result: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    L.sorted (map_entry_order order0 _) l == true /\
    ~ (L.memP (fst y) (L.map fst l)) /\
    L.sorted entry_lex_order l_result == true /\
    kpos <= L.length l /\
    l_result == L.append (It.list_narrow l 0 kpos) (y :: It.list_narrow l kpos (L.length l - kpos))
  ))
  (ensures (
    map_insert cbor_compare l y == Some l_result /\
    L.sorted (map_entry_order order0 _) l_result == true
  ))
= let _ : squash (compare_prop order0 cbor_compare) = lemma_compare_prop in
  let _ = entry_lex_compare_prop in
  let l1 = It.list_narrow l 0 kpos in
  let l2 = It.list_narrow l kpos (L.length l - kpos) in
  // step a: l1 @ l2 == l
  It.list_narrow_split l kpos;
  // step b: map_insert produces a key-sorted list; key absent => Some
  CBOR.Spec.Raw.Map.map_insert_sorted order0 cbor_compare l y;
  let m' = map_insert cbor_compare l y in
  assert (Some? m');
  let lm = Some?.v m' in
  assert (L.sorted (map_entry_order order0 _) lm == true);
  // step c+a combined: l_result and lm have the same elements
  introduce forall (x:(raw_data_item & raw_data_item)). L.memP x l_result <==> L.memP x lm
  with begin
    L.append_memP l1 (y :: l2) x;   // memP x l_result <==> memP x l1 \/ (x==y \/ memP x l2)
    L.append_memP l1 l2 x;          // memP x l       <==> memP x l1 \/ memP x l2
    CBOR.Spec.Raw.Map.map_insert_mem cbor_compare l y x  // memP x lm <==> (x==y \/ memP x l)
  end;
  // step d: lm is also lex-sorted
  sorted_key_implies_lex lm;
  // step e: uniqueness of sorted lists => l_result == lm
  assert (U.order_irrefl entry_lex_order);
  assert (U.order_trans entry_lex_order);
  U.list_sorted_ext_eq entry_lex_order l_result lm;
  assert (l_result == lm)
#pop-options
