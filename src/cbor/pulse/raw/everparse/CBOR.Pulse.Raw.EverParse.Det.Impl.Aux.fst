module CBOR.Pulse.Raw.EverParse.Det.Impl.Aux
friend CBOR.Spec.API.Format

module Spec = CBOR.Spec.API.Format
module SpecRawBase = CBOR.Spec.Raw.Base
module SpecRaw = CBOR.Spec.Raw
module Optimal = CBOR.Spec.Raw.Optimal
module Format = CBOR.Spec.Raw.Format

let mk_det_raw_cbor_tot (c: Spec.cbor) : Tot SpecRawBase.raw_data_item
= SpecRaw.mk_det_raw_cbor c

let det_raw_list (l: list Spec.cbor) : Tot (list SpecRawBase.raw_data_item)
= List.Tot.map mk_det_raw_cbor_tot l

#push-options "--fuel 1 --ifuel 1 --z3rlimit 32"

let rec list_map_mk_det_raw_cbor_correct (l: list Spec.cbor)
: Lemma (ensures (
    let l' = det_raw_list l in
    List.Tot.for_all Optimal.raw_data_item_ints_optimal l' /\
    List.Tot.for_all (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) l'
  ))
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_det_raw_cbor_correct q

let rec list_map_mk_cbor_mk_det_raw_cbor (l: list Spec.cbor)
: Lemma (ensures (List.Tot.map SpecRaw.mk_cbor (det_raw_list l) == l))
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_cbor_mk_det_raw_cbor q

let rec mk_det_raw_cbor_inj_map (l1 l2: list Spec.cbor)
: Lemma
    (requires det_raw_list l1 == det_raw_list l2)
    (ensures l1 == l2)
    (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | x1 :: t1, x2 :: t2 ->
    SpecRaw.mk_det_raw_cbor_inj x1 x2;
    mk_det_raw_cbor_inj_map t1 t2

let rec det_raw_list_eq (l: list Spec.cbor)
: Lemma (det_raw_list l == List.Tot.map SpecRaw.mk_det_raw_cbor l)
        [SMTPat (det_raw_list l)]
= match l with
  | [] -> ()
  | _ :: q -> det_raw_list_eq q

let length_det_raw_list (l: list Spec.cbor)
  : Lemma (List.Tot.length (det_raw_list l) == List.Tot.length l)
          [SMTPat (List.Tot.length (det_raw_list l))]
= ()

let rec det_raw_list_inverse (l: list SpecRawBase.raw_data_item)
: Lemma
    (requires
      List.Tot.for_all Optimal.raw_data_item_ints_optimal l /\
      List.Tot.for_all (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) l)
    (ensures det_raw_list (List.Tot.map SpecRaw.mk_cbor l) == l)
    (decreases l)
= match l with
  | [] -> ()
  | x :: q ->
    SpecRaw.mk_det_raw_cbor_mk_cbor x;
    det_raw_list_inverse q

let det_raw_list_take_eq (l: list Spec.cbor) (n: nat)
: Lemma
    (det_raw_list (fst (List.Tot.splitAt n l)) ==
     LowParse.PulseParse.Iterator.list_narrow (det_raw_list l) 0 n)
= CBOR.Spec.Util.list_map_splitAt mk_det_raw_cbor_tot l n;
  // list_narrow lr 0 n == fst (splitAt n (snd (splitAt 0 lr)))
  //                     == fst (splitAt n lr)  (since splitAt 0 lr == ([], lr))
  assert (List.Tot.splitAt 0 (det_raw_list l) == ([], det_raw_list l))

(* Lemma: when y is a det cbor that unpacks to CArray l, then mk_det_raw_cbor y is Array _ (det_raw_list l) *)
let mk_det_raw_cbor_array_eq (y: Spec.cbor) (l: list Spec.cbor)
: Lemma
    (requires
      FStar.UInt.fits (List.Tot.length l) 64 /\
      Spec.unpack y == Spec.CArray l)
    (ensures
       SpecRawBase.Array? (SpecRaw.mk_det_raw_cbor y) /\
       (SpecRawBase.Array?.v (SpecRaw.mk_det_raw_cbor y) <: list SpecRawBase.raw_data_item) == det_raw_list l /\
       SpecRawBase.Array?.len (SpecRaw.mk_det_raw_cbor y) ==
         Optimal.mk_raw_uint64 (FStar.UInt64.uint_to_t (List.Tot.length l)))
= Spec.pack_unpack y;
  let len = Optimal.mk_raw_uint64 (FStar.UInt64.uint_to_t (List.Tot.length l)) in
  let l' = det_raw_list l in
  let x : SpecRawBase.raw_data_item = SpecRawBase.Array len l' in
  list_map_mk_cbor_mk_det_raw_cbor l;
  list_map_mk_det_raw_cbor_correct l;
  Optimal.raw_data_item_sorted_optimal_valid Format.deterministically_encoded_cbor_map_key_order x;
  SpecRaw.mk_cbor_eq x;
  SpecRaw.mk_det_raw_cbor_mk_cbor x;
  assert (SpecRaw.mk_det_raw_cbor (Spec.pack (Spec.CArray l)) == x)

#pop-options

(* ====================================================================
   Map-entry helpers (foundation for cbor_det_map_iterator_match). *)

let det_raw_map_entries
  (l: list (Spec.cbor & Spec.cbor))
: Tot (list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
= List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry l

let rec mk_det_raw_cbor_inj_map_entries
  (l1 l2: list (Spec.cbor & Spec.cbor))
: Lemma
    (requires det_raw_map_entries l1 == det_raw_map_entries l2)
    (ensures l1 == l2)
    (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | (k1, v1) :: t1, (k2, v2) :: t2 ->
    SpecRaw.mk_det_raw_cbor_inj k1 k2;
    SpecRaw.mk_det_raw_cbor_inj v1 v2;
    mk_det_raw_cbor_inj_map_entries t1 t2

let det_raw_map_entries_eq
  (l: list (Spec.cbor & Spec.cbor))
: Lemma
    (det_raw_map_entries l == List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry l)
    [SMTPat (det_raw_map_entries l)]
= ()

let rec length_det_raw_map_entries
  (l: list (Spec.cbor & Spec.cbor))
: Lemma
    (List.Tot.length (det_raw_map_entries l) == List.Tot.length l)
    [SMTPat (List.Tot.length (det_raw_map_entries l))]
= match l with
  | [] -> ()
  | _ :: q -> length_det_raw_map_entries q

(* Inverse / soundness lemmas for cbor_det_map_iterator_next. *)

let rec list_map_mk_cbor_mk_det_raw_cbor_map_entry (l: list (Spec.cbor & Spec.cbor))
: Lemma (ensures (List.Tot.map SpecRaw.mk_cbor_map_entry (det_raw_map_entries l) == l))
= match l with
  | [] -> ()
  | (k, v) :: q ->
    list_map_mk_cbor_mk_det_raw_cbor [k];
    list_map_mk_cbor_mk_det_raw_cbor [v];
    list_map_mk_cbor_mk_det_raw_cbor_map_entry q

let rec list_map_mk_det_raw_cbor_correct_map_entries (l: list (Spec.cbor & Spec.cbor))
: Lemma (ensures (
    let l' = det_raw_map_entries l in
    List.Tot.for_all
      (CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal) l' /\
    List.Tot.for_all
      (CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order)) l'
  ))
= match l with
  | [] -> ()
  | (k, v) :: q ->
    list_map_mk_det_raw_cbor_correct [k];
    list_map_mk_det_raw_cbor_correct [v];
    list_map_mk_det_raw_cbor_correct_map_entries q

let rec det_raw_map_entries_inverse (l: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
: Lemma
    (requires
      List.Tot.for_all
        (CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal) l /\
      List.Tot.for_all
        (CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order)) l)
    (ensures det_raw_map_entries (List.Tot.map SpecRaw.mk_cbor_map_entry l) == l)
    (decreases l)
= match l with
  | [] -> ()
  | (k, v) :: q ->
    SpecRaw.mk_det_raw_cbor_mk_cbor k;
    SpecRaw.mk_det_raw_cbor_mk_cbor v;
    det_raw_map_entries_inverse q

let mk_det_raw_cbor_map_entry_mk_cbor_map_entry (x: SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)
: Lemma
    (requires
      CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal x /\
      CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) x)
    (ensures (SpecRaw.mk_det_raw_cbor_map_entry (SpecRaw.mk_cbor_map_entry x) == x))
= SpecRaw.mk_det_raw_cbor_mk_cbor (fst x);
  SpecRaw.mk_det_raw_cbor_mk_cbor (snd x)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"

module SpecRawValid = CBOR.Spec.Raw.Valid

let valid_pair_of_sorted_optimal
  (kv: SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)
: Lemma
    (requires
      CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) kv /\
      CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal kv)
    (ensures
      SpecRawValid.valid_raw_data_item (fst kv) /\
      SpecRawValid.valid_raw_data_item (snd kv))
= Optimal.raw_data_item_sorted_optimal_valid Format.deterministically_encoded_cbor_map_key_order (fst kv);
  Optimal.raw_data_item_sorted_optimal_valid Format.deterministically_encoded_cbor_map_key_order (snd kv)

let rec for_all_valid_fst_of_mk_det_raw
  (l: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
: Lemma
    (requires
      List.Tot.for_all
        (CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order)) l /\
      List.Tot.for_all
        (CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal) l)
    (ensures
      List.Tot.for_all SpecRawValid.valid_raw_data_item (List.Tot.map fst l) /\
      List.Tot.for_all SpecRawValid.valid_raw_data_item (List.Tot.map snd l))
    (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    valid_pair_of_sorted_optimal a;
    for_all_valid_fst_of_mk_det_raw q

let mk_det_raw_cbor_map_eq (y: Spec.cbor) (l: list (Spec.cbor & Spec.cbor))
: Lemma
    (requires
      Spec.CMap? (Spec.unpack y) /\
      FStar.UInt.fits (List.Tot.length l) 64 /\
      l == List.Tot.map SpecRaw.mk_cbor_map_entry (SpecRaw.mk_det_raw_cbor_map_raw (Spec.CMap?.c (Spec.unpack y))))
    (ensures (
       SpecRawBase.Map? (SpecRaw.mk_det_raw_cbor y) /\
       (SpecRawBase.Map?.v (SpecRaw.mk_det_raw_cbor y) <: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)) == det_raw_map_entries l /\
       List.Tot.length l == Spec.cbor_map_length (Spec.CMap?.c (Spec.unpack y)) /\
       List.Tot.no_repeats_p (List.Tot.map fst l) /\
       (forall (k: Spec.cbor) . Spec.cbor_map_get (Spec.CMap?.c (Spec.unpack y)) k == List.Tot.assoc k l)
    ))
= let m : Spec.cbor_map = Spec.CMap?.c (Spec.unpack y) in
  let raw_l = SpecRaw.mk_det_raw_cbor_map_raw m in
  // 1. mk_det_raw_cbor y == Map _ raw_l
  SpecRaw.mk_cbor_eq_map y;
  // 2. det_raw_map_entries l == raw_l (inverse round-trip)
  det_raw_map_entries_inverse raw_l;
  // 3. no_repeats: raw_l is sorted, so no_repeats; lift to l
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats Format.deterministically_encoded_cbor_map_key_order raw_l;
  SpecRaw.no_repeats_map_fst_mk_det_raw_cbor_map_entry l;
  // 4. validity for_all on raw_l projections
  for_all_valid_fst_of_mk_det_raw raw_l;
  // 5. mk_cbor_match_map raw_l m via mk_cbor_eq
  SpecRaw.mk_cbor_eq (SpecRaw.mk_det_raw_cbor y);
  // 6. assoc: cbor_map_get m k == List.Tot.assoc k l
  let prf (k: Spec.cbor) : Lemma
    (Spec.cbor_map_get m k == List.Tot.assoc k l)
  = SpecRaw.list_assoc_map_mk_cbor_map_entry m raw_l () k
  in
  Classical.forall_intro prf

#pop-options
