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
       (SpecRawBase.Array?.v (SpecRaw.mk_det_raw_cbor y) <: list SpecRawBase.raw_data_item) == det_raw_list l)
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
