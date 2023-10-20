module CBOR.Spec.Type
open LowParse.WellFounded

// Ordering of map keys (Section 4.2)

let holds_on_pair_bounded
  (#t0: Type)
  (bound: t0)
  (#t: Type)
  (pred: ((x: t { x << bound }) -> bool))
  (x: (t & t) { x << bound })
: Tot bool
= let (x1, x2) = x in
  pred x1 && pred x2

let rec holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  begin match x with
  | Array l -> forall_list l (holds_on_raw_data_item p)
  | Map l ->
    let l : list (raw_data_item & raw_data_item) = l in // IMPORTANT to remove the refinement on the type of the `bound` arg to holds_on_pair_bounded
    forall_list l (holds_on_pair_bounded l (holds_on_raw_data_item p))
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

#push-options "--z3rlimit 16"

#restart-solver
let holds_on_raw_data_item_eq
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == holds_on_raw_data_item' p x)
= match x with
  | Array l ->
    assert_norm (holds_on_raw_data_item p (Array l) == (p (Array l) && forall_list l (holds_on_raw_data_item p)));
    forall_list_correct (holds_on_raw_data_item p) l
  | Map l ->
    let l : list (raw_data_item & raw_data_item) = l in
    assert_norm (holds_on_raw_data_item p (Map l) == (p (Map l) && forall_list l (holds_on_pair_bounded l (holds_on_raw_data_item p))));
    forall_list_correct (holds_on_pair (holds_on_raw_data_item p)) l;
    forall_list_ext l (holds_on_pair (holds_on_raw_data_item p)) (holds_on_pair_bounded l (holds_on_raw_data_item p)) (fun _ -> ())
  | _ -> ()

#pop-options
