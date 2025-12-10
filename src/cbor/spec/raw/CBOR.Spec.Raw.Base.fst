module CBOR.Spec.Raw.Base

let rec holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  begin match x with
  | Array _ l -> wf_list_for_all l (holds_on_raw_data_item p)
  | Map _ l ->
    wf_list_for_all l (holds_on_pair_raw_data_item p)
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

and holds_on_pair_raw_data_item
  (p: (raw_data_item -> bool))
  (x: (raw_data_item & raw_data_item))
: Tot bool
= holds_on_raw_data_item p (fst x) &&
  holds_on_raw_data_item p (snd x)

let holds_on_raw_data_item_eq
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == holds_on_raw_data_item' p x)
= match x with
  | Array len l ->
    assert_norm (holds_on_raw_data_item p (Array len l) == (p (Array len l) && wf_list_for_all l (holds_on_raw_data_item p)));
    wf_list_for_all_eq (holds_on_raw_data_item p) l
  | Map len l ->
    assert_norm (holds_on_raw_data_item p (Map len l) == (p (Map len l) && wf_list_for_all l (holds_on_pair_raw_data_item p)));
    wf_list_for_all_eq (holds_on_pair_raw_data_item p) l;
    list_for_all_ext (holds_on_pair_raw_data_item p) (holds_on_pair (holds_on_raw_data_item p)) l (fun _ -> ())
  | _ -> ()

let rec raw_data_item_size
  (x: raw_data_item)
: Tot nat
= match x with
  | Array _ v -> 2 + wf_list_sum v raw_data_item_size
  | Map _ v -> 2 + wf_list_sum v raw_data_item_pair_size
  | Tagged _ v -> 2 + raw_data_item_size v
  | _ -> 1

and raw_data_item_pair_size
  (x: (raw_data_item & raw_data_item))
: Tot nat
= raw_data_item_size (fst x) + raw_data_item_size (snd x)

let raw_data_item_pair_size_eq
  (x: (raw_data_item & raw_data_item))
: Lemma
  (raw_data_item_pair_size x == pair_sum raw_data_item_size raw_data_item_size x)
= ()

let raw_data_item_size_eq
  (x: raw_data_item)
: Lemma
  (raw_data_item_size x == begin match x with
  | Array _ v -> 2 + list_sum raw_data_item_size v
  | Map _ v -> 2 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v
  | Tagged _ v -> 2 + raw_data_item_size v
  | _ -> 1
  end)
= match x with
  | Array len v ->
    assert_norm (raw_data_item_size (Array len v) == 2 + wf_list_sum v raw_data_item_size);
    wf_list_sum_eq raw_data_item_size v
  | Map len v ->
    assert_norm (raw_data_item_size (Map len v) == 2 + wf_list_sum v raw_data_item_pair_size);
    wf_list_sum_eq raw_data_item_pair_size v;
    list_sum_ext raw_data_item_pair_size (pair_sum raw_data_item_size raw_data_item_size) v (fun _ -> ())
  | _ -> ()

let rec raw_data_item_fmap
  (f: raw_data_item -> raw_data_item)
  (x: raw_data_item)
: Tot raw_data_item
= match x with
  | Map len v ->
    f (Map len (wf_list_map v (raw_data_item_pair_fmap f)))
  | Array len v -> f (Array len (wf_list_map v (raw_data_item_fmap f)))
  | Tagged tag v -> f (Tagged tag (raw_data_item_fmap f v))
  | _ -> f x

and raw_data_item_pair_fmap
  (f: raw_data_item -> raw_data_item)
  (x: (raw_data_item & raw_data_item))
: Tot (raw_data_item & raw_data_item)
= raw_data_item_fmap f (fst x), raw_data_item_fmap f (snd x)

let raw_data_item_fmap_eq
  f x
= match x with
  | Map len v ->
    assert_norm (raw_data_item_fmap f (Map len v) == f (Map len (wf_list_map v (raw_data_item_pair_fmap f))));
    wf_list_map_eq (raw_data_item_pair_fmap f) v;
    list_map_ext (raw_data_item_pair_fmap f) (apply_on_pair (raw_data_item_fmap f)) v (fun _ -> ());
    ()
  | Array len v ->
    assert_norm (raw_data_item_fmap f (Array len v) == f (Array len (wf_list_map v (raw_data_item_fmap f))));
    wf_list_map_eq (raw_data_item_fmap f) v
  | _ -> ()

#push-options "--z3rlimit 32"

#restart-solver
let rec holds_on_raw_data_item_fmap_gen
  f p q prf1 prf x
= let x' = raw_data_item_fmap f x in
  raw_data_item_fmap_eq f x;
  holds_on_raw_data_item_eq p x;
  match x with
  | Tagged tag v ->
    holds_on_raw_data_item_fmap_gen f p q prf1 prf v; 
    prf1 x;
    let x_ = Tagged tag (raw_data_item_fmap f v) in
    pre_holds_on_raw_data_item_implies (p `andp` q) p x_ (fun _ -> ());
    pre_holds_on_raw_data_item_implies (p `andp` q) q x_ (fun _ -> ());
    holds_on_raw_data_item_eq p x_;
    prf x_
  | Array len v ->
    list_for_all_map (raw_data_item_fmap f) v (holds_on_raw_data_item p) (holds_on_raw_data_item (p `andp` q)) (fun x ->
      holds_on_raw_data_item_fmap_gen f p q prf1 prf x
    );
    prf1 x;
    let x_ = Array len (List.Tot.map (raw_data_item_fmap f) v) in
    pre_holds_on_raw_data_item_implies (p `andp` q) p x_ (fun _ -> ());
    pre_holds_on_raw_data_item_implies (p `andp` q) q x_ (fun _ -> ());
    holds_on_raw_data_item_eq p x_;
    prf x_
  | Map len v ->
    list_for_all_map (apply_on_pair (raw_data_item_fmap f)) v (holds_on_pair (holds_on_raw_data_item p)) (holds_on_pair (holds_on_raw_data_item (p `andp` q))) (fun x ->
      holds_on_raw_data_item_fmap_gen f p q prf1 prf (fst x);
      holds_on_raw_data_item_fmap_gen f p q prf1 prf (snd x)
    );
    prf1 x;
    let x_ = Map len (List.Tot.map (apply_on_pair (raw_data_item_fmap f)) v) in
    pre_holds_on_raw_data_item_implies (p `andp` q) p x_ (fun _ -> ());
    pre_holds_on_raw_data_item_implies (p `andp` q) q x_ (fun _ -> ());
    holds_on_raw_data_item_eq p x_;
    prf x_
  | _ ->
    prf1 x;
    prf x

#pop-options
