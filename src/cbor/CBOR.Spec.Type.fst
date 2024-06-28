module CBOR.Spec.Type

module R = CBOR.Spec.Raw.Sort
module U = CBOR.Spec.Util

let cbor_bool (x: R.raw_data_item) : Tot bool =
  R.raw_data_item_ints_optimal x &&
  R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order x

let cbor_prop (x: R.raw_data_item) : Tot prop =
  cbor_bool x == true

let cbor = (x: R.raw_data_item { cbor_prop x })

let cbor_map_prop (x: list (R.raw_data_item & R.raw_data_item)) : Tot prop =
  List.Tot.for_all (U.holds_on_pair R.raw_data_item_ints_optimal) x == true /\
  List.Tot.for_all (U.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) x == true /\
  List.Tot.sorted (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) x

let cbor_map = (x: list (R.raw_data_item & R.raw_data_item) { cbor_map_prop x })

let list_assoc_cbor
  (k: R.raw_data_item)
  (m: cbor_map)
: Lemma
  (requires (Some? (List.Tot.assoc k m)))
  (ensures (match List.Tot.assoc k m with
  | None -> False
  | Some v ->
    cbor_prop k /\ cbor_prop v
  ))
= let Some v = List.Tot.assoc k m in
  List.Tot.assoc_memP_some k v m;
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) m;
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) m

let cbor_map_get m k =
  match List.Tot.assoc k m with
  | None -> None
  | Some v ->
    list_assoc_cbor k m;
    Some v

let cbor_map_ext m1 m2 =
  let prf () : Lemma
    (requires (cbor_map_equal m1 m2))
    (ensures (m1 == m2))
  =
    R.deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 (fun k ->
      match List.Tot.assoc k m1, List.Tot.assoc k m2 with
      | Some v, _ ->
        list_assoc_cbor k m1;
        assert (cbor_map_get m1 k == cbor_map_get m2 k)
      | _, Some v ->
        list_assoc_cbor k m2;
        assert (cbor_map_get m1 k == cbor_map_get m2 k)
      | _ -> ()
    )
  in
  Classical.move_requires prf ()

let rec cbor_map_set_keys m =
  match m with
  | [] -> FS.emptyset
  | (a, _) :: q -> FS.union (FS.singleton a) (cbor_map_set_keys q)

let rec cbor_map_set_keys_mem m k =
  match m with
  | [] -> ()
  | (a, _) :: q ->
    if k = a
    then ()
    else cbor_map_set_keys_mem q k

let rec cbor_map_length m =
  match m with
  | [] -> 0
  | kv :: q ->
    let (a, _) = kv in
    let s' = cbor_map_set_keys q in
    let prf : squash (FS.mem a s' == false) =
      if FS.mem a s'
      then begin
        let Some v' = List.Tot.assoc a q in
        List.Tot.assoc_memP_some a v' q;
        CBOR.Spec.Util.list_sorted_memP (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) kv q (a, v')
      end
      else ()
    in
    1 + cbor_map_length q

let cbor_map_empty = []

let cbor_map_get_empty _ = ()

let cbor_map_singleton k v = [k, v]

let cbor_map_get_singleton k v k' = ()

let rec list_for_all_filter_invariant
  (#t: Type)
  (p: t -> bool)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.for_all p l == true))
  (ensures (List.Tot.for_all p (List.Tot.filter f l) == true))
  [SMTPat (List.Tot.for_all p (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_filter_invariant p f q

let rec list_sorted_filter
  (#t1: Type)
  (key_order: t1 -> t1 -> bool {
    forall x y z . (key_order x y /\ key_order y z) ==> key_order x z
  })
  (f: t1 -> bool)
  (l: list t1)
: Lemma
  (requires (
    List.Tot.sorted key_order l
  ))
  (ensures (
    List.Tot.sorted key_order (List.Tot.filter f l)
  ))
= match l with
  | [] -> ()
  | a :: q ->
    list_sorted_filter key_order f q;
    if f a
    then begin
      CBOR.Spec.Raw.Map.list_sorted_cons_elim key_order a q;
      list_for_all_filter_invariant (key_order a) f q
    end
    else ()

let cbor_map_filter_f
  (f: cbor -> cbor -> bool)
  (x: (R.raw_data_item & R.raw_data_item))
: Tot bool =
    if cbor_bool (fst x) && cbor_bool (snd x)
    then f (fst x) (snd x)
    else false

let cbor_map_filter f m =
  list_sorted_filter (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) (cbor_map_filter_f f) m;
  List.Tot.filter (cbor_map_filter_f f) m

let rec cbor_map_get_filter'
  (f: (cbor -> cbor -> bool))
  (m: cbor_map)
  (k: cbor)
: Lemma
  (ensures (cbor_map_get (cbor_map_filter f m) k == begin match cbor_map_get m k with
  | None -> None
  | Some v -> if f k v then Some v else None
  end))
  (decreases m)
= match m with
  | [] -> ()
  | (a, v) :: q ->
    if k = a
    then begin
      if f k v
      then ()
      else begin
        match cbor_map_get (cbor_map_filter f q) k with
        | None -> ()
        | Some v' ->
          admit ();
          List.Tot.assoc_memP_some a v' q;
          CBOR.Spec.Util.list_sorted_memP (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) (a, v) q (a, v')
      end
    end
    else cbor_map_get_filter' f q k

let cbor_map_get_filter = cbor_map_get_filter'
