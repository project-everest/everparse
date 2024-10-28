module CBOR.Spec.API.Type

module R = CBOR.Spec.Raw.Sort

let cbor_bool (x: R.raw_data_item) : Tot bool =
  R.raw_data_item_ints_optimal x &&
  R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order x

let cbor_prop (x: R.raw_data_item) : Tot prop =
  cbor_bool x == true

let cbor = (x: R.raw_data_item { cbor_prop x })

unfold
let cbor_map_prop (x: list (R.raw_data_item & R.raw_data_item)) : Tot prop =
  List.Tot.for_all (U.holds_on_pair R.raw_data_item_ints_optimal) x == true /\
  List.Tot.for_all (U.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) x == true /\
  List.Tot.sorted (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) x

let cbor_map = (x: list (R.raw_data_item & R.raw_data_item) { cbor_map_prop x })

let list_assoc_cbor
  (m: cbor_map)
  (k: R.raw_data_item)
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
    list_assoc_cbor m k;
    Some v

let cbor_map_get_precedes m k =
  match List.Tot.assoc k m with
  | None -> ()
  | Some v ->
    CBOR.Spec.Util.list_assoc_mem_intro k v m;
    List.Tot.memP_precedes (k, v) m

let cbor_map_ext m1 m2 =
  let prf () : Lemma
    (requires (cbor_map_equal m1 m2))
    (ensures (m1 == m2))
  =
    R.deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 (fun k ->
      match List.Tot.assoc k m1, List.Tot.assoc k m2 with
      | Some v, _ ->
        list_assoc_cbor m1 k;
        assert (cbor_map_get m1 k == cbor_map_get m2 k)
      | _, Some v ->
        list_assoc_cbor m2 k;
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
        U.list_sorted_memP (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) kv q (a, v')
      end
      else ()
    in
    1 + cbor_map_length q

let rec cbor_map_length_eq
  (m: cbor_map)
: Lemma
  (cbor_map_length m == List.Tot.length m)
= match m with
  | [] -> ()
  | _ :: q -> cbor_map_length_eq q

let cbor_map_empty = []

let cbor_map_get_empty _ = ()

let cbor_map_singleton k v = [k, v]

let cbor_map_get_singleton k v k' = ()

let cbor_map_filter_f
  (f: (cbor & cbor) -> bool)
  (x: (R.raw_data_item & R.raw_data_item))
: Tot bool =
    if cbor_bool (fst x) && cbor_bool (snd x)
    then f (fst x, snd x)
    else false

let cbor_map_filter f m =
  U.list_sorted_filter (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) (cbor_map_filter_f f) m;
  List.Tot.filter (cbor_map_filter_f f) m

let rec cbor_map_get_filter'
  (f: (cbor & cbor -> bool))
  (m: cbor_map)
  (k: cbor)
: Lemma
  (ensures (cbor_map_get (cbor_map_filter f m) k == begin match cbor_map_get m k with
  | None -> None
  | Some v -> if f (k, v) then Some v else None
  end))
  (decreases m)
= match m with
  | [] -> ()
  | (a, v) :: q ->
    if k = a
    then begin
      if f (k, v)
      then ()
      else begin
        match cbor_map_get (cbor_map_filter f q) k with
        | None -> ()
        | Some v' ->
          List.Tot.assoc_memP_some a v' (cbor_map_filter f q);
          U.list_sorted_memP (R.map_entry_order R.deterministically_encoded_cbor_map_key_order _) (a, v) q (a, v')
      end
    end
    else cbor_map_get_filter' f q k

let cbor_map_get_filter = cbor_map_get_filter'

let cbor_map_diff_f (m1: cbor_map) (kv: (cbor & cbor)) : Tot bool =
  None? (cbor_map_get m1 (fst kv))

let cbor_map_union m1 m2 =
  let m2' = cbor_map_filter (cbor_map_diff_f m1) m2 in
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) m1;
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) m2';
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) m1;
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) m2';
  Classical.forall_intro (List.Tot.append_memP m1 m2');
  let m' = m1 `List.Tot.append` m2' in
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats R.deterministically_encoded_cbor_map_key_order m1;
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats R.deterministically_encoded_cbor_map_key_order m2';
  assert (List.Tot.no_repeats_p (List.Tot.map fst m1));
  assert (List.Tot.no_repeats_p (List.Tot.map fst m2'));
  let prf
    (x: R.raw_data_item)
  : Lemma
    (requires (List.Tot.memP x (List.Tot.map fst m1)))
    (ensures (~ (List.Tot.memP x (List.Tot.map fst m2'))))
  = List.Tot.assoc_mem x m1;
    List.Tot.assoc_mem x m2';
    if Some? (List.Tot.assoc x m2')
    then begin
      list_assoc_cbor m2' x;
      cbor_map_get_filter (cbor_map_diff_f m1) m2' x
    end
  in
  Classical.forall_intro (Classical.move_requires prf);
  List.Tot.no_repeats_p_append (List.Tot.map fst m1) (List.Tot.map fst m2');
  List.Tot.map_append fst m1 m2';
  let res = R.cbor_map_sort_failsafe m' in
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) res;
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) res;
  res

let cbor_map_get_union m1 m2 k =
  let m2' = cbor_map_filter (cbor_map_diff_f m1) m2 in
  R.cbor_map_sort_failsafe_correct (List.Tot.append m1 m2');
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats R.deterministically_encoded_cbor_map_key_order (cbor_map_union m1 m2);
  U.list_assoc_append k m1 m2';
  cbor_map_get_filter (cbor_map_diff_f m1) m2 k

let cast_to_cbor (x: R.raw_data_item) : Tot cbor =
  if cbor_bool x
  then x
  else R.Simple 0uy // dummy

let list_cbor_of_cbor_list
  (l: list R.raw_data_item)
: Tot (list cbor)
= List.Tot.map cast_to_cbor l

// let cbor_map_key_list_raw (m: cbor_map) : Tot (list R.raw_data_item) = List.Tot.map fst m

let rec cbor_map_key_list_tot (m: cbor_map) : Tot (list cbor) =
  match m with
  | [] -> []
  | (k, _) :: q -> k :: cbor_map_key_list_tot q

let cbor_map_key_list (m: cbor_map) : GTot (list cbor) =
  cbor_map_key_list_tot m

let rec cbor_map_key_list_mem_aux (m: cbor_map) (k: cbor) : Lemma
  (List.Tot.memP k (cbor_map_key_list m) <==> List.Tot.memP k (List.Tot.map fst m))
= match m with
  | [] -> ()
  | (k', _) :: q ->
    if k = k' then () else cbor_map_key_list_mem_aux q k

let cbor_map_key_list_mem (m: cbor_map) (k: cbor) : Lemma
  (List.Tot.memP k (cbor_map_key_list m) <==> cbor_map_defined k m)
= cbor_map_key_list_mem_aux m k;
  List.Tot.assoc_mem k m;
  List.Tot.mem_memP k (List.Tot.map fst m)

let rec cbor_map_key_list_no_repeats_p (m: cbor_map) : Lemma
  (List.Tot.no_repeats_p (cbor_map_key_list m))
= CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats R.deterministically_encoded_cbor_map_key_order m;
  match m with
  | [] -> ()
  | (k, _) :: q ->
    cbor_map_key_list_mem_aux q k;
    cbor_map_key_list_no_repeats_p q

let rec cbor_map_key_list_length (m: cbor_map) : Lemma
  (List.Tot.length (cbor_map_key_list m) == cbor_map_length m)
= match m with
  | [] -> ()
  | _ :: q -> cbor_map_key_list_length q

let cbor_map_fold
  (#a: Type)
  (f: a -> cbor -> a)
  (x: a)
  (m: cbor_map)
: Tot a
= List.Tot.fold_left f x (cbor_map_key_list_tot m)

let rec list_sorted_map_entry_order
  (#key #value: Type)
  (f: key -> key -> bool {
    U.order_irrefl f /\
    U.order_trans f
  })
  (l: list (key & value))
: Lemma
  (requires (List.Tot.sorted (R.map_entry_order f value) l))
  (ensures (List.Tot.sorted f (List.Tot.map fst l)))
= match l with
  | [] -> ()
  | a :: q -> list_sorted_map_entry_order f q

let rec cbor_map_key_list_sorted
  (m: cbor_map)
: Lemma
  (List.Tot.sorted R.deterministically_encoded_cbor_map_key_order (cbor_map_key_list m))
= list_sorted_map_entry_order R.deterministically_encoded_cbor_map_key_order m;
  match m with
  | [] -> ()
  | a :: q ->
    cbor_map_key_list_sorted q

let cbor_map_fold_ext
  (#a: Type)
  (f1 f2: a -> cbor -> a)
  (x: a)
  (m1 m2: cbor_map)
= let l1 = cbor_map_key_list m1 in
  cbor_map_key_list_sorted m1;
  cbor_map_key_list_sorted m2;  
  U.list_sorted_ext_eq R.deterministically_encoded_cbor_map_key_order l1 (cbor_map_key_list m2);
  U.list_fold_ext f1 f2 x l1

let cbor_map_fold_eq
  (#a: Type)
  (f: a -> cbor -> a)
  (x: a)
  (m: cbor_map)
  (l: list cbor)
: Lemma
  (requires (
    U.op_comm f /\
    (forall (x: cbor) . List.Tot.memP x l <==> cbor_map_defined x m) /\
    List.Tot.no_repeats_p l
  ))
  (ensures (
    cbor_map_fold f x m == List.Tot.fold_left f x l
  ))
= cbor_map_key_list_no_repeats_p m;
  U.list_fold_ext_no_repeats_p f x (cbor_map_key_list m) l

let rec cbor_list_of_list_cbor_precedes (l: list R.raw_data_item {
    List.Tot.for_all (R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem) l /\
    List.Tot.for_all (R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order)) l
  }) (x: cbor) : Lemma
  (requires (
    List.Tot.memP x (list_cbor_of_cbor_list l)
  ))
  (ensures (x << l))
= let a :: q = l in
  if a = x
  then ()
  else (
    assert (q << l);
    cbor_list_of_list_cbor_precedes q x
  )

let unpack m =
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order));
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem m;
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order) m;
  match m with
  | R.Simple v -> CSimple v
  | R.Int64 ty v -> CInt64 ty v.value
  | R.String ty len v -> CString ty v
  | R.Array len v -> CArray (list_cbor_of_cbor_list v)
  | R.Map len v ->
    cbor_map_length_eq v;
    CMap v
  | R.Tagged tag v -> CTagged tag.value v

let cast_from_cbor (x: cbor) : Tot R.raw_data_item = x

let cbor_list_of_list_cbor (l: list cbor) : Tot (list R.raw_data_item) =
  List.Tot.map cast_from_cbor l

let cbor_list_of_list_cbor_correct
  (l: list cbor)
: Lemma
  (ensures (let l' = cbor_list_of_list_cbor l in
   List.Tot.for_all (R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem) l' == true /\
   List.Tot.for_all (R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order)) l' == true
  ))
  [SMTPat (cbor_list_of_list_cbor l)]
= U.list_for_all_truep l;
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order));
  U.list_for_all_map cast_from_cbor l U.truep R.raw_data_item_ints_optimal (fun _ -> ());
  U.list_for_all_map cast_from_cbor l U.truep (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)  (fun _ -> ())

let pack x =
  let m : R.raw_data_item = match x with
  | CSimple v -> R.Simple v
  | CInt64 ty v -> R.Int64 ty (R.mk_raw_uint64 v)
  | CString ty v -> R.String ty (R.mk_raw_uint64 (U64.uint_to_t (Seq.length v))) v
  | CArray v -> R.Array (R.mk_raw_uint64 (U64.uint_to_t (List.Tot.length v))) (cbor_list_of_list_cbor v)
  | CMap v ->
    cbor_map_length_eq v;
    R.Map (R.mk_raw_uint64 (U64.uint_to_t (List.Tot.length v))) v
  | CTagged tag v -> R.Tagged (R.mk_raw_uint64 tag) v
  in
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order));
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem m;
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order) m;
  m

let rec cbor_list_of_list_cbor_of_cbor_list
  (l: list R.raw_data_item {
    List.Tot.for_all (R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem) l == true /\
    List.Tot.for_all (R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order)) l == true
  })
: Lemma
  (cbor_list_of_list_cbor (list_cbor_of_cbor_list l) == l)
= match l with
  | [] -> ()
  | _ :: q -> cbor_list_of_list_cbor_of_cbor_list q

let rec list_cbor_of_cbor_list_of_list_cbor
  (l: list cbor)
: Lemma
  (list_cbor_of_cbor_list (cbor_list_of_list_cbor l) == l)
= match l with
  | [] -> ()
  | _ :: q -> list_cbor_of_cbor_list_of_list_cbor q

let unpack_pack c = match c with
  | CArray v -> list_cbor_of_cbor_list_of_list_cbor v
  | _ -> ()

let pack_unpack c = match c with
  | R.Simple _ -> ()
  | R.Int64 _ v
  | R.Tagged v _
  | R.Map v _
  | R.String _ v _ -> R.raw_uint64_optimal_unique v (R.mk_raw_uint64 v.value)
  | R.Array len v ->
    R.raw_uint64_optimal_unique len (R.mk_raw_uint64 len.value);
    cbor_list_of_list_cbor_of_cbor_list v

let unpack_precedes c =
  match c with
  | R.Array _ v ->
    Classical.forall_intro (Classical.move_requires (cbor_list_of_list_cbor_precedes v))
  | _ -> ()
