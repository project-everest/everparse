module CBOR.Spec.Raw.DataModel

module R = CBOR.Spec.Raw.Sort

let cbor_bool
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    R.compare_prop order compare
  })
  (x: R.raw_data_item)
: Tot bool =
  R.raw_data_item_ints_optimal x &&
  R.raw_data_item_sorted order x

let cbor_prop order compare (x: R.raw_data_item) : Tot prop =
  cbor_bool order compare x == true

let cbor order compare = (x: R.raw_data_item { cbor_prop order compare x })

unfold
let cbor_map_prop order
  (compare: raw_data_item -> raw_data_item -> int {
    R.compare_prop order compare
  })
  (x: list (R.raw_data_item & R.raw_data_item)) : Tot prop =
  List.Tot.for_all (U.holds_on_pair R.raw_data_item_ints_optimal) x == true /\
  List.Tot.for_all (U.holds_on_pair (R.raw_data_item_sorted order)) x == true /\
  List.Tot.sorted (R.map_entry_order order _) x

let cbor_map order compare = (x: list (R.raw_data_item & R.raw_data_item) { cbor_map_prop order compare x })

let list_assoc_cbor
  #order #compare
  (m: cbor_map order compare)
  (k: R.raw_data_item)
: Lemma
  (requires (Some? (List.Tot.assoc k m)))
  (ensures (match List.Tot.assoc k m with
  | None -> False
  | Some v ->
    cbor_prop order compare k /\ cbor_prop order compare v
  ))
= let Some v = List.Tot.assoc k m in
  List.Tot.assoc_memP_some k v m;
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) m;
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted order)) m

let cbor_map_get #order #compare m k =
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

let cbor_map_ext #order #compare m1 m2 =
  let prf () : Lemma
    (requires (cbor_map_equal m1 m2))
    (ensures (m1 == m2))
  =
    let prf'
      (k: raw_data_item)
    : Lemma
      (List.Tot.assoc k m1 == List.Tot.assoc k m2)
    =
      match List.Tot.assoc k m1, List.Tot.assoc k m2 with
      | Some v, _ ->
        list_assoc_cbor m1 k;
        assert (cbor_map_get m1 k == cbor_map_get m2 k)
      | _, Some v ->
        list_assoc_cbor m2 k;
        assert (cbor_map_get m1 k == cbor_map_get m2 k)
      | _ -> ()
    in
    Classical.forall_intro prf';
    CBOR.Spec.Raw.Map.list_sorted_map_assoc_ext order m1 m2
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

let rec cbor_map_length #order #compare m =
  match m with
  | [] -> 0
  | kv :: q ->
    let (a, _) = kv in
    let s' = cbor_map_set_keys #order #compare q in
    let prf : squash (FS.mem a s' == false) =
      if FS.mem a s'
      then begin
        let Some v' = List.Tot.assoc a q in
        List.Tot.assoc_memP_some a v' q;
        U.list_sorted_memP (R.map_entry_order order _) kv q (a, v')
      end
      else ()
    in
    1 + cbor_map_length #order #compare q

let rec cbor_map_length_eq
  #order #compare
  (m: cbor_map order compare)
: Lemma
  (cbor_map_length m == List.Tot.length m)
= match m with
  | [] -> ()
  | _ :: q -> cbor_map_length_eq #order #compare q

let cbor_map_empty #order #compare = []

let cbor_map_get_empty _ = ()

let cbor_map_singleton k v = [k, v]

let cbor_map_get_singleton k v k' = ()

let cbor_map_filter_f
  #order #compare
  (f: (cbor order compare & cbor order compare) -> bool)
  (x: (R.raw_data_item & R.raw_data_item))
: Tot bool =
    if cbor_bool order compare (fst x) && cbor_bool order compare (snd x)
    then f (fst x, snd x)
    else false

let cbor_map_filter #order  f m =
  U.list_sorted_filter (R.map_entry_order order _) (cbor_map_filter_f f) m;
  List.Tot.filter (cbor_map_filter_f f) m

let rec cbor_map_get_filter'
  #order #compare
  (f: (cbor order compare & cbor order compare -> bool))
  (m: cbor_map order compare)
  (k: cbor order compare)
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
          U.list_sorted_memP (R.map_entry_order order _) (a, v) q (a, v')
      end
    end
    else cbor_map_get_filter' f q k

let cbor_map_get_filter = cbor_map_get_filter'

let cbor_map_diff_f #order #compare (m1: cbor_map order compare) (kv: (cbor order compare & cbor order compare)) : Tot bool =
  None? (cbor_map_get m1 (fst kv))

let cbor_map_length_filter f m =
  cbor_map_length_eq m;
  cbor_map_length_eq (cbor_map_filter f m);
  U.list_length_filter (cbor_map_filter_f f) m

let cbor_map_union #order #compare m1 m2 =
  let m2' = cbor_map_filter (cbor_map_diff_f m1) m2 in
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) m1;
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) m2';
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted order)) m1;
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted order)) m2';
  Classical.forall_intro (List.Tot.append_memP m1 m2');
  let m' = m1 `List.Tot.append` m2' in
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats order m1;
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats order m2';
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
  let res = R.cbor_map_sort_failsafe order m' in
  R.cbor_map_sort_failsafe_correct order compare m';
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) res;
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted order)) res;
  res

let cbor_map_get_union #order #compare m1 m2 k =
  let m2' = cbor_map_filter (cbor_map_diff_f m1) m2 in
  R.cbor_map_sort_failsafe_correct order compare (List.Tot.append m1 m2');
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats order (cbor_map_union m1 m2);
  U.list_assoc_append k m1 m2';
  cbor_map_get_filter (cbor_map_diff_f m1) m2 k

let cast_to_cbor
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    R.compare_prop order compare
  })
  (x: R.raw_data_item) : Tot (cbor order compare) =
  if cbor_bool order compare x
  then x
  else R.Simple 0uy // dummy

let list_cbor_of_cbor_list
  #order #compare
  (l: list R.raw_data_item)
: Tot (list (cbor order compare))
= List.Tot.map (cast_to_cbor order compare) l

// let cbor_map_key_list_raw (m: cbor_map) : Tot (list R.raw_data_item) = List.Tot.map fst m

let rec cbor_map_key_list_tot #order #compare (m: cbor_map order compare) : Tot (list (cbor order compare)) =
  match m with
  | [] -> []
  | (k, _) :: q -> k :: cbor_map_key_list_tot q

let cbor_map_key_list #order #compare (m: cbor_map order compare) : GTot (list (cbor order compare)) =
  cbor_map_key_list_tot m

let rec cbor_map_key_list_mem_aux #order #compare (m: cbor_map order compare) (k: cbor order compare) : Lemma
  (List.Tot.memP k (cbor_map_key_list m) <==> List.Tot.memP k (List.Tot.map fst m))
= match m with
  | [] -> ()
  | (k', _) :: q ->
    if k = k' then () else cbor_map_key_list_mem_aux q k

let cbor_map_key_list_mem #order #compare (m: cbor_map order compare) (k: cbor order compare) : Lemma
  (List.Tot.memP k (cbor_map_key_list m) <==> cbor_map_defined k m)
= cbor_map_key_list_mem_aux m k;
  List.Tot.assoc_mem k m;
  List.Tot.mem_memP k (List.Tot.map fst m)

let rec cbor_map_key_list_no_repeats_p #order #compare (m: cbor_map order compare) : Lemma
  (List.Tot.no_repeats_p (cbor_map_key_list m))
= CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats order m;
  match m with
  | [] -> ()
  | (k, _) :: q ->
    cbor_map_key_list_mem_aux #order #compare q k;
    cbor_map_key_list_no_repeats_p #order #compare q

let rec cbor_map_key_list_length #order #compare (m: cbor_map order compare) : Lemma
  (List.Tot.length (cbor_map_key_list m) == cbor_map_length m)
= match m with
  | [] -> ()
  | _ :: q -> cbor_map_key_list_length #order #compare q

let cbor_map_fold
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a)
  (x: a)
  (m: cbor_map order compare)
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
  #order #compare
  (m: cbor_map order compare)
: Lemma
  (List.Tot.sorted order (cbor_map_key_list m))
= list_sorted_map_entry_order order m;
  match m with
  | [] -> ()
  | a :: q ->
    cbor_map_key_list_sorted #order #compare q

let cbor_map_fold_ext
  #order #compare
  (#a: Type)
  (f1 f2: a -> cbor order compare -> a)
  (x: a)
  (m1 m2: cbor_map order compare)
= let l1 = cbor_map_key_list m1 in
  cbor_map_key_list_sorted m1;
  cbor_map_key_list_sorted m2;  
  U.list_sorted_ext_eq order l1 (cbor_map_key_list m2);
  U.list_fold_ext f1 f2 x l1

let cbor_map_fold_eq
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a)
  (x: a)
  (m: cbor_map order compare)
  (l: list (cbor order compare))
: Lemma
  (requires (
    U.op_comm f /\
    (forall (x: cbor order compare) . List.Tot.memP x l <==> cbor_map_defined x m) /\
    List.Tot.no_repeats_p l
  ))
  (ensures (
    cbor_map_fold f x m == List.Tot.fold_left f x l
  ))
= cbor_map_key_list_no_repeats_p m;
  U.list_fold_ext_no_repeats_p f x (cbor_map_key_list m) l

let cbor_map_fold_eq_idem
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a)
  (x: a)
  (m: cbor_map order compare)
  (l: list (cbor order compare))
= U.list_fold_ext_idem f x (cbor_map_key_list m) l

let rec cbor_list_of_list_cbor_precedes
  #order #compare
  (l: list R.raw_data_item {
    List.Tot.for_all (R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem) l /\
    List.Tot.for_all (R.holds_on_raw_data_item (R.raw_data_item_sorted_elem order)) l
  }) (x: cbor order compare) : Lemma
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

let unpack #order #compare m =
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem order));
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem m;
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem order) m;
  match m with
  | R.Simple v -> CSimple v
  | R.Int64 ty v -> CInt64 ty v.value
  | R.String ty len v -> CString ty v
  | R.Array len v -> CArray (list_cbor_of_cbor_list v)
  | R.Map len v ->
    cbor_map_length_eq #order #compare v;
    CMap v
  | R.Tagged tag v -> CTagged tag.value v

let cast_from_cbor #order #compare (x: cbor order compare) : Tot R.raw_data_item = x

let cbor_list_of_list_cbor #order #compare (l: list (cbor order compare)) : Tot (list R.raw_data_item) =
  List.Tot.map cast_from_cbor l

let cbor_list_of_list_cbor_correct
  #order #compare
  (l: list (cbor order compare))
: Lemma
  (ensures (let l' = cbor_list_of_list_cbor l in
   List.Tot.for_all (R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem) l' == true /\
   List.Tot.for_all (R.holds_on_raw_data_item (R.raw_data_item_sorted_elem order)) l' == true
  ))
  [SMTPat (cbor_list_of_list_cbor l)]
= U.list_for_all_truep l;
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem order));
  U.list_for_all_map cast_from_cbor l U.truep R.raw_data_item_ints_optimal (fun _ -> ());
  U.list_for_all_map cast_from_cbor l U.truep (R.raw_data_item_sorted order)  (fun _ -> ())

let pack #order #compare x =
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
  assert_norm (R.raw_data_item_sorted order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem order));
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem m;
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem order) m;
  m

let rec cbor_list_of_list_cbor_of_cbor_list
  #order #compare
  (l: list R.raw_data_item {
    List.Tot.for_all (R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem) l == true /\
    List.Tot.for_all (R.holds_on_raw_data_item (R.raw_data_item_sorted_elem order)) l == true
  })
: Lemma
  (cbor_list_of_list_cbor #order #compare (list_cbor_of_cbor_list l) == l)
= match l with
  | [] -> ()
  | _ :: q -> cbor_list_of_list_cbor_of_cbor_list #order #compare q

let rec list_cbor_of_cbor_list_of_list_cbor
  #order #compare
  (l: list (cbor order compare))
: Lemma
  (list_cbor_of_cbor_list (cbor_list_of_list_cbor l) == l)
= match l with
  | [] -> ()
  | _ :: q -> list_cbor_of_cbor_list_of_list_cbor q

let unpack_pack c = match c with
  | CArray v -> list_cbor_of_cbor_list_of_list_cbor v
  | _ -> ()

let pack_unpack #order #compare c = match c with
  | R.Simple _ -> ()
  | R.Int64 _ v
  | R.Tagged v _
  | R.Map v _
  | R.String _ v _ -> R.raw_uint64_optimal_unique v (R.mk_raw_uint64 v.value)
  | R.Array len v ->
    R.raw_uint64_optimal_unique len (R.mk_raw_uint64 len.value);
    cbor_list_of_list_cbor_of_cbor_list #order #compare v

let unpack_precedes #order #compare c =
  match c with
  | R.Array _ v ->
    Classical.forall_intro (Classical.move_requires (cbor_list_of_list_cbor_precedes #order #compare v))
  | _ -> ()

let size c = raw_data_item_size c

let cbor_map_mem_mem
  #order #compare 
  (m: cbor_map order compare)
  (kv: (cbor order compare & cbor order compare))
: Lemma
  (requires (cbor_map_mem kv m))
  (ensures (List.Tot.memP (fst kv, snd kv) m))
= CBOR.Spec.Util.list_assoc_mem_intro (fst kv) (snd kv) m

let cbor_map_mem_size
  #order #compare 
  (m: cbor_map order compare)
  (kv: (cbor order compare & cbor order compare))
: Lemma
  (requires (cbor_map_mem kv m))
  (ensures (
    let sz = CBOR.Spec.Util.list_sum (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) m in
    size (fst kv) <= sz /\ size (snd kv) <= sz
  ))
= cbor_map_mem_mem m kv;
  CBOR.Spec.Util.list_sum_memP (CBOR.Spec.Util.pair_sum raw_data_item_size raw_data_item_size) m (fst kv, snd kv)

let rec list_cbor_of_cbor_list_size
  #order #compare
  (l: list R.raw_data_item)
  (x: cbor order compare)
: Lemma
  (requires (
    List.Tot.for_all (R.raw_data_item_ints_optimal) l /\
    List.Tot.for_all (R.raw_data_item_sorted order) l /\
    List.Tot.memP x (list_cbor_of_cbor_list l)
  ))
  (ensures (
    size x <= CBOR.Spec.Util.list_sum raw_data_item_size l
  ))
= let a :: q = l in
  if x = a
  then ()
  else begin
    list_cbor_of_cbor_list_size q x;
    ()
  end

let size_unpack #order #compare x =
  raw_data_item_size_eq x;
  holds_on_raw_data_item_eq (R.raw_data_item_ints_optimal_elem) x;
  holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem order) x;
  match x with
  | Map _ m -> Classical.forall_intro (Classical.move_requires (cbor_map_mem_size #order #compare m));
    ()
  | Array _ v ->
    Classical.forall_intro (Classical.move_requires (list_cbor_of_cbor_list_size #order #compare v));
    ()
  | _ -> ()
