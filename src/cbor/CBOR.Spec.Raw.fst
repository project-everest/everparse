module CBOR.Spec.Raw

let rec raw_equiv (l1 l2: raw_data_item) : Tot bool (decreases l1) =
  match l1, l2 with
  | Simple v1, Simple v2 -> v1 = v2
  | Int64 ty1 v1, Int64 ty2 v2 -> ty1 = ty2 && raw_uint64_equiv v1 v2
  | String ty1 len1 v1, String ty2 len2 v2 -> ty1 = ty2 && raw_uint64_equiv len1 len2 && v1 = v2
  | Array len1 v1, Array len2 v2 -> raw_uint64_equiv len1 len2 && wf_list_for_all2 v1 v2 raw_equiv
  | Map len1 v1, Map len2 v2 ->
    raw_uint64_equiv len1 len2 &&
    wf_list_for_all_exists v1 v2 raw_pair_equiv &&
    wf_list_for_all_exists v2 v1 raw_pair_equiv_swap
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_equiv tag1 tag2 &&
    raw_equiv v1 v2
  | _ -> false

and raw_pair_equiv (l1 l2: (raw_data_item & raw_data_item)) : Tot bool (decreases l1) =
  raw_equiv (fst l1) (fst l2) && raw_equiv (snd l1) (snd l2)

and raw_pair_equiv_swap (l2 l1: (raw_data_item & raw_data_item)) : Tot bool (decreases l1) =
  raw_equiv (fst l1) (fst l2) && raw_equiv (snd l1) (snd l2)

let rec raw_equiv_eq' (l1 l2: raw_data_item) : Lemma (ensures
  raw_equiv l1 l2 == begin match l1, l2 with
  | Simple v1, Simple v2 -> v1 = v2
  | Int64 ty1 v1, Int64 ty2 v2 -> ty1 = ty2 && raw_uint64_equiv v1 v2
  | String ty1 len1 v1, String ty2 len2 v2 -> ty1 = ty2 && raw_uint64_equiv len1 len2 && v1 = v2
  | Array len1 v1, Array len2 v2 -> raw_uint64_equiv len1 len2 && list_for_all2 raw_equiv v1 v2
  | Map len1 v1, Map len2 v2 ->
    raw_uint64_equiv len1 len2 &&
    list_for_all_exists (holds_on_pair2 raw_equiv) v1 v2 &&
    list_for_all_exists (holds_on_pair2 raw_equiv) v2 v1
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_equiv tag1 tag2 &&
    raw_equiv v1 v2
  | _ -> false
  end /\
  (raw_equiv l1 l2 == raw_equiv l2 l1)
)
(decreases l1)
= match l1, l2 with
  | Array len1 v1, Array len2 v2 ->
    assert_norm (raw_equiv (Array len1 v1) (Array len2 v2) == (raw_uint64_equiv len1 len2 && wf_list_for_all2 v1 v2 raw_equiv));
    assert_norm (raw_equiv (Array len2 v2) (Array len1 v1) == (raw_uint64_equiv len2 len1 && wf_list_for_all2 v2 v1 raw_equiv));
    wf_list_for_all2_eq raw_equiv v1 v2;
    wf_list_for_all2_eq raw_equiv v2 v1;
    list_for_all2_ext raw_equiv (swap raw_equiv) v1 v2 (fun x1 x2 ->
      raw_equiv_eq' x1 x2
    );
    list_for_all2_swap raw_equiv v2 v1;
    assert (list_for_all2 raw_equiv v1 v2 == list_for_all2 raw_equiv v2 v1)
  | Map len1 v1, Map len2 v2 ->
    assert_norm (raw_equiv (Map len1 v1) (Map len2 v2) == (
      raw_uint64_equiv len1 len2 &&
      wf_list_for_all_exists v1 v2 raw_pair_equiv &&
      wf_list_for_all_exists v2 v1 raw_pair_equiv_swap
    ));
    assert_norm (raw_equiv (Map len2 v2) (Map len1 v1) == (
      raw_uint64_equiv len2 len1 &&
      wf_list_for_all_exists v2 v1 raw_pair_equiv &&
      wf_list_for_all_exists v1 v2 raw_pair_equiv_swap
    ));
    wf_list_for_all_exists_eq raw_pair_equiv v1 v2;
    list_for_all_exists_ext raw_pair_equiv (holds_on_pair2 raw_equiv) v1 v2 (fun _ _ -> ());
    wf_list_for_all_exists_eq raw_pair_equiv_swap v2 v1;
    list_for_all_exists_ext raw_pair_equiv_swap (holds_on_pair2 raw_equiv) v2 v1 (fun x2 x1 ->
      raw_equiv_eq' (fst x1) (fst x2);
      raw_equiv_eq' (snd x1) (snd x2)
    );
    wf_list_for_all_exists_eq raw_pair_equiv v2 v1;
    list_for_all_exists_ext raw_pair_equiv (holds_on_pair2 raw_equiv) v2 v1 (fun _ _ -> ());
    wf_list_for_all_exists_eq raw_pair_equiv_swap v1 v2;
    list_for_all_exists_ext raw_pair_equiv_swap (holds_on_pair2 raw_equiv) v1 v2 (fun x1 x2 ->
      raw_equiv_eq' (fst x1) (fst x2);
      raw_equiv_eq' (snd x1) (snd x2)
    )
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_equiv_eq' v1 v2
  | _ -> ()

let raw_equiv_eq l1 l2 = raw_equiv_eq' l1 l2

let raw_equiv_sym l1 l2 = raw_equiv_eq' l1 l2
