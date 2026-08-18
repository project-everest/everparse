module CBOR.Spec.Raw.EverParse.Assoc
open CBOR.Spec.Raw.Valid
include LowParse.Spec.Combinators
include LowParse.Spec.List
include LowParse.Spec.Sorted

(* Association lists *)

let parse_assoc
  (#kkey: parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (pvalue: parser kvalue tvalue)
: Tot (parser _ (list (tkey & tvalue)))
= parse_list (pkey `nondep_then` pvalue)

let serialize_assoc
  (#kkey: parser_kind)
  (#tkey: Type)
  (#pkey: parser kkey tkey)
  (skey: serializer pkey)
  (#kvalue: parser_kind)
  (#tvalue: Type)
  (#pvalue: parser kvalue tvalue)
  (svalue: serializer pvalue)
: Pure (serializer (parse_assoc pkey pvalue))
    (requires (
      kkey.parser_kind_subkind == Some ParserStrong /\
      kvalue.parser_kind_subkind == Some ParserStrong /\
      kkey.parser_kind_low + kvalue.parser_kind_low > 0
    ))
    (ensures (fun _ -> True))
= serialize_list _ (serialize_nondep_then skey svalue)

let rec list_ghost_assoc
  (#key: Type)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: GTot (option value)
  (decreases m)
= match m with
  | [] -> None
  | (k', v') :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v'
    else list_ghost_assoc k m'

let rec list_ghost_assoc_eq
  (#key: eqtype)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: Lemma
  (ensures (list_ghost_assoc k m == List.Tot.assoc k m))
= match m with
  | [] -> ()
  | (k', v') :: m' ->
    if k = k'
    then ()
    else list_ghost_assoc_eq k m'

let rec map_entry_order_assoc_order_none
  (#key: Type)
  (key_order: (key -> key -> bool))
  (key_order_irrefl: (
    (k1: key) ->
    (k2: key) ->
    Lemma
    (requires (key_order k1 k2))
    (ensures (~ (k1 == k2)))
  ))
  (key_order_trans: (
    (k1: key) ->
    (k2: key) ->
    (k3: key) ->
    Lemma
    (requires (key_order k1 k2 /\ key_order k2 k3))
    (ensures (key_order k1 k3))
  ))
  (#value: Type)
  (k: key)
  (v: value)
  (m: list (key & value))
  (k': key)
: Lemma
  (requires (key_order k' k /\ List.Tot.sorted (map_entry_order key_order _) ((k, v) :: m)))
  (ensures (list_ghost_assoc k' ((k, v) :: m) == None))
  (decreases m)
= key_order_irrefl k' k;
  match m with
  | [] -> ()
  | (k2, v2) :: m2 ->
    key_order_trans k' k k2;
    map_entry_order_assoc_order_none key_order key_order_irrefl key_order_trans k2 v2 m2 k'

let map_entry_order_assoc_tail_none
  (#key: Type)
  (key_order: (key -> key -> bool))
  (key_order_irrefl: (
    (k1: key) ->
    (k2: key) ->
    Lemma
    (requires (key_order k1 k2))
    (ensures (~ (k1 == k2)))
  ))
  (key_order_trans: (
    (k1: key) ->
    (k2: key) ->
    (k3: key) ->
    Lemma
    (requires (key_order k1 k2 /\ key_order k2 k3))
    (ensures (key_order k1 k3))
  ))
  (#value: Type)
  (k: key)
  (v: value)
  (m: list (key & value))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) ((k, v) :: m)))
  (ensures list_ghost_assoc k m == None)
  (decreases m)
= match m with
  | [] -> ()
  | (k', v') :: m' ->
    map_entry_order_assoc_order_none key_order key_order_irrefl key_order_trans k' v' m' k

let rec map_entry_order_assoc_ext
  (#key: Type)
  (key_order: (key -> key -> bool))
  (key_order_irrefl: (
    (k1: key) ->
    (k2: key) ->
    Lemma
    (requires (key_order k1 k2))
    (ensures (~ (k1 == k2)))
  ))
  (key_order_trans: (
    (k1: key) ->
    (k2: key) ->
    (k3: key) ->
    Lemma
    (requires (key_order k1 k2 /\ key_order k2 k3))
    (ensures (key_order k1 k3))
  ))
  (key_order_total: (
    (k1: key) ->
    (k2: key) ->
    Lemma
    (k1 == k2 \/ key_order k1 k2 \/ key_order k2 k1)
  ))
  (#value: Type)
  (m1 m2: list (key & value))
  (ext: (
    (k: key) ->
    Lemma
    (list_ghost_assoc k m1 == list_ghost_assoc k m2)
  ))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) m1 /\ List.Tot.sorted (map_entry_order key_order _) m2))
  (ensures (m1 == m2))
  (decreases (List.Tot.length m1 + List.Tot.length m2))
= match m1, m2 with
  | [], [] -> ()
  | [], (k, _) :: _
  | (k, _) :: _, [] -> ext k
  | (k1, v1) :: m1', (k2, v2) :: m2' ->
    key_order_total k1 k2;
    ext k1;
    ext k2;
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k1 == k2)
    then begin
      map_entry_order_assoc_tail_none key_order key_order_irrefl key_order_trans k1 v1 m1';
      map_entry_order_assoc_tail_none key_order key_order_irrefl key_order_trans k2 v2 m2';
      map_entry_order_assoc_ext key_order key_order_irrefl key_order_trans key_order_total m1' m2' (fun k -> ext k)
    end
    else if key_order k1 k2
    then map_entry_order_assoc_order_none key_order key_order_irrefl key_order_trans k2 v2 m2' k1
    else map_entry_order_assoc_order_none key_order key_order_irrefl key_order_trans k1 v1 m1' k2

let map_entry_weak_compare
  (#key: Type)
  (#key_order: key -> key -> bool)
  (w: weak_compare_for key_order)
  (value: Type)
: Tot (weak_compare_for (map_entry_order key_order value))
= fun (k1, _) (k2, _) -> w k1 k2

let rec map_entry_insert_none
  (#key: Type)
  (#key_order: key -> key -> bool)
  (c: compare_for key_order)
  (#value: Type)
  (k: key)
  (v: value)
  (a: list (key & value))
: Lemma
  (ensures (None? (insert (map_entry_weak_compare #_ #key_order c value) (k, v) a) == Some? (list_ghost_assoc k a)))
  (decreases a)
= match a with
  | [] -> ()
  | (k', _) :: a' ->
    if c k k' > 0
    then map_entry_insert_none c k v a'
    else ()

let rec map_entry_insert_some
  (#key: Type)
  (#key_order: key -> key -> bool)
  (w: weak_compare_for key_order)
  (#value: Type)
  (k: key)
  (v: value)
  (a: list (key & value))
  (a': list (key & value))
  (k': key)
: Lemma
  (requires (insert (map_entry_weak_compare w value) (k, v) a == Some a'))
  (ensures (list_ghost_assoc k' a' == (if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k') then Some v else list_ghost_assoc k' a)))
  (decreases a)
= match a with
  | [] -> ()
  | (k1, _) :: a1 ->
    if w k k1 > 0 && not (FStar.StrongExcludedMiddle.strong_excluded_middle (k1 == k'))
    then
      let Some a1' = insert (map_entry_weak_compare w value) (k, v) a1 in
      map_entry_insert_some w k v a1 a1' k'
    else ()
