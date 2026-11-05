module CBOR.Spec.Raw.EverParse.DupCheck
include CBOR.Spec.Raw.EverParse.Items
include CBOR.Spec.Raw.DupCheck
open CBOR.Spec.Util
open LowParse.Spec

(* Specifications supporting the offset-based, sort-based map key
   duplicate check of CBOR.Pulse.Raw.EverParse.DupCheck. *)

module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module MS = LowParse.Spec.MergeSort
module U64 = FStar.UInt64
module U8 = FStar.UInt8

(* Generic sequence/list lemmas *)

let seq_to_list_index (#t: Type) (s: Seq.seq t) (i: nat) : Lemma
  (requires i < Seq.length s)
  (ensures (
    List.Tot.length (Seq.seq_to_list s) == Seq.length s /\
    List.Tot.index (Seq.seq_to_list s) i == Seq.index s i
  ))
= SP.lemma_index_is_nth s i

let seq_to_list_uncons (#t: Type) (s: Seq.seq t) : Lemma
  (requires Seq.length s > 0)
  (ensures Seq.seq_to_list s == Seq.index s 0 :: Seq.seq_to_list (Seq.slice s 1 (Seq.length s)))
= assert (s `Seq.equal` Seq.cons (Seq.index s 0) (Seq.slice s 1 (Seq.length s)));
  Seq.lemma_seq_to_list_cons (Seq.index s 0) (Seq.slice s 1 (Seq.length s))

let seq_to_list_slice_cons (#t: Type) (s: Seq.seq t) (i j: nat) : Lemma
  (requires i < j /\ j <= Seq.length s)
  (ensures Seq.seq_to_list (Seq.slice s i j) == Seq.index s i :: Seq.seq_to_list (Seq.slice s (i + 1) j))
= let s' = Seq.slice s i j in
  seq_to_list_uncons s';
  assert (Seq.slice s' 1 (Seq.length s') `Seq.equal` Seq.slice s (i + 1) j)

let rec seq_to_list_memP (#t: eqtype) (s: Seq.seq t) (x: t) : Lemma
  (ensures List.Tot.memP x (Seq.seq_to_list s) <==> SP.mem x s)
  (decreases (Seq.length s))
= if Seq.length s = 0
  then ()
  else begin
    let s' = Seq.slice s 1 (Seq.length s) in
    seq_to_list_memP s' x;
    seq_to_list_uncons s;
    SP.lemma_mem_inversion s
  end

let rec list_index_map (#a #b: Type) (f: a -> b) (l: list a) (i: nat) : Lemma
  (requires i < List.Tot.length l)
  (ensures List.Tot.length (List.Tot.map f l) == List.Tot.length l /\ List.Tot.index (List.Tot.map f l) i == f (List.Tot.index l i))
= if i = 0 then () else list_index_map f (List.Tot.tl l) (i - 1)

let rec ssorted_sorted_map
  (#t #t': Type)
  (cmp: t -> t -> int)
  (r: t' -> t' -> bool)
  (g: t -> t')
  (s: Seq.seq t)
  (prf: (x: t) -> (y: t) -> Lemma (requires cmp x y < 0) (ensures r (g x) (g y)))
: Lemma
  (requires MS.ssorted cmp s)
  (ensures List.Tot.sorted r (List.Tot.map g (Seq.seq_to_list s)))
  (decreases (Seq.length s))
= if Seq.length s <= 1
  then ()
  else begin
    let s' = Seq.slice s 1 (Seq.length s) in
    seq_to_list_uncons s;
    seq_to_list_uncons s';
    assert (Seq.index s' 0 == Seq.index s 1);
    assert (MS.ssorted cmp s' <==> (forall (i: nat) . i + 1 < Seq.length s' ==> cmp (Seq.index s (i + 1)) (Seq.index s (i + 2)) < 0));
    ssorted_sorted_map cmp r g s' prf;
    prf (Seq.index s 0) (Seq.index s 1)
  end

let list_memP_map_seq_iff
  (#t: eqtype) (#t': Type)
  (g: t -> t')
  (s1 s2: Seq.seq t)
: Lemma
  (requires forall x . SP.mem x s1 <==> SP.mem x s2)
  (ensures forall y . List.Tot.memP y (List.Tot.map g (Seq.seq_to_list s1)) <==> List.Tot.memP y (List.Tot.map g (Seq.seq_to_list s2)))
= Classical.forall_intro (seq_to_list_memP s1);
  Classical.forall_intro (seq_to_list_memP s2);
  list_memP_map_iff g (Seq.seq_to_list s1) (Seq.seq_to_list s2)

let perm_mem (#t: eqtype) (s1 s2: Seq.seq t) : Lemma
  (requires SP.permutation t s1 s2)
  (ensures forall x . SP.mem x s1 <==> SP.mem x s2)
= ()

(* Bounds and validity predicates *)

let item_bnd (n f: nat) (a: raw_data_item) : Tot bool =
  map_depth a <= f && map_length_bounded n a

let item_ok (n f: nat) (a: raw_data_item) : Tot bool =
  item_bnd n f a && valid_raw_data_item a

let item_bnd_map (n f: nat) (len: raw_uint64) (v: list (raw_data_item & raw_data_item)) : Lemma
  (requires List.Tot.length v == U64.v len.value /\ item_bnd n f (Map len v))
  (ensures
    f >= 1 /\
    U64.v len.value <= n /\
    List.Tot.for_all (item_bnd n (f - 1)) (list_of_pair_list v)
  )
= let a = Map len v in
  let p = map_length_bounded_elem n in
  map_depth_eq a;
  holds_on_raw_data_item_eq p a;
  list_max_map_dep_pair_list_of_pair_list v;
  list_of_pair_list_for_all (holds_on_raw_data_item p) v;
  let l = list_of_pair_list v in
  assert (List.Tot.for_all (holds_on_raw_data_item p) l);
  assert (list_max map_depth l <= f - 1);
  List.Tot.for_all_mem (holds_on_raw_data_item p) l;
  let prf (x: raw_data_item) : Lemma
    (requires List.Tot.memP x l)
    (ensures item_bnd n (f - 1) x)
  = list_max_correct map_depth l x;
    assert (holds_on_raw_data_item p x)
  in
  Classical.forall_intro (Classical.move_requires prf);
  List.Tot.for_all_mem (item_bnd n (f - 1)) l

let item_ok_map (n f: nat) (len: raw_uint64) (v: list (raw_data_item & raw_data_item)) : Lemma
  (requires List.Tot.length v == U64.v len.value /\ item_ok n f (Map len v))
  (ensures
    f >= 1 /\
    U64.v len.value <= n /\
    List.Tot.for_all (item_ok n (f - 1)) (list_of_pair_list v) /\
    List.Tot.for_all valid_raw_data_item (List.Tot.map fst v) /\
    list_no_setoid_repeats raw_equiv (List.Tot.map fst v) /\
    no_cc_dup (List.Tot.map fst v)
  )
= let a = Map len v in
  item_bnd_map n f len v;
  valid_eq basic_data_model a;
  list_of_pair_list_map valid_raw_data_item v;
  list_of_pair_list_for_all valid_raw_data_item v;
  let l = list_of_pair_list v in
  List.Tot.for_all_mem (item_bnd n (f - 1)) l;
  List.Tot.for_all_mem valid_raw_data_item l;
  List.Tot.for_all_mem (item_ok n (f - 1)) l;
  no_cc_dup_correct (List.Tot.map fst v)

let item_bnd_children (n f: nat) (a: raw_data_item) : Lemma
  (requires item_bnd n f a /\ ~ (Map? a))
  (ensures List.Tot.for_all (item_bnd n f) (children a))
= let p = map_length_bounded_elem n in
  map_depth_eq a;
  holds_on_raw_data_item_eq p a;
  match a with
  | Array _ l ->
    assert (List.Tot.for_all (holds_on_raw_data_item p) l);
    List.Tot.for_all_mem (holds_on_raw_data_item p) l;
    let prf (x: raw_data_item) : Lemma
      (requires List.Tot.memP x l)
      (ensures item_bnd n f x)
    = list_max_correct map_depth l x;
      assert (holds_on_raw_data_item p x)
    in
    Classical.forall_intro (Classical.move_requires prf);
    List.Tot.for_all_mem (item_bnd n f) l
  | _ -> ()

let item_ok_children (n f: nat) (a: raw_data_item) : Lemma
  (requires item_ok n f a /\ ~ (Map? a))
  (ensures List.Tot.for_all (item_ok n f) (children a))
= item_bnd_children n f a;
  valid_eq basic_data_model a;
  List.Tot.for_all_mem (item_bnd n f) (children a);
  List.Tot.for_all_mem valid_raw_data_item (children a);
  List.Tot.for_all_mem (item_ok n f) (children a)

(* Functional views of items at an offset *)

let dummy : raw_data_item = Int64 cbor_major_type_uint64 { size = 0uy; value = 0uL }

let item_at (b: bytes) (o: nat) : Tot raw_data_item =
  if o <= Seq.length b
  then match tot_parse_raw_data_item (Seq.slice b o (Seq.length b)) with
    | Some (x, _) -> x
    | None -> dummy
  else dummy

let item_end (b: bytes) (o: nat) : Tot nat =
  if o <= Seq.length b
  then match tot_parse_raw_data_item (Seq.slice b o (Seq.length b)) with
    | Some (_, c) -> o + c
    | None -> o
  else o

let item_at_eq (b: bytes) (o: nat) : Lemma
  (requires o <= Seq.length b)
  (ensures (match parse parse_raw_data_item (Seq.slice b o (Seq.length b)) with
    | Some (x, c) -> item_at b o == x /\ item_end b o == o + c
    | None -> True
  ))
= ()

let items_at_item_at (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures
    Cons? l /\
    item_at b o == List.Tot.hd l /\
    items_at b (item_end b o) (n - 1) (List.Tot.tl l) /\
    items_at b o 1 [List.Tot.hd l]
  )
= items_at_hd b o n l;
  let sb = Seq.slice b o (Seq.length b) in
  let Some (_, c) = parse parse_raw_data_item sb in
  let sb' = Seq.slice b (o + c) (Seq.length b) in
  parse_nlist_eq 0 parse_raw_data_item sb';
  items_at_intro_hd b o (List.Tot.hd l) c 0 []

let rec items_at_bound (b: bytes) (o: nat) (n: nat) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures o + n <= Seq.length b)
  (decreases n)
= if n = 0
  then ()
  else begin
    items_at_item_at b o n l;
    parser_kind_prop_equiv parse_raw_data_item_kind parse_raw_data_item;
    item_at_eq b o;
    items_at_hd b o n l;
    let Some (_, c) = parse parse_raw_data_item (Seq.slice b o (Seq.length b)) in
    assert (c >= 1);
    items_at_bound b (item_end b o) (n - 1) (List.Tot.tl l)
  end

let items_at_nil (b: bytes) (o: nat) : Lemma
  (requires o <= Seq.length b)
  (ensures items_at b o 0 [])
= parse_nlist_eq 0 parse_raw_data_item (Seq.slice b o (Seq.length b))

(* Comparing items at offsets *)

let key_cmp (b: bytes) (x y: SZ.t) : Tot int =
  cc (item_at b (SZ.v x)) (item_at b (SZ.v y))

let key_cmp_g (b: Ghost.erased bytes) : Ghost.erased (SZ.t -> SZ.t -> int) =
  Ghost.elift1 key_cmp b

let key_cmp_props (b: bytes) : Lemma
  (MS.compare_props (key_cmp b))
= cc_props

let cmp_pre (b: Ghost.erased bytes) (n f: Ghost.erased nat) (scl: nat) (x: SZ.t) : prop =
  scl >= 3 * n * f /\
  items_at b (SZ.v x) 1 [item_at b (SZ.v x)] /\
  item_ok n f (item_at b (SZ.v x))

(* Map entries at offsets *)

let entry_of (b: bytes) (x: SZ.t) : Tot (raw_data_item & raw_data_item) =
  (item_at b (SZ.v x), item_at b (item_end b (SZ.v x)))

let entry_pre (b: bytes) (n f: nat) (x: SZ.t) : prop =
  items_at b (SZ.v x) 2 [fst (entry_of b x); snd (entry_of b x)] /\
  item_ok n f (fst (entry_of b x)) /\
  item_ok n f (snd (entry_of b x))

let entry_pre_intro (b: bytes) (n f: nat) (x: SZ.t) (k v: raw_data_item) (q: list raw_data_item) (m: nat) : Lemma
  (requires
    items_at b (SZ.v x) (m + 2) (k :: v :: q) /\
    item_ok n f k /\ item_ok n f v
  )
  (ensures
    entry_pre b n f x /\
    entry_of b x == (k, v) /\
    item_end b (item_end b (SZ.v x)) <= Seq.length b /\
    items_at b (item_end b (item_end b (SZ.v x))) m q
  )
= let o = SZ.v x in
  items_at_hd b o (m + 2) (k :: v :: q);
  items_at_item_at b o (m + 2) (k :: v :: q);
  item_at_eq b o;
  let Some (_, c0) = parse parse_raw_data_item (Seq.slice b o (Seq.length b)) in
  let o1 = item_end b o in
  assert (o1 == o + c0);
  items_at_hd b o1 (m + 1) (v :: q);
  items_at_item_at b o1 (m + 1) (v :: q);
  item_at_eq b o1;
  let Some (_, c1) = parse parse_raw_data_item (Seq.slice b o1 (Seq.length b)) in
  let o2 = item_end b o1 in
  assert (o2 == o1 + c1);
  items_at_bound b o2 m q;
  items_at_nil b o2;
  items_at_intro_hd b o1 v c1 0 [];
  items_at_intro_hd b o k c0 1 [v]

let entry_pre_elim (b: bytes) (n f: nat) (x: SZ.t) : Lemma
  (requires entry_pre b n f x)
  (ensures (
    let o1 = item_end b (SZ.v x) in
    items_at b (SZ.v x) 1 [item_at b (SZ.v x)] /\
    item_ok n f (item_at b (SZ.v x)) /\
    o1 <= Seq.length b /\
    items_at b o1 1 [item_at b o1] /\
    item_ok n f (item_at b o1) /\
    (forall (o: SZ.t) . SZ.v o == o1 ==> (fst (entry_of b x) == item_at b (SZ.v x) /\ snd (entry_of b x) == item_at b (SZ.v o)))
  ))
= let (k, v) = entry_of b x in
  items_at_item_at b (SZ.v x) 2 [k; v];
  let o1 = item_end b (SZ.v x) in
  items_at_bound b o1 1 [v];
  items_at_item_at b o1 1 [v]

let entries_of (b: bytes) (s: Seq.seq SZ.t) : Tot (list (raw_data_item & raw_data_item)) =
  List.Tot.map (entry_of b) (Seq.seq_to_list s)

let entries_of_length (b: bytes) (s: Seq.seq SZ.t) : Lemma
  (List.Tot.length (entries_of b s) == Seq.length s)
  [SMTPat (List.Tot.length (entries_of b s))]
= ()

let entries_of_slice_cons (b: bytes) (s: Seq.seq SZ.t) (i j: nat) : Lemma
  (requires i < j /\ j <= Seq.length s)
  (ensures entries_of b (Seq.slice s i j) == entry_of b (Seq.index s i) :: entries_of b (Seq.slice s (i + 1) j))
= seq_to_list_slice_cons s i j

let entries_of_slice_full (b: bytes) (s: Seq.seq SZ.t) : Lemma
  (entries_of b (Seq.slice s 0 (Seq.length s)) == entries_of b s)
= assert (Seq.slice s 0 (Seq.length s) `Seq.equal` s)

let entries_of_slice_empty (b: bytes) (s: Seq.seq SZ.t) (i: nat) : Lemma
  (requires i <= Seq.length s)
  (ensures entries_of b (Seq.slice s i i) == [])
= ()

(* The offsets of the entries of a map, in the order of the input *)

let offsets_match (b: bytes) (s: Seq.seq SZ.t) (i: nat) (v: list (raw_data_item & raw_data_item)) : prop =
  i <= Seq.length s /\
  i <= List.Tot.length v /\
  (forall (j: nat) . j < i ==> entry_of b (Seq.index s j) == List.Tot.index v j) /\
  (forall (j1 j2: nat) . (j1 < j2 /\ j2 < i) ==> SZ.v (Seq.index s j1) < SZ.v (Seq.index s j2))

let offsets_match_step
  (b: bytes) (s s': Seq.seq SZ.t) (i: nat) (v: list (raw_data_item & raw_data_item)) (x: SZ.t)
: Lemma
  (requires
    offsets_match b s i v /\
    i < Seq.length s /\
    i < List.Tot.length v /\
    s' == Seq.upd s i x /\
    entry_of b x == List.Tot.index v i /\
    (forall (j: nat) . j < i ==> SZ.v (Seq.index s j) < SZ.v x)
  )
  (ensures offsets_match b s' (i + 1) v)
= ()

let offsets_sort_ok
  (b: bytes) (s0: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s0 (Seq.length s0) v /\
    Seq.length s0 == List.Tot.length v /\
    no_cc_dup (List.Tot.map fst v)
  )
  (ensures
    MS.compare_props (key_cmp b) /\
    MS.seq_distinct s0 /\
    MS.seq_no_cmp_dup (key_cmp b) s0 /\
    ~ (MS.sort_abort_witness (key_cmp b) s0)
  )
= key_cmp_props b;
  no_cc_dup_index (List.Tot.map fst v);
  let prf (i j: nat) : Lemma
    (requires i < j /\ j < Seq.length s0)
    (ensures (i < j /\ j < Seq.length s0) ==> key_cmp b (Seq.index s0 i) (Seq.index s0 j) <> 0)
  = list_index_map fst v i;
    list_index_map fst v j;
    let l = List.Tot.map fst v in
    assert (entry_of b (Seq.index s0 i) == List.Tot.index v i);
    assert (entry_of b (Seq.index s0 j) == List.Tot.index v j);
    assert (cc_eq0 (List.Tot.index l i) (List.Tot.index l j) == false)
  in
  Classical.forall_intro_2 (fun i -> Classical.move_requires (prf i));
  MS.sort_abort_witness_distinct (key_cmp b) s0

let offsets_sort_fail
  (b: bytes) (s0: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s0 (Seq.length s0) v /\
    Seq.length s0 == List.Tot.length v /\
    MS.sort_abort_witness (key_cmp b) s0
  )
  (ensures no_cc_dup (List.Tot.map fst v) == false)
= Classical.move_requires (offsets_sort_ok b s0) v

let offsets_match_entries
  (b: bytes) (s0: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s0 (Seq.length s0) v /\
    Seq.length s0 == List.Tot.length v
  )
  (ensures entries_of b s0 == v)
= let prf (i: nat) : Lemma
    (requires i < List.Tot.length v)
    (ensures i < List.Tot.length v ==> List.Tot.index (entries_of b s0) i == List.Tot.index v i)
  = list_index_map (entry_of b) (Seq.seq_to_list s0) i;
    seq_to_list_index s0 i
  in
  Classical.forall_intro (Classical.move_requires prf);
  FStar.List.Tot.Properties.index_extensionality (entries_of b s0) v

let sorted_entries
  (b: bytes) (s0 s1: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s0 (Seq.length s0) v /\
    Seq.length s0 == List.Tot.length v /\
    MS.sort_post (key_cmp b) s0 s1 true
  )
  (ensures (
    let l = entries_of b s1 in
    List.Tot.length l == List.Tot.length v /\
    (forall x . List.Tot.memP x l <==> List.Tot.memP x v) /\
    List.Tot.sorted cc_key_lt l
  ))
= offsets_match_entries b s0 v;
  perm_mem s0 s1;
  list_memP_map_seq_iff (entry_of b) s1 s0;
  ssorted_sorted_map (key_cmp b) cc_key_lt (entry_of b) s1 (fun _ _ -> ())

let cc_map_sorted
  (b: bytes)
  (n f: nat)
  (len1: raw_uint64) (v1: list (raw_data_item & raw_data_item)) (s01 s1: Seq.seq SZ.t)
  (len2: raw_uint64) (v2: list (raw_data_item & raw_data_item)) (s02 s2: Seq.seq SZ.t)
: Lemma
  (requires
    List.Tot.length v1 == U64.v len1.value /\
    List.Tot.length v2 == U64.v len2.value /\
    item_ok n f (Map len1 v1) /\
    item_ok n f (Map len2 v2) /\
    len1.value == len2.value /\
    offsets_match b s01 (Seq.length s01) v1 /\
    Seq.length s01 == List.Tot.length v1 /\
    MS.sort_post (key_cmp b) s01 s1 true /\
    offsets_match b s02 (Seq.length s02) v2 /\
    Seq.length s02 == List.Tot.length v2 /\
    MS.sort_post (key_cmp b) s02 s2 true
  )
  (ensures
    Seq.length s1 == Seq.length s2 /\
    cc (Map len1 v1) (Map len2 v2) == cc_entries (entries_of b s1) (entries_of b s2)
  )
= item_ok_map n f len1 v1;
  item_ok_map n f len2 v2;
  sorted_entries b s01 s1 v1;
  sorted_entries b s02 s2 v2;
  cc_eq (Map len1 v1) (Map len2 v2);
  cc_map_entries_sorted v1 (entries_of b s1) v2 (entries_of b s2)

(* The walker spec, one step at a time *)

let check_dups_cons (a: raw_data_item) (q: list raw_data_item) : Lemma
  (check_dups (a :: q) == (
    match a with
    | Map _ v -> check_dups (list_of_pair_list v) && no_cc_dup (List.Tot.map fst v) && check_dups q
    | _ -> check_dups (List.Tot.append (children a) q)
  ))
= match a with
  | Tagged _ v -> ()
  | Array _ v -> ()
  | Map _ v -> ()
  | _ -> ()

let list_sum_size_cons (a: raw_data_item) (q: list raw_data_item) : Lemma
  (list_sum raw_data_item_size (a :: q) > list_sum raw_data_item_size (List.Tot.append (children a) q) /\
   list_sum raw_data_item_size (a :: q) > list_sum raw_data_item_size q)
= raw_data_item_size_eq a;
  list_sum_append raw_data_item_size (children a) q;
  match a with
  | Map _ v -> list_of_pair_list_sum raw_data_item_size v
  | _ -> ()

(* One step of the item-list comparison *)

let cc_list_cons (a1 a2: raw_data_item) (q1 q2: list raw_data_item) : Lemma
  (requires List.Tot.length q1 == List.Tot.length q2)
  (ensures cc_list (a1 :: q1) (a2 :: q2) == (let c = cc a1 a2 in if c <> 0 then c else cc_list q1 q2))
= ()

let cc_string_eq (a1 a2: raw_data_item) : Lemma
  (requires String? a1 /\ String? a2 /\ String?.typ a1 == String?.typ a2 /\ (String?.len a1).value == (String?.len a2).value /\ CBOR.Spec.Raw.Format.bytes_lex_compare (String?.v a1) (String?.v a2) == 0)
  (ensures cc a1 a2 == 0)
= cc_eq a1 a2;
  let c = int_compare (U8.v (get_major_type a1)) (U8.v (get_major_type a2)) in
  assert (c == 0)

let same_major_type (a1 a2: raw_data_item) : Lemma
  (requires get_major_type a1 == get_major_type a2)
  (ensures
    Int64? a1 == Int64? a2 /\
    String? a1 == String? a2 /\
    Simple? a1 == Simple? a2 /\
    Array? a1 == Array? a2 /\
    Map? a1 == Map? a2 /\
    Tagged? a1 == Tagged? a2
  )
= ()

let cc_list_children (a1 a2: raw_data_item) (q1 q2: list raw_data_item) : Lemma
  (requires
    List.Tot.length q1 == List.Tot.length q2 /\
    ~ (Map? a1) /\
    get_major_type a1 == get_major_type a2 /\
    (Tagged? a1 ==> (Tagged?.tag a1).value == (Tagged?.tag a2).value) /\
    (Array? a1 ==> (Array?.len a1).value == (Array?.len a2).value) /\
    (Int64? a1 ==> (Int64?.v a1).value == (Int64?.v a2).value) /\
    (Simple? a1 ==> Simple?.v a1 == Simple?.v a2) /\
    (String? a1 ==> ((String?.len a1).value == (String?.len a2).value /\ CBOR.Spec.Raw.Format.bytes_lex_compare (String?.v a1) (String?.v a2) == 0))
  )
  (ensures
    List.Tot.length (children a1) == List.Tot.length (children a2) /\
    List.Tot.length (List.Tot.append (children a1) q1) == List.Tot.length (List.Tot.append (children a2) q2) /\
    cc_list (a1 :: q1) (a2 :: q2) == cc_list (List.Tot.append (children a1) q1) (List.Tot.append (children a2) q2)
  )
= cc_eq a1 a2;
  same_major_type a1 a2;
  match a1, a2 with
  | Tagged _ v1, Tagged _ v2 ->
    cc_list_append [v1] q1 [v2] q2
  | Array _ v1, Array _ v2 ->
    cc_list_append v1 q1 v2 q2
  | Int64 _ _, Int64 _ _ -> assert (cc a1 a2 == 0)
  | Simple _, Simple _ -> assert (cc a1 a2 == 0)
  | String _ _ _, String _ _ _ -> cc_string_eq a1 a2

let header_major_type (a: raw_data_item) : Lemma
  (get_header_major_type (get_raw_data_item_header a) == get_major_type a)
= let x = synth_raw_data_item_recip a in
  assert (synth_raw_data_item x == a)

(* Steps over items at offsets *)

let items_at_step (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures
    Cons? l /\
    Some? (parse parse_raw_data_item (Seq.slice b o (Seq.length b))) /\
    Some? (parse parse_header (Seq.slice b o (Seq.length b))) /\
    item_at b o == List.Tot.hd l /\
    o < item_end b o /\
    item_end b o <= Seq.length b /\
    items_at b (item_end b o) (n - 1) (List.Tot.tl l) /\
    items_at b o 1 [List.Tot.hd l]
  )
= items_at_item_at b o n l;
  items_at_cons b o n l;
  parser_kind_prop_equiv parse_raw_data_item_kind parse_raw_data_item;
  item_at_eq b o;
  items_at_hd b o n l

let items_at_header (b: bytes) (o: nat) (n: pos) (l: list raw_data_item) (h: header) (o1: nat) : Lemma
  (requires
    items_at b o n l /\
    (match parse parse_header (Seq.slice b o (Seq.length b)) with
     | Some (h', c) -> h' == h /\ o1 == o + c
     | None -> False)
  )
  (ensures (
    Cons? l /\ (
    let a = List.Tot.hd l in
    h == get_raw_data_item_header a /\
    get_header_major_type h == get_major_type a /\
    o1 + leaf_size h <= Seq.length b /\
    (String? a ==> Seq.slice b o1 (o1 + leaf_size h) == String?.v a) /\
    items_at b (o1 + leaf_size h) (remaining_data_items_header h + (n - 1)) (children a `List.Tot.append` List.Tot.tl l)
  )))
= items_at_cons b o n l;
  header_major_type (List.Tot.hd l)

let leaf_size_eq (a: raw_data_item) : Lemma
  (leaf_size (get_raw_data_item_header a) == (match a with String _ len _ -> U64.v len.value | _ -> 0))
= header_major_type a;
  let x = synth_raw_data_item_recip a in
  assert (synth_raw_data_item x == a)

(* Comparing the heads of two items with the same major type *)

let head_compare (a1 a2: raw_data_item) : Tot int =
  match a1, a2 with
  | Int64 _ v1, Int64 _ v2 -> int_compare (U64.v v1.value) (U64.v v2.value)
  | Simple v1, Simple v2 -> int_compare (U8.v v1) (U8.v v2)
  | String _ len1 _, String _ len2 _ -> int_compare (U64.v len1.value) (U64.v len2.value)
  | Tagged tag1 _, Tagged tag2 _ -> int_compare (U64.v tag1.value) (U64.v tag2.value)
  | Array len1 _, Array len2 _ -> int_compare (U64.v len1.value) (U64.v len2.value)
  | Map len1 _, Map len2 _ -> int_compare (U64.v len1.value) (U64.v len2.value)
  | _ -> 0

let cc_head (a1 a2: raw_data_item) : Lemma
  (requires get_major_type a1 == get_major_type a2)
  (ensures (
    let hc = head_compare a1 a2 in
    (hc <> 0 ==> cc a1 a2 == hc) /\
    (hc == 0 ==> (
      (String? a1 ==> cc a1 a2 == CBOR.Spec.Raw.Format.bytes_lex_compare (String?.v a1) (String?.v a2)) /\
      (Map? a1 ==> List.Tot.length (Map?.v a1) == List.Tot.length (Map?.v a2))
    ))
  ))
= cc_eq a1 a2;
  same_major_type a1 a2

let cc_list_head (a1 a2: raw_data_item) (q1 q2: list raw_data_item) : Lemma
  (requires
    List.Tot.length q1 == List.Tot.length q2 /\
    get_major_type a1 == get_major_type a2 /\
    ~ (Map? a1) /\
    head_compare a1 a2 == 0 /\
    (String? a1 ==> CBOR.Spec.Raw.Format.bytes_lex_compare (String?.v a1) (String?.v a2) == 0)
  )
  (ensures
    List.Tot.length (List.Tot.append (children a1) q1) == List.Tot.length (List.Tot.append (children a2) q2) /\
    cc_list (a1 :: q1) (a2 :: q2) == cc_list (List.Tot.append (children a1) q1) (List.Tot.append (children a2) q2)
  )
= same_major_type a1 a2;
  cc_list_children a1 a2 q1 q2

let item_ok_cons_children (n f: nat) (a: raw_data_item) (q: list raw_data_item) : Lemma
  (requires List.Tot.for_all (item_ok n f) (a :: q) /\ ~ (Map? a))
  (ensures List.Tot.for_all (item_ok n f) (List.Tot.append (children a) q))
= item_ok_children n f a;
  List.Tot.for_all_append (item_ok n f) (children a) q

let item_bnd_cons_children (n f: nat) (a: raw_data_item) (q: list raw_data_item) : Lemma
  (requires List.Tot.for_all (item_bnd n f) (a :: q) /\ ~ (Map? a))
  (ensures List.Tot.for_all (item_bnd n f) (List.Tot.append (children a) q))
= item_bnd_children n f a;
  List.Tot.for_all_append (item_bnd n f) (children a) q

let cc_list_nil (_: unit) : Lemma (cc_list [] [] == 0) = ()

let cc_list_single (a1 a2: raw_data_item) : Lemma (cc_list [a1] [a2] == cc a1 a2) = ()

(* Filling the offsets of map entries *)

let rec ldrop (#t: Type) (i: nat) (l: list t) : Tot (list t) (decreases i) =
  if i = 0 then l else match l with
  | [] -> []
  | _ :: q -> ldrop (i - 1) q

let rec ldrop_cons (#t: Type) (i: nat) (l: list t) : Lemma
  (requires i < List.Tot.length l)
  (ensures ldrop i l == List.Tot.index l i :: ldrop (i + 1) l)
  (decreases i)
= if i = 0 then () else ldrop_cons (i - 1) (List.Tot.tl l)

let rec ldrop_length (#t: Type) (i: nat) (l: list t) : Lemma
  (requires i <= List.Tot.length l)
  (ensures List.Tot.length (ldrop i l) == List.Tot.length l - i)
  (decreases i)
= if i = 0 then () else ldrop_length (i - 1) (List.Tot.tl l)

let entry_struct (b: bytes) (x: SZ.t) : prop =
  items_at b (SZ.v x) 2 [fst (entry_of b x); snd (entry_of b x)]

#push-options "--z3rlimit 64"

let fill_step
  (b: bytes) (o: nat) (rv: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires
    Cons? rv /\
    items_at b o (2 * List.Tot.length rv + m) (List.Tot.append (list_of_pair_list rv) q)
  )
  (ensures (
    let o1 = item_end b o in
    let o2 = item_end b o1 in
    Some? (parse parse_raw_data_item (Seq.slice b o (Seq.length b))) /\
    o < o1 /\ o1 < o2 /\ o2 <= Seq.length b /\
    Some? (parse parse_raw_data_item (Seq.slice b o1 (Seq.length b))) /\
    (forall (x: SZ.t) . SZ.v x == o ==> (entry_struct b x /\ entry_of b x == List.Tot.hd rv)) /\
    items_at b o2 (2 * List.Tot.length (List.Tot.tl rv) + m) (List.Tot.append (list_of_pair_list (List.Tot.tl rv)) q)
  ))
= let (k, v) :: rv' = rv in
  let l = List.Tot.append (list_of_pair_list rv) q in
  let n = 2 * List.Tot.length rv + m in
  assert (l == k :: v :: List.Tot.append (list_of_pair_list rv') q);
  items_at_step b o n l;
  let o1 = item_end b o in
  items_at_step b o1 (n - 1) (List.Tot.tl l);
  let o2 = item_end b o1 in
  items_at_nil b o2;
  item_at_eq b o1;
  let Some (_, c1) = parse parse_raw_data_item (Seq.slice b o1 (Seq.length b)) in
  items_at_intro_hd b o1 v c1 0 [];
  item_at_eq b o;
  let Some (_, c0) = parse parse_raw_data_item (Seq.slice b o (Seq.length b)) in
  items_at_intro_hd b o k c0 1 [v];
  let prf (x: SZ.t) : Lemma
    (requires SZ.v x == o)
    (ensures entry_struct b x /\ entry_of b x == List.Tot.hd rv)
  = ()
  in
  Classical.forall_intro (Classical.move_requires prf)

#pop-options

let fill_init (b: bytes) (s: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item)) : Lemma
  (requires Seq.length s == List.Tot.length v)
  (ensures offsets_match b s 0 v /\ ldrop 0 v == v)
= ()

let entries_ok (b: bytes) (n f: nat) (s: Seq.seq SZ.t) : prop =
  forall (x: SZ.t) . SP.mem x s ==> entry_pre b n f x

let rec for_all_lopl_index (p: raw_data_item -> bool) (v: list (raw_data_item & raw_data_item)) (j: nat) : Lemma
  (requires List.Tot.for_all p (list_of_pair_list v) /\ j < List.Tot.length v)
  (ensures p (fst (List.Tot.index v j)) /\ p (snd (List.Tot.index v j)))
  (decreases j)
= match v with
  | _ :: q -> if j = 0 then () else for_all_lopl_index p q (j - 1)

let fill_entries_ok
  (b: bytes) (n f: nat) (s: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s (Seq.length s) v /\
    Seq.length s == List.Tot.length v /\
    (forall (j: nat) . j < Seq.length s ==> entry_struct b (Seq.index s j)) /\
    List.Tot.for_all (item_ok n f) (list_of_pair_list v)
  )
  (ensures entries_ok b n f s)
= let prf (x: SZ.t) : Lemma
    (requires SP.mem x s)
    (ensures entry_pre b n f x)
  = let j = SP.index_mem x s in
    for_all_lopl_index (item_ok n f) v j
  in
  Classical.forall_intro (Classical.move_requires prf)

let entries_ok_perm (b: bytes) (n f: nat) (s1 s2: Seq.seq SZ.t) : Lemma
  (requires entries_ok b n f s1 /\ SP.permutation SZ.t s1 s2)
  (ensures entries_ok b n f s2)
= perm_mem s1 s2

let rec seq_index_mem (#t: eqtype) (s: Seq.seq t) (i: nat) : Lemma
  (requires i < Seq.length s)
  (ensures SP.mem (Seq.index s i) s)
  (decreases i)
= if i = 0
  then ()
  else seq_index_mem (Seq.tail s) (i - 1)

let entries_ok_index (b: bytes) (n f: nat) (s: Seq.seq SZ.t) (i: nat) : Lemma
  (requires entries_ok b n f s /\ i < Seq.length s)
  (ensures entry_pre b n f (Seq.index s i))
= seq_index_mem s i

let entry_pre_cmp_pre (b: Ghost.erased bytes) (n f: Ghost.erased nat) (scl: nat) (x: SZ.t) : Lemma
  (requires entry_pre b n f x /\ scl >= 3 * n * f)
  (ensures cmp_pre b n f scl x)
= entry_pre_elim b n f x

let entries_ok_cmp_pre (b: Ghost.erased bytes) (n f: Ghost.erased nat) (scl: nat) (s: Seq.seq SZ.t) : Lemma
  (requires entries_ok b n f s /\ scl >= 3 * n * f)
  (ensures forall x . SP.mem x s ==> cmp_pre b n f scl x)
= Classical.forall_intro (Classical.move_requires (entry_pre_cmp_pre b n f scl))

(* Successful sort means no duplicates *)

let offsets_sort_success
  (b: bytes) (s0 s1: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s0 (Seq.length s0) v /\
    Seq.length s0 == List.Tot.length v /\
    MS.sort_post (key_cmp b) s0 s1 true
  )
  (ensures no_cc_dup (List.Tot.map fst v) == true)
= key_cmp_props b;
  MS.sorted_no_dup (key_cmp b) s0 s1;
  MS.sort_abort_witness_distinct (key_cmp b) s0;
  let l = List.Tot.map fst v in
  let prf (i j: nat) : Lemma
    (requires i < j /\ j < List.Tot.length l)
    (ensures (i < j /\ j < List.Tot.length l) ==> cc_eq0 (List.Tot.index l i) (List.Tot.index l j) == false)
  = list_index_map fst v i;
    list_index_map fst v j;
    assert (key_cmp b (Seq.index s0 i) (Seq.index s0 j) <> 0)
  in
  Classical.forall_intro_2 (fun i -> Classical.move_requires (prf i));
  no_cc_dup_index l

(* The lockstep comparison of sorted entries *)

let cc_entries_step (b: bytes) (s1 s2: Seq.seq SZ.t) (i: nat) : Lemma
  (requires i < Seq.length s1 /\ Seq.length s1 == Seq.length s2)
  (ensures (
    let k = Seq.length s1 in
    let x1 = Seq.index s1 i in
    let x2 = Seq.index s2 i in
    cc_entries (entries_of b (Seq.slice s1 i k)) (entries_of b (Seq.slice s2 i k)) == (
      let c = key_cmp b x1 x2 in
      if c <> 0 then c else
      let c = cc (item_at b (item_end b (SZ.v x1))) (item_at b (item_end b (SZ.v x2))) in
      if c <> 0 then c else
      cc_entries (entries_of b (Seq.slice s1 (i + 1) k)) (entries_of b (Seq.slice s2 (i + 1) k))
    )
  ))
= let k = Seq.length s1 in
  entries_of_slice_cons b s1 i k;
  entries_of_slice_cons b s2 i k

let cc_entries_init (b: bytes) (s1 s2: Seq.seq SZ.t) : Lemma
  (requires Seq.length s1 == Seq.length s2)
  (ensures
    cc_entries (entries_of b s1) (entries_of b s2) ==
    cc_entries (entries_of b (Seq.slice s1 0 (Seq.length s1))) (entries_of b (Seq.slice s2 0 (Seq.length s2))))
= entries_of_slice_full b s1;
  entries_of_slice_full b s2

let cc_entries_end (b: bytes) (s1 s2: Seq.seq SZ.t) : Lemma
  (requires Seq.length s1 == Seq.length s2)
  (ensures cc_entries (entries_of b (Seq.slice s1 (Seq.length s1) (Seq.length s1))) (entries_of b (Seq.slice s2 (Seq.length s2) (Seq.length s2))) == 0)
= entries_of_slice_empty b s1 (Seq.length s1);
  entries_of_slice_empty b s2 (Seq.length s2)

(* The map item at the head of a list *)

let item_ok_map_hd (n f: nat) (a: raw_data_item) (q: list raw_data_item) : Lemma
  (requires List.Tot.for_all (item_ok n f) (a :: q) /\ Map? a)
  (ensures (
    let Map len v = a in
    f >= 1 /\
    U64.v len.value <= n /\
    List.Tot.length v == U64.v len.value /\
    item_ok n f a /\
    List.Tot.for_all (item_ok n f) q /\
    children a == list_of_pair_list v /\
    List.Tot.for_all (item_ok n (f - 1)) (list_of_pair_list v)
  ))
= let Map len v = a in
  item_ok_map n f len v

let item_bnd_map_hd (n f: nat) (a: raw_data_item) (q: list raw_data_item) : Lemma
  (requires List.Tot.for_all (item_bnd n f) (a :: q) /\ Map? a)
  (ensures (
    let Map len v = a in
    f >= 1 /\
    U64.v len.value <= n /\
    List.Tot.length v == U64.v len.value /\
    List.Tot.for_all (item_bnd n f) q /\
    children a == list_of_pair_list v /\
    List.Tot.length (list_of_pair_list v) == 2 * List.Tot.length v /\
    List.Tot.for_all (item_bnd n (f - 1)) (list_of_pair_list v)
  ))
= let Map len v = a in
  item_bnd_map n f len v;
  list_of_pair_list_length v

let walker_map_ok (n f: nat) (a: raw_data_item) (q: list raw_data_item) : Lemma
  (requires
    Map? a /\
    List.Tot.for_all (item_bnd n f) [a] /\
    check_dups (children a) == true
  )
  (ensures
    List.Tot.for_all (item_ok n (f - 1)) (children a) /\
    check_dups (a :: q) == (no_cc_dup (List.Tot.map fst (Map?.v a)) && check_dups q)
  )
= let Map len v = a in
  item_bnd_map n f len v;
  check_dups_correct (list_of_pair_list v);
  let l = list_of_pair_list v in
  List.Tot.for_all_mem (item_bnd n (f - 1)) l;
  List.Tot.for_all_mem valid_raw_data_item l;
  List.Tot.for_all_mem (item_ok n (f - 1)) l;
  check_dups_cons a q

let check_dups_single (x: raw_data_item) : Lemma
  (check_dups (List.Tot.append [x] []) == valid_raw_data_item x)
= check_dups_valid x

let items_at_append_nil (b: bytes) (o: nat) (n: nat) (l: list raw_data_item) : Lemma
  (requires items_at b o n l)
  (ensures items_at b o n (List.Tot.append l []))
= List.Tot.append_l_nil l

(* The invariant of the loop filling the offsets of map entries *)

let fill_inv
  (b: bytes) (s: Seq.seq SZ.t) (i: nat) (o: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: prop
= i <= Seq.length s /\
  Seq.length s == List.Tot.length v /\
  offsets_match b s i v /\
  (forall (j: nat) . j < i ==> (entry_struct b (Seq.index s j) /\ SZ.v (Seq.index s j) < o)) /\
  List.Tot.length (ldrop i v) == List.Tot.length v - i /\
  items_at b o (2 * List.Tot.length (ldrop i v) + m) (List.Tot.append (list_of_pair_list (ldrop i v)) q)

let fill_inv_init
  (b: bytes) (s: Seq.seq SZ.t) (o: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires
    Seq.length s == List.Tot.length v /\
    items_at b o (2 * List.Tot.length v + m) (List.Tot.append (list_of_pair_list v) q)
  )
  (ensures fill_inv b s 0 o v m q)
= ()

#push-options "--z3rlimit 64"

let fill_inv_step
  (b: bytes) (s: Seq.seq SZ.t) (i: nat) (x: SZ.t)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires fill_inv b s i (SZ.v x) v m q /\ i < Seq.length s)
  (ensures (
    let o = SZ.v x in
    let o1 = item_end b o in
    let o2 = item_end b o1 in
    Some? (parse parse_raw_data_item (Seq.slice b o (Seq.length b))) /\
    o1 <= Seq.length b /\
    Some? (parse parse_raw_data_item (Seq.slice b o1 (Seq.length b))) /\
    o2 <= Seq.length b /\
    fill_inv b (Seq.upd s i x) (i + 1) o2 v m q
  ))
= let o = SZ.v x in
  ldrop_cons i v;
  ldrop_length (i + 1) v;
  fill_step b o (ldrop i v) m q;
  let o2 = item_end b (item_end b o) in
  let s' = Seq.upd s i x in
  offsets_match_step b s s' i v x;
  assert (forall (j: nat) . j < i + 1 ==> (entry_struct b (Seq.index s' j) /\ SZ.v (Seq.index s' j) < o2))

#pop-options

let fill_inv_end
  (b: bytes) (s: Seq.seq SZ.t) (o: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires fill_inv b s (Seq.length s) o v m q)
  (ensures
    Seq.length s == List.Tot.length v /\
    offsets_match b s (Seq.length s) v /\
    (forall (j: nat) . j < Seq.length s ==> entry_struct b (Seq.index s j)) /\
    items_at b o m q
  )
= let l = ldrop (Seq.length s) v in
  assert (List.Tot.length l == 0);
  assert (l == [])

(* The invariant of the comparison loop *)

let cmp_inv
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2: nat) (c: nat)
  (l1 l2: list raw_data_item) (res: int)
: prop
= items_at b o1 c l1 /\ items_at b o2 c l2 /\
  List.Tot.length l1 == c /\ List.Tot.length l2 == c /\
  List.Tot.for_all (item_ok n f) l1 /\ List.Tot.for_all (item_ok n f) l2 /\
  (res == 0 ==> key_cmp b x y == cc_list l1 l2) /\
  (res <> 0 ==> MS.same_sign res (key_cmp b x y))

let cmp_inv_init (b: Ghost.erased bytes) (n f: Ghost.erased nat) (scl: nat) (x y: SZ.t) : Lemma
  (requires cmp_pre b n f scl x /\ cmp_pre b n f scl y)
  (ensures cmp_inv b n f x y (SZ.v x) (SZ.v y) 1 [item_at b (SZ.v x)] [item_at b (SZ.v y)] 0)
= cc_list_single (item_at b (SZ.v x)) (item_at b (SZ.v y))

let cmp_inv_end
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2: nat) (c: nat)
  (l1 l2: list raw_data_item) (res: int)
: Lemma
  (requires cmp_inv b n f x y o1 o2 c l1 l2 res /\ (res <> 0 \/ c == 0))
  (ensures MS.same_sign res (key_cmp b x y))
= ()

let cmp_inv_stop
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2: nat) (c: nat)
  (l1 l2: list raw_data_item) (r: int)
: Lemma
  (requires
    cmp_inv b n f x y o1 o2 c l1 l2 0 /\
    Cons? l1 /\ Cons? l2 /\ r <> 0 /\
    MS.same_sign r (cc (List.Tot.hd l1) (List.Tot.hd l2))
  )
  (ensures cmp_inv b n f x y o1 o2 c l1 l2 r)
= ()

let cc_major_type_diff (a1 a2: raw_data_item) : Lemma
  (requires get_major_type a1 <> get_major_type a2)
  (ensures cc a1 a2 == int_compare (U8.v (get_major_type a1)) (U8.v (get_major_type a2)))
= cc_eq a1 a2

let str_eq (a1 a2: raw_data_item) : prop =
  match a1, a2 with
  | String _ _ v1, String _ _ v2 -> CBOR.Spec.Raw.Format.bytes_lex_compare v1 v2 == 0
  | _ -> True

let cmp_inv_cont_nonmap
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2: nat) (c: nat)
  (l1 l2: list raw_data_item) (o1' o2': nat)
: Lemma
  (requires
    cmp_inv b n f x y o1 o2 c l1 l2 0 /\
    Cons? l1 /\ Cons? l2 /\ (
    let a1 = List.Tot.hd l1 in
    let a2 = List.Tot.hd l2 in
    get_major_type a1 == get_major_type a2 /\
    ~ (Map? a1) /\
    head_compare a1 a2 == 0 /\
    str_eq a1 a2 /\
    items_at b o1' (remaining_data_items_header (get_raw_data_item_header a1) + (c - 1)) (List.Tot.append (children a1) (List.Tot.tl l1)) /\
    items_at b o2' (remaining_data_items_header (get_raw_data_item_header a2) + (c - 1)) (List.Tot.append (children a2) (List.Tot.tl l2))
  ))
  (ensures (
    let a1 = List.Tot.hd l1 in
    let a2 = List.Tot.hd l2 in
    let c' = remaining_data_items_header (get_raw_data_item_header a1) + (c - 1) in
    remaining_data_items_header (get_raw_data_item_header a1) == remaining_data_items_header (get_raw_data_item_header a2) /\
    cmp_inv b n f x y o1' o2' c' (List.Tot.append (children a1) (List.Tot.tl l1)) (List.Tot.append (children a2) (List.Tot.tl l2)) 0 /\
    list_sum raw_data_item_size (List.Tot.append (children a1) (List.Tot.tl l1)) < list_sum raw_data_item_size l1
  ))
= let a1 :: q1 = l1 in
  let a2 :: q2 = l2 in
  same_major_type a1 a2;
  cc_list_head a1 a2 q1 q2;
  item_ok_cons_children n f a1 q1;
  item_ok_cons_children n f a2 q2;
  list_sum_size_cons a1 q1;
  items_at_length b o1' (remaining_data_items_header (get_raw_data_item_header a1) + (c - 1)) (List.Tot.append (children a1) q1);
  items_at_length b o2' (remaining_data_items_header (get_raw_data_item_header a2) + (c - 1)) (List.Tot.append (children a2) q2)

let cmp_inv_cont_map
  (b: bytes) (n f: nat) (x y: SZ.t) (o1 o2: nat) (c: nat)
  (l1 l2: list raw_data_item) (o1' o2': nat)
: Lemma
  (requires
    cmp_inv b n f x y o1 o2 c l1 l2 0 /\
    Cons? l1 /\ Cons? l2 /\
    cc (List.Tot.hd l1) (List.Tot.hd l2) == 0 /\
    items_at b o1' (c - 1) (List.Tot.tl l1) /\
    items_at b o2' (c - 1) (List.Tot.tl l2)
  )
  (ensures
    cmp_inv b n f x y o1' o2' (c - 1) (List.Tot.tl l1) (List.Tot.tl l2) 0 /\
    list_sum raw_data_item_size (List.Tot.tl l1) < list_sum raw_data_item_size l1
  )
= let a1 :: q1 = l1 in
  let a2 :: q2 = l2 in
  list_sum_size_cons a1 q1

let remaining_children_length (a: raw_data_item) : Lemma
  (List.Tot.length (children a) == remaining_data_items_header (get_raw_data_item_header a))
= synth_raw_data_item_from_alt_header_children a;
  let (| lf, c |) = synth_raw_data_item_from_alt_recip a in
  assert (List.Tot.length (c <: list raw_data_item) == remaining_data_items lf)

let children_map_length (a: raw_data_item) : Lemma
  (requires Map? a)
  (ensures
    leaf_size (get_raw_data_item_header a) == 0 /\
    children a == list_of_pair_list (Map?.v a) /\
    List.Tot.length (children a) == 2 * List.Tot.length (Map?.v a))
= let Map _ v = a in
  leaf_size_eq a;
  list_of_pair_list_length v

let map_layout (b: bytes) (o1: nat) (c: pos) (a: raw_data_item) (q: list raw_data_item) : Lemma
  (requires
    Map? a /\
    items_at b (o1 + leaf_size (get_raw_data_item_header a)) (remaining_data_items_header (get_raw_data_item_header a) + (c - 1)) (List.Tot.append (children a) q)
  )
  (ensures
    items_at b o1 (2 * List.Tot.length (Map?.v a) + (c - 1)) (List.Tot.append (list_of_pair_list (Map?.v a)) q)
  )
= children_map_length a;
  remaining_children_length a;
  let r = remaining_data_items_header (get_raw_data_item_header a) in
  items_at_length b (o1 + leaf_size (get_raw_data_item_header a)) (r + (c - 1)) (List.Tot.append (children a) q);
  List.Tot.append_length (children a) q;
  assert (r == 2 * List.Tot.length (Map?.v a));
  assert (o1 + leaf_size (get_raw_data_item_header a) == o1);
  assert (List.Tot.append (children a) q == List.Tot.append (list_of_pair_list (Map?.v a)) q)
