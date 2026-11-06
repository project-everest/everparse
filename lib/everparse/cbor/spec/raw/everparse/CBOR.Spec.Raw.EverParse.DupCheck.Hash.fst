module CBOR.Spec.Raw.EverParse.DupCheck.Hash
include CBOR.Spec.Raw.EverParse.DupCheck
include CBOR.Spec.Raw.Hash
open CBOR.Spec.Util
open LowParse.Spec

(* Specifications supporting the hash-based map key duplicate check of
   CBOR.Pulse.Raw.EverParse.DupCheck: the keys of a map are sorted by
   hash first, then by `cc` only when their hashes are equal. *)

module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module MS = LowParse.Spec.MergeSort
module U64 = FStar.UInt64
module U8 = FStar.UInt8

(* Hashing a list of items with a work list *)

let head_value (a: raw_data_item) : Tot U64.t =
  match a with
  | Simple v -> FStar.Int.Cast.uint8_to_uint64 v
  | Int64 _ v -> v.value
  | String _ len _ -> len.value
  | Tagged tag _ -> tag.value
  | Array len _ -> len.value
  | Map len _ -> len.value

let leaf_feed (s: sip) (a: raw_data_item) : Tot sip =
  match a with
  | String _ _ v -> absorb_bytes s v
  | _ -> s

let rec rh_feed_list_append (k0 k1: U64.t) (s: sip) (l1 l2: list raw_data_item) : Lemma
  (ensures rh_feed_list k0 k1 s (List.Tot.append l1 l2) == rh_feed_list k0 k1 (rh_feed_list k0 k1 s l1) l2)
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q -> rh_feed_list_append k0 k1 (rh_feed k0 k1 s a) q l2

#push-options "--fuel 2 --ifuel 1"

let rh_step_nonmap (k0 k1: U64.t) (s: sip) (a: raw_data_item) (tl: list raw_data_item) : Lemma
  (requires ~ (Map? a))
  (ensures rh_feed_list k0 k1 s (a :: tl) ==
    rh_feed_list k0 k1 (leaf_feed (rh_head s (get_major_type a) (head_value a)) a) (List.Tot.append (children a) tl))
= let s1 = leaf_feed (rh_head s (get_major_type a) (head_value a)) a in
  rh_feed_list_append k0 k1 s1 (children a) tl;
  match a with
  | Tagged _ v -> assert (rh_feed_list k0 k1 s1 [v] == rh_feed k0 k1 s1 v)
  | _ -> ()

let rh_step_map (k0 k1: U64.t) (s: sip) (a: raw_data_item) (tl: list raw_data_item) : Lemma
  (requires Map? a)
  (ensures rh_feed_list k0 k1 s (a :: tl) ==
    rh_feed_list k0 k1 (sip_absorb (rh_head s cbor_major_type_map (head_value a)) (msum k0 k1 (Map?.v a))) tl)
= ()

let rh_single (k0 k1: U64.t) (x: raw_data_item) : Lemma
  (sip_fin (rh_feed_list k0 k1 (sip_init k0 k1) [x]) == rh k0 k1 x)
= ()

#pop-options

(* The loop over the entries of a map, hashing them *)

let add_mod_zero (x: U64.t) : Lemma
  (U64.add_mod 0uL x == x /\ U64.add_mod x 0uL == x)
= FStar.Math.Lemmas.small_mod (U64.v x) (pow2 64);
  U64.v_inj (U64.add_mod 0uL x) x;
  U64.v_inj (U64.add_mod x 0uL) x

let hent_inv
  (b: bytes) (k0 k1: U64.t) (oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
  (i e: nat) (acc: U64.t)
: prop
= i <= List.Tot.length v /\
  List.Tot.length (ldrop i v) == List.Tot.length v - i /\
  items_at b e (2 * (List.Tot.length v - i) + m) (List.Tot.append (list_of_pair_list (ldrop i v)) q) /\
  e == items_end b oh (2 * i) /\
  msum k0 k1 v == U64.add_mod acc (msum k0 k1 (ldrop i v))

let hent_init
  (b: bytes) (k0 k1: U64.t) (oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
: Lemma
  (requires items_at b oh (2 * List.Tot.length v + m) (List.Tot.append (list_of_pair_list v) q))
  (ensures hent_inv b k0 k1 oh v m q 0 oh 0uL)
= assert (ldrop 0 v == v);
  assert (items_end b oh 0 == oh);
  add_mod_zero (msum k0 k1 v)

let hent_mk (v: list (raw_data_item & raw_data_item)) (i: nat) (m: nat) : Tot nat =
  if i < List.Tot.length v then 2 * (List.Tot.length v - (i + 1)) + m else m

let hent_qv (v: list (raw_data_item & raw_data_item)) (i: nat) (q: list raw_data_item) : Tot (list raw_data_item) =
  List.Tot.append (list_of_pair_list (ldrop (i + 1) v)) q

let hent_mk_eq (v: list (raw_data_item & raw_data_item)) (i: nat) (m: nat) : Lemma
  (requires i < List.Tot.length v)
  (ensures
    hent_mk v i m == 2 * (List.Tot.length v - (i + 1)) + m /\
    1 + (1 + hent_mk v i m) == 2 * (List.Tot.length v - i) + m)
= ()

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"

let hent_pre
  (b: bytes) (k0 k1: U64.t) (n f: nat) (oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
  (i e: nat) (acc: U64.t)
: Lemma
  (requires
    hent_inv b k0 k1 oh v m q i e acc /\
    i < List.Tot.length v /\
    List.Tot.for_all (item_bnd n f) (list_of_pair_list v))
  (ensures (
    let ei = List.Tot.index v i in
    List.Tot.for_all (item_bnd n f) [fst ei] /\
    List.Tot.for_all (item_bnd n f) [snd ei] /\
    hent_mk v i m == 2 * (List.Tot.length v - (i + 1)) + m /\
    items_at b e (1 + (1 + hent_mk v i m)) (List.Tot.append [fst ei] (List.Tot.append [snd ei] (hent_qv v i q)))))
= let ei = List.Tot.index v i in
  for_all_lopl_index (item_bnd n f) v i;
  lopl_ldrop_cons v i;
  ldrop_length (i + 1) v;
  let x = hent_qv v i q in
  assert (List.Tot.append [fst ei] (List.Tot.append [snd ei] x) == fst ei :: snd ei :: x);
  assert (List.Tot.append (list_of_pair_list (ldrop i v)) q == fst ei :: snd ei :: x);
  hent_mk_eq v i m;
  assert (items_at b e (2 * (List.Tot.length v - i) + m) (List.Tot.append (list_of_pair_list (ldrop i v)) q))

let hent_step
  (b: bytes) (k0 k1: U64.t) (oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
  (i e: nat) (acc: U64.t)
  (o1 o2: nat) (sk sv: sip)
: Lemma
  (requires (
    i < List.Tot.length v /\ (
    let ei = List.Tot.index v i in
    hent_inv b k0 k1 oh v m q i e acc /\
    o1 == items_end b e 1 /\
    o2 == items_end b o1 1 /\
    items_at b o2 (hent_mk v i m) (hent_qv v i q) /\
    sk == rh_feed_list k0 k1 (sip_init k0 k1) [fst ei] /\
    sv == rh_feed_list k0 k1 (sip_init k0 k1) [snd ei])))
  (ensures
    hent_inv b k0 k1 oh v m q (i + 1) o2 (U64.add_mod acc (ehash k0 k1 (sip_fin sk) (sip_fin sv))))
= let ei = List.Tot.index v i in
  rh_single k0 k1 (fst ei);
  rh_single k0 k1 (snd ei);
  ldrop_cons i v;
  ldrop_length (i + 1) v;
  hent_mk_eq v i m;
  items_end_add b oh (2 * i) 2;
  items_end_add b e 1 1;
  add_mod_assoc acc (ent k0 k1 ei) (msum k0 k1 (ldrop (i + 1) v))

#pop-options

let hent_end
  (b: bytes) (k0 k1: U64.t) (oh: nat)
  (v: list (raw_data_item & raw_data_item)) (m: nat) (q: list raw_data_item)
  (e: nat) (acc: U64.t)
: Lemma
  (requires hent_inv b k0 k1 oh v m q (List.Tot.length v) e acc)
  (ensures
    items_at b e m q /\
    e == items_end b oh (2 * List.Tot.length v) /\
    msum k0 k1 v == acc)
= ldrop_length (List.Tot.length v) v;
  assert (ldrop (List.Tot.length v) v == [])

(* Hashing bytes *)

let le_word_step (b: Seq.seq U8.t) (x y: nat) : Lemma
  (requires x < y /\ y <= Seq.length b)
  (ensures le_word (Seq.slice b x y) ==
    U64.logor (FStar.Int.Cast.uint8_to_uint64 (Seq.index b x)) (U64.shift_left (le_word (Seq.slice b (x + 1) y)) 8ul))
= assert (Seq.tail (Seq.slice b x y) `Seq.equal` Seq.slice b (x + 1) y)

let le_word_nil (b: Seq.seq U8.t) (x: nat) : Lemma
  (requires x <= Seq.length b)
  (ensures le_word (Seq.slice b x x) == 0uL)
= ()

let absorb_bytes_step (s: sip) (b: Seq.seq U8.t) (x y: nat) : Lemma
  (requires x < y /\ y <= Seq.length b)
  (ensures (
    let c = if y - x < 8 then y - x else 8 in
    absorb_bytes s (Seq.slice b x y) ==
      absorb_bytes (sip_absorb s (le_word (Seq.slice b x (x + c)))) (Seq.slice b (x + c) y)))
= let c = if y - x < 8 then y - x else 8 in
  assert (Seq.slice (Seq.slice b x y) 0 c `Seq.equal` Seq.slice b x (x + c));
  assert (Seq.slice (Seq.slice b x y) c (y - x) `Seq.equal` Seq.slice b (x + c) y)

let absorb_bytes_nil (s: sip) (b: Seq.seq U8.t) (x: nat) : Lemma
  (requires x <= Seq.length b)
  (ensures absorb_bytes s (Seq.slice b x x) == s)
= ()

(* Sorting the keys of a map by hash first: we sort the indices of the
   key offsets, so that the hash of each key is computed only once *)

let hv_at (shv: Seq.seq U64.t) (i: SZ.t) : Tot U64.t =
  if SZ.v i < Seq.length shv then Seq.index shv (SZ.v i) else 0uL

let ks_at (sks: Seq.seq SZ.t) (i: SZ.t) : Tot SZ.t =
  if SZ.v i < Seq.length sks then Seq.index sks (SZ.v i) else 0sz

let icmp (b: bytes) (sks: Seq.seq SZ.t) (shv: Seq.seq U64.t) (i j: SZ.t) : Tot int =
  let hi = hv_at shv i in
  let hj = hv_at shv j in
  if U64.lt hi hj then -1
  else if U64.lt hj hi then 1
  else key_cmp b (ks_at sks i) (ks_at sks j)

let icmp_g (b: Ghost.erased bytes) (sks: Ghost.erased (Seq.seq SZ.t)) (shv: Ghost.erased (Seq.seq U64.t)) : Ghost.erased (SZ.t -> SZ.t -> int) =
  Ghost.hide (icmp b sks shv)

let icmp_props (b: bytes) (sks: Seq.seq SZ.t) (shv: Seq.seq U64.t) : Lemma
  (MS.compare_props (icmp b sks shv))
= key_cmp_props b

let ipre (k: nat) (i: SZ.t) : prop = SZ.v i < k

(* The hashes of the keys *)

[@@"opaque_to_smt"]
let key_hash (b: bytes) (k0 k1: U64.t) (x: SZ.t) : Tot U64.t =
  rh k0 k1 (item_at b (SZ.v x))

let key_hash_eq (b: bytes) (k0 k1: U64.t) (x: SZ.t) : Lemma
  (key_hash b k0 k1 x == rh k0 k1 (item_at b (SZ.v x)))
= reveal_opaque (`%key_hash) (key_hash b k0 k1 x)

let hv_ok (b: bytes) (k0 k1: U64.t) (sks: Seq.seq SZ.t) (shv: Seq.seq U64.t) (i: nat) : prop =
  i <= Seq.length sks /\
  Seq.length shv == Seq.length sks /\
  (forall (j: nat) . j < i ==> Seq.index shv j == key_hash b k0 k1 (Seq.index sks j))

let hv_ok_step (b: bytes) (k0 k1: U64.t) (sks: Seq.seq SZ.t) (shv: Seq.seq U64.t) (i: nat) (h: U64.t) : Lemma
  (requires hv_ok b k0 k1 sks shv i /\ i < Seq.length sks /\ h == key_hash b k0 k1 (Seq.index sks i))
  (ensures hv_ok b k0 k1 sks (Seq.upd shv i h) (i + 1))
= ()

(* The initial indices *)

let is_iota (s: Seq.seq SZ.t) (i: nat) : prop =
  i <= Seq.length s /\
  (forall (j: nat) . j < i ==> SZ.v (Seq.index s j) == j)

let is_iota_step (s: Seq.seq SZ.t) (i: nat) (x: SZ.t) : Lemma
  (requires is_iota s i /\ i < Seq.length s /\ SZ.v x == i)
  (ensures is_iota (Seq.upd s i x) (i + 1))
= ()

let iota_pre (s: Seq.seq SZ.t) : Lemma
  (requires is_iota s (Seq.length s))
  (ensures (forall (x: SZ.t) . SP.mem x s ==> ipre (Seq.length s) x) /\ MS.seq_distinct s)
= let prf (x: SZ.t) : Lemma
    (requires SP.mem x s)
    (ensures ipre (Seq.length s) x)
  = let _ = SP.index_mem x s in ()
  in
  Classical.forall_intro (Classical.move_requires prf)

(* The comparator on indices finds the same duplicates as on keys *)

let no_dup_offsets
  (b: bytes) (s0: Seq.seq SZ.t) (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    offsets_match b s0 (Seq.length s0) v /\
    Seq.length s0 == List.Tot.length v
  )
  (ensures no_cc_dup (List.Tot.map fst v) == true <==> MS.seq_no_cmp_dup (key_cmp b) s0)
= Classical.move_requires (offsets_sort_ok b s0) v;
  let l = List.Tot.map fst v in
  let prf2 () : Lemma
    (requires MS.seq_no_cmp_dup (key_cmp b) s0)
    (ensures no_cc_dup l == true)
  = let prf (i j: nat) : Lemma
      (requires i < j /\ j < List.Tot.length l)
      (ensures (i < j /\ j < List.Tot.length l) ==> cc_eq0 (List.Tot.index l i) (List.Tot.index l j) == false)
    = list_index_map fst v i;
      list_index_map fst v j;
      assert (key_cmp b (Seq.index s0 i) (Seq.index s0 j) <> 0)
    in
    Classical.forall_intro_2 (fun i -> Classical.move_requires (prf i));
    no_cc_dup_index l
  in
  Classical.move_requires prf2 ()

#push-options "--z3rlimit 32"

let icmp_no_dup
  (b: bytes) (k0 k1: U64.t) (sks: Seq.seq SZ.t) (shv: Seq.seq U64.t) (sidx: Seq.seq SZ.t)
: Lemma
  (requires
    hv_ok b k0 k1 sks shv (Seq.length sks) /\
    Seq.length sidx == Seq.length sks /\
    is_iota sidx (Seq.length sidx))
  (ensures MS.seq_no_cmp_dup (icmp b sks shv) sidx <==> MS.seq_no_cmp_dup (key_cmp b) sks)
= let prf (i j: nat) : Lemma
    (requires i < j /\ j < Seq.length sks /\ Seq.length sidx == Seq.length sks)
    (ensures i < j /\ j < Seq.length sidx /\ (icmp b sks shv (Seq.index sidx i) (Seq.index sidx j) == 0 <==> key_cmp b (Seq.index sks i) (Seq.index sks j) == 0))
  = key_hash_eq b k0 k1 (Seq.index sks i);
    key_hash_eq b k0 k1 (Seq.index sks j);
    Classical.move_requires (cc_hash k0 k1 (item_at b (SZ.v (Seq.index sks i)))) (item_at b (SZ.v (Seq.index sks j)))
  in
  Classical.forall_intro_2 (fun i -> Classical.move_requires (prf i))

#pop-options

let hash_sort_result
  (b: bytes) (k0 k1: U64.t) (sks: Seq.seq SZ.t) (shv: Seq.seq U64.t) (sidx s1: Seq.seq SZ.t)
  (v: list (raw_data_item & raw_data_item)) (res: bool)
: Lemma
  (requires
    offsets_match b sks (Seq.length sks) v /\
    Seq.length sks == List.Tot.length v /\
    hv_ok b k0 k1 sks shv (Seq.length sks) /\
    Seq.length sidx == Seq.length sks /\
    is_iota sidx (Seq.length sidx) /\
    MS.sort_post (icmp b sks shv) sidx s1 res)
  (ensures res == no_cc_dup (List.Tot.map fst v))
= icmp_props b sks shv;
  iota_pre sidx;
  MS.sort_abort_witness_distinct (icmp b sks shv) sidx;
  icmp_no_dup b k0 k1 sks shv sidx;
  no_dup_offsets b sks v;
  if res then MS.sorted_no_dup (icmp b sks shv) sidx s1
