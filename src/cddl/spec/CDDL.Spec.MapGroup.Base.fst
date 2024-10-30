module CDDL.Spec.MapGroup.Base
open CBOR.Spec.API.Type

module FE = FStar.FunctionalExtensionality
module MPS = CBOR.Spec.API.MapPairSet

let map_group_item : eqtype =
  (cbor_map & cbor_map)

let mps_for_all
  (f: (map_group_item -> bool))
  (m: MPS.t)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> (forall k . MPS.mem k m ==> f k))
= let b = MPS.filter f m = m in // HERE we use the fact that the map pair set is eqtype
  assert (b == true <==> MPS.equal (MPS.filter f m) m);
  b

type map_group_sem_result =
| MapGroupResult of MPS.t
| MapGroupCutFailure

let map_group_post'_prop
  (l: cbor_map)
  (res: MPS.t)
: Tot prop
=
      forall l' .
      MPS.mem l' res ==>  map_group_item_post l l'

let map_group_post'_t (l: cbor_map) : Tot eqtype = (res: MPS.t { map_group_post'_prop l res })

let map_group_post'
  (l: cbor_map)
  (res: MPS.t)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> map_group_post'_prop l res)
= mps_for_all (map_group_item_post l) res

let map_group_post
  (l: cbor_map)
  (res: map_group_sem_result)
: Tot bool
= match res with
  | MapGroupResult res -> map_group_post' l res
  | MapGroupCutFailure -> true

let map_group_codom
  (l: cbor_map)
: Tot Type0
= (res: map_group_sem_result {
      map_group_post l res
  })

let map_group : Type0 =
  FE.restricted_t
    (cbor_map)
    (map_group_codom)

let map_group_always_false : map_group =
  FE.on_dom cbor_map #map_group_codom
    (fun _ -> MapGroupResult MPS.empty)

let map_group_nop : map_group =
  FE.on_dom cbor_map #map_group_codom
    (fun l -> MapGroupResult (MPS.singleton (cbor_map_empty, l)))

let map_group_end : map_group =
  FE.on_dom cbor_map #map_group_codom
    (fun l -> if l = cbor_map_empty then map_group_nop l else map_group_always_false l)

let cbor_map_singleton_inj
  (k1 v1 k2 v2: cbor)
: Lemma
  (requires (cbor_map_singleton k1 v1 == cbor_map_singleton k2 v2))
  (ensures (k1 == k2 /\ v1 == v2))
  [SMTPat (cbor_map_singleton k1 v1); SMTPat (cbor_map_singleton k2 v2)]
= assert (forall x . cbor_map_mem x (cbor_map_singleton k1 v1) ==> x == (k1, v1));
  assert (forall x . cbor_map_mem x (cbor_map_singleton k2 v2) ==> x == (k2, v2))

unfold
let map_group_match_item_witness_pred (key value: typ) (l: cbor_map) (l': cbor_map & cbor_map) (x: cbor & cbor) : Tot prop =
  map_group_item_post l l' /\
  fst l' == cbor_map_singleton (fst x) (snd x) /\
  key (fst x) /\
  value (snd x)

let map_group_match_item_witness_pred_inj (key value: typ) (l: cbor_map) (l': cbor_map & cbor_map) (x1 x2: (cbor & cbor)) : Lemma
  (requires (map_group_match_item_witness_pred key value l l' x1 /\ map_group_match_item_witness_pred key value l l' x2))
  (ensures (x1 == x2))
= ()

let map_group_match_item_witness_bool (key value: typ) (l: cbor_map) (l': cbor_map & cbor_map) (x: cbor & cbor) : Pure bool
  (requires True)
  (ensures fun b -> b <==> map_group_match_item_witness_pred key value l l' x)
= map_group_item_post l l' &&
  fst l' = cbor_map_singleton (fst x) (snd x) &&
  key (fst x) &&
  value (snd x)

(*
let pred2_equiv_trans
  (#t #t': Type)
  (p1 p2 p3: t -> t' -> prop)
: Lemma
  (requires (
    (forall x x' . p1 x x' <==> p2 x x') /\
    (forall x x' . p2 x x' <==> p3 x x')
  ))
  (ensures (
    (forall x x' . p1 x x' <==> p3 x x')
  ))
= ()
*)

let mps_union_assoc
  (x1 x2 x3: MPS.t)
: Lemma
  (ensures (MPS.union (MPS.union x1 x2) x3 == MPS.union x1 (MPS.union x2 x3)))
  [SMTPatOr [
    [SMTPat (MPS.union (MPS.union x1 x2) x3)];
    [SMTPat (MPS.union x1 (MPS.union x2 x3))];
  ]]
= assert (MPS.equal (MPS.union (MPS.union x1 x2) x3) (MPS.union x1 (MPS.union x2 x3)))

let mps_union_comm
  (x1 x2: MPS.t)
: Lemma
  (ensures (MPS.union x1 x2 == MPS.union x2 x1))
  [SMTPat (MPS.union x1 x2)]
= assert (MPS.equal (MPS.union x1 x2) (MPS.union x2 x1))

let map_group_match_item_op
  (key value: typ)
  (l: cbor_map)
  (accu: map_group_post'_t l)
  (k: cbor)
: Tot (map_group_post'_t l)
= match cbor_map_get l k with
  | None -> accu
  | Some v ->
    if key k && value v
    then
      let l1 = cbor_map_singleton k v in
      let l2 = cbor_map_sub l l1 in
      MPS.union accu (MPS.singleton (l1, l2))
    else accu

let map_group_match_item_op_implies
  (key value: typ)
  (l: cbor_map)
  (accu: map_group_post'_t l)
  (k: cbor)
  (l': map_group_item)
: Lemma
  (requires (
    MPS.mem l' (map_group_match_item_op key value l accu k)
  ))
  (ensures (MPS.mem l' accu \/ exists x . map_group_match_item_witness_pred key value l l' (k, x)))
= ()

let map_group_match_item_op_implies_recip
  (key value: typ)
  (l: cbor_map)
  (accu: map_group_post'_t l)
  (k: cbor)
  (l': map_group_item)
  (x: cbor)
: Lemma
  (requires (
    map_group_match_item_witness_pred key value l l' (k, x)
  ))
  (ensures (MPS.mem l' (map_group_match_item_op key value l accu k)))
= assert (cbor_map_defined k l);
  let Some v = cbor_map_get l k in
  assert (x == v);
  assert (key k);
  assert (value v);
  assert (cbor_map_equal (fst l') (cbor_map_singleton k v));
  assert (cbor_map_equal (snd l') (cbor_map_sub l (fst l')))

let map_group_match_item_op_eq
  (key value: typ)
  (l: cbor_map)
  (accu: map_group_post'_t l)
  (k: cbor)
  (l': map_group_item)
: Lemma
  (ensures (MPS.mem l' (map_group_match_item_op key value l accu k) <==> (MPS.mem l' accu \/ exists x . map_group_match_item_witness_pred key value l l' x /\ fst x == k)))
  [SMTPat (MPS.mem l' (map_group_match_item_op key value l accu k))]
= Classical.forall_intro (Classical.move_requires (map_group_match_item_op_implies_recip key value l accu k l'))

let rec list_fold_map_group_match_item_op_eq
  (key value: typ)
  (l: cbor_map)
  (accu: map_group_post'_t l)
  (ls: list cbor)
  (l': map_group_item)
: Lemma
  (ensures (MPS.mem l' (List.Tot.fold_left (map_group_match_item_op key value l) accu ls) <==> (MPS.mem l' accu \/ exists x . map_group_match_item_witness_pred key value l l' x /\ List.Tot.memP (fst x) ls)))
  (decreases ls)
  [SMTPat (MPS.mem l' (List.Tot.fold_left (map_group_match_item_op key value l) accu ls))]
= match ls with
  | [] -> ()
  | a :: q -> list_fold_map_group_match_item_op_eq key value l (map_group_match_item_op key value l accu a) q l'

let map_group_match_item' (key value: typ) (l: cbor_map) : map_group_post'_t l =
  cbor_map_fold (map_group_match_item_op key value l) MPS.empty l

let map_group_match_item'_eq (key value: typ) (l: cbor_map) (l': map_group_item) : Lemma
  (ensures (MPS.mem l' (map_group_match_item' key value l) <==> exists x . map_group_match_item_witness_pred key value l l' x))
  [SMTPat (MPS.mem l' (map_group_match_item' key value l))]
= cbor_map_fold_eq (map_group_match_item_op key value l) MPS.empty l (cbor_map_key_list l)

let mps_singleton_elim
  (s: MPS.t)
: Pure map_group_item
    (requires MPS.cardinality s == 1)
    (ensures fun x -> MPS.equal s (MPS.singleton x))
= let l = Ghost.hide (MPS.as_list s) in
  assert (forall x . List.Tot.memP x l <==> MPS.mem x s);
  assert (List.Tot.length l == 1);
  assert (forall x . MPS.mem x s <==> x == List.Tot.hd l);
  let t = (x: map_group_item { MPS.mem x s }) in
  let f (accu: option t) (x: map_group_item) : Tot (option t) =
    if MPS.mem x s
    then Some x
    else accu
  in
  MPS.fold_eq f None s l;
  let ores : option t = MPS.fold f None s in
  assert (Some? ores);
  Some?.v ores

let cbor_map_singleton_elim
  (s: cbor_map)
: Pure (cbor & cbor)
    (requires cbor_map_length s == 1)
    (ensures fun x -> cbor_map_equal s (cbor_map_singleton (fst x) (snd x)))
= let l = Ghost.hide (cbor_map_key_list s) in
  assert (forall x . List.Tot.memP x l <==> cbor_map_defined x s);
  assert (List.Tot.length l == 1);
  assert (forall x . cbor_map_defined x s <==> x == List.Tot.hd l);
  let t = (x: cbor { cbor_map_defined x s }) in
  let f (accu: option t) (x: cbor) : Tot (option t) =
    if cbor_map_defined x s
    then Some x
    else accu
  in
  cbor_map_fold_eq f None s l;
  let ores : option t = cbor_map_fold f None s in
  assert (Some? ores);
  let k = Some?.v ores in
  let Some v = cbor_map_get s k in
  (k, v)

let map_group_match_item'_elim (key value: typ) (l: cbor_map) l' : Pure _
  (requires (MPS.mem l' (map_group_match_item' key value l)))
  (ensures (fun x -> map_group_match_item_witness_pred key value l l' x))
= cbor_map_singleton_elim (fst l')

let map_group_match_item_cut_failure_witness_pred (key: typ) (s: MPS.t) (elt: map_group_item) (entry: (cbor & cbor)) : Tot bool =
  let (_, rem) = elt in
  let (k, _) = entry in
  MPS.mem elt s &&
  cbor_map_mem entry rem &&
  key k

let map_group_match_item_cut_pre
  (l: cbor_map)
  (s: map_group_post'_t l)
: Tot (map_group_post'_t l)
= if s = MPS.empty
  then MPS.singleton (cbor_map_empty, l)
  else s

let cbor_map_exists_op
  (f: (cbor & cbor) -> bool)
  (l: cbor_map)
  (accu: bool)
  (k: cbor)
: Tot bool
= match cbor_map_get l k with
  | None -> accu
  | Some v -> accu || f (k, v)

let rec list_fold_cbor_map_exists_op_true
  (f: (cbor & cbor) -> bool)
  (l: cbor_map)
  (l': list cbor)
: Lemma
  (List.Tot.fold_left (cbor_map_exists_op f l) true l' == true)
= match l' with
  | [] -> ()
  | _ :: q -> list_fold_cbor_map_exists_op_true f l q

let rec list_fold_cbor_map_exists_op_eq
  (f: (cbor & cbor) -> bool)
  (l: cbor_map)
  (l': list cbor)
: Lemma
  (List.Tot.fold_left (cbor_map_exists_op f l) false l' == true <==> (exists k . List.Tot.memP k l' /\ cbor_map_exists_op f l false k))
= match l' with
  | [] -> ()
  | a :: q ->
    if cbor_map_exists_op f l false a
    then list_fold_cbor_map_exists_op_true f l q
    else list_fold_cbor_map_exists_op_eq f l q

let cbor_map_exists 
  (f: (cbor & cbor) -> bool)
  (l: cbor_map)
: Tot bool
= cbor_map_fold (cbor_map_exists_op f l) false l

let cbor_map_exists_eq
  (f: (cbor & cbor) -> bool)
  (l: cbor_map)
: Lemma
  (ensures (cbor_map_exists f l <==> exists k . cbor_map_exists_op f l false k))
  [SMTPat (cbor_map_exists f l)]
= let l' = cbor_map_key_list l in
  list_fold_cbor_map_exists_op_eq f l l';
  cbor_map_fold_eq (cbor_map_exists_op f l) false l l'

let mps_exists_op
  (f: map_group_item -> bool)
  (accu: bool)
  (k: map_group_item)
: Tot bool
= accu || f k

let rec list_fold_mps_exists_op_true
  (f: map_group_item -> bool)
  (l': list map_group_item)
: Lemma
  (List.Tot.fold_left (mps_exists_op f) true l' == true)
= match l' with
  | [] -> ()
  | _ :: q -> list_fold_mps_exists_op_true f q

let rec list_fold_mps_exists_op_eq
  (f: map_group_item -> bool)
  (l': list map_group_item)
: Lemma
  (List.Tot.fold_left (mps_exists_op f) false l' == true <==> (exists k . List.Tot.memP k l' /\ f k))
= match l' with
  | [] -> ()
  | a :: q ->
    if mps_exists_op f false a
    then list_fold_mps_exists_op_true f q
    else list_fold_mps_exists_op_eq f q

let mps_exists 
  (f: map_group_item -> bool)
  (l: MPS.t)
: Tot bool
= MPS.fold (mps_exists_op f) false l

let mps_exists_eq
  (f: map_group_item -> bool)
  (l: MPS.t)
: Lemma
  (ensures (mps_exists f l <==> exists k . MPS.mem k l /\ f k))
  [SMTPat (mps_exists f l)]
= let l' = MPS.as_list l in
  list_fold_mps_exists_op_eq f l';
  MPS.fold_eq (mps_exists_op f) false l l'

let map_group_match_item_cut_exists_pred
  (key: typ) (s: MPS.t) (elt: map_group_item)
: Tot bool
= cbor_map_exists (map_group_match_item_cut_failure_witness_pred key s elt) (snd elt)

let map_group_match_item_cut
  (key: typ)
  (l: cbor_map)
  (s: map_group_post'_t l)
: Tot map_group_sem_result
= 
  let s' = map_group_match_item_cut_pre l s in
  if mps_exists (map_group_match_item_cut_exists_pred key s') s'
  then MapGroupCutFailure
  else MapGroupResult s

let map_group_match_item (cut: bool) (key value: typ) : map_group =
  FE.on_dom cbor_map #map_group_codom
    (fun l ->
      let s = map_group_match_item' key value l in
      if cut
      then map_group_match_item_cut key l s
      else MapGroupResult s
    )

let map_group_match_item_ext
  cut key value key' value'
= 
  assert (forall x . map_group_match_item' key value x `MPS.equal` map_group_match_item' key' value' x);
  assert (forall s . mps_exists (map_group_match_item_cut_exists_pred key s) s <==> mps_exists (map_group_match_item_cut_exists_pred key' s) s);
  assert (map_group_match_item cut key value `FE.feq` map_group_match_item cut key' value')

(*
let gset_map_witness_pred (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) x2 x1 : GTot prop =
  x2 == f x1 /\ FStar.GSet.mem x1 s

let gset_map (#t1 #t2: Type) (f: t1 -> GTot t2) (s: FStar.GSet.set t1) : FStar.GSet.set t2 =
  FStar.GSet.comprehend (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (exists x1 .
    gset_map_witness_pred f s x2 x1
  ))

let gset_map_elim #t1 #t2 (f: t1 -> GTot t2) (s: FStar.GSet.set t1) (x2: t2) : Ghost t1
  (requires FStar.GSet.mem x2 (gset_map f s))
  (ensures fun x1 -> gset_map_witness_pred f s x2 x1)
= FStar.IndefiniteDescription.indefinite_description_ghost _ (gset_map_witness_pred f s x2)
*)

let map_group_match_item_alt_pred
  (key value: typ)
  (l: cbor_map)
  (kv: (cbor & cbor))
: Tot bool
= cbor_map_mem kv l &&
  matches_map_group_entry key value kv

(*
let map_group_match_item_alt_r
  l0
  (ll, lr)
= (ll, ghost_map_union l0 lr)

let map_group_match_item_alt (key value: typ) (l: cbor_map) : GTot _ =
  match maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) with
  | None -> FStar.GSet.empty
  | Some kv ->
    let l1 = ghost_map_singleton (fst kv) (snd kv) in
    let l2 = ghost_map_sub l l1 in
    FStar.GSet.union (FStar.GSet.singleton (l1, l2))
      (gset_map (map_group_match_item_alt_r l1) (map_group_match_item' key value l2))

#restart-solver
let map_group_match_item_alt_map_group_match_item
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item_alt key value l) ==> FStar.GSet.mem l' (map_group_match_item' key value l))
=
  if FStar.GSet.mem l' (map_group_match_item_alt key value l)
  then begin
    let Some kv = maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) in
    let l1 = ghost_map_singleton (fst kv) (snd kv) in
    let l2 = ghost_map_sub l l1 in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (l' == (l1, l2))
    then assert (map_group_match_item_witness_pred key value l l' kv)
    else begin
      let x = gset_map_elim (map_group_match_item_alt_r l1) (map_group_match_item' key value l2) l' in
      let kv' = map_group_match_item_elim key value l2 x in
      ghost_map_union_assoc l1 (fst x) (snd x);
      ghost_map_disjoint_union_comm l1 (fst x);
      ghost_map_union_assoc (fst x) l1 (snd x);
      assert (map_group_match_item_witness_pred key value l l' kv')
    end
  end

let map_group_match_item_map_group_match_item_alt
  (key value: typ) (l: cbor_map) l'
: Lemma
  (FStar.GSet.mem l' (map_group_match_item' key value l) ==> FStar.GSet.mem l' (map_group_match_item_alt key value l))
= if FStar.GSet.mem l' (map_group_match_item' key value l)
  then begin
    let kv' = map_group_match_item_elim key value l l' in
    assert (map_group_match_item_alt_pred key value l kv');
    let Some kv = maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value l) in
    let l1 = ghost_map_singleton (fst kv) (snd kv) in
    let l2 = ghost_map_sub l l1 in
    if FStar.StrongExcludedMiddle.strong_excluded_middle (kv == kv')
    then ghost_map_disjoint_union_simpl_l l1 l2 (snd l')
    else begin
      assert (ghost_map_mem kv' l2);
      let l2' = snd l' `ghost_map_sub` l1 in
      ghost_map_disjoint_union_comm l1 l2';
      ghost_map_union_assoc (fst l') l1 l2';
      ghost_map_disjoint_union_comm (fst l') l1;
      ghost_map_union_assoc l1 (fst l') l2';
      ghost_map_disjoint_union_simpl_l l1 (fst l' `ghost_map_union` l2') l2;
      assert (map_group_match_item_witness_pred key value l2 (fst l', l2') kv');
      assert (gset_map_witness_pred (map_group_match_item_alt_r l1) (map_group_match_item' key value l2) l' (fst l', l2'))
    end
  end
*)

let map_group_equiv
  (m1 m2: map_group)
: Tot prop
= forall l . match m1 l, m2 l with
  | MapGroupCutFailure, MapGroupCutFailure -> True
  | MapGroupResult s1, MapGroupResult s2 -> s1 `MPS.equal` s2
  | _ -> False

let map_group_equiv_eq
  (m1 m2: map_group)
: Lemma
  (map_group_equiv m1 m2 <==> m1 == m2)
  [SMTPat (map_group_equiv m1 m2)]
= assert (FE.feq m1 m2 <==> m1 == m2)

(*
let map_group_match_item_alt_correct
  (key value: typ) (l: cbor_map)
: Lemma
  (map_group_match_item_alt key value l == map_group_match_item' key value l)
= Classical.forall_intro (map_group_match_item_map_group_match_item_alt key value l);
  Classical.forall_intro (map_group_match_item_alt_map_group_match_item key value l);
  assert (map_group_match_item_alt key value l `FStar.GSet.equal` map_group_match_item' key value l)
*)

let map_group_choice (m1 m2: map_group) : map_group =
  FE.on_dom cbor_map #map_group_codom (fun l ->
    // greedy PEG semantics for `//`
    match m1 l with
    | MapGroupCutFailure -> MapGroupCutFailure
    | MapGroupResult res1 ->
      if res1 = MPS.empty
      then m2 l
      else MapGroupResult res1
  )

let map_group_choice_assoc
  (g1 g2 g3: map_group)
: Lemma
  ((g1 `map_group_choice` g2) `map_group_choice` g3 == g1 `map_group_choice` (g2 `map_group_choice` g3))
= assert (((g1 `map_group_choice` g2) `map_group_choice` g3) `map_group_equiv` (g1 `map_group_choice` (g2 `map_group_choice` g3)))

let map_group_choice_always_false_l
  (g: map_group)
: Lemma
  (map_group_choice map_group_always_false g == g)
= assert (map_group_choice map_group_always_false g `map_group_equiv` g)

let map_group_choice_always_false_r
  (g: map_group)
: Lemma
  (map_group_choice g map_group_always_false == g)
= assert (map_group_choice g map_group_always_false `map_group_equiv` g)

let map_group_concat_witness_pred
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (cbor_map & cbor_map))
  (l1l2: ((cbor_map & cbor_map) & (cbor_map & cbor_map)))
: Tot prop
= let (l1, l2) = l1l2 in
  MapGroupResult? (m1 l) /\
  MPS.mem l1 (MapGroupResult?._0 (m1 l)) /\
  MapGroupResult? (m2 (snd l1)) /\
  MPS.mem l2 (MapGroupResult?._0 (m2 (snd l1))) /\
  fst l' `cbor_map_equal` (fst l1 `cbor_map_union` fst l2) /\
  snd l' == snd l2

let cbor_map_disjoint_union_elim
  (m m1 m2: cbor_map)
: Lemma
  (requires cbor_map_disjoint m (m1 `cbor_map_union` m2))
  (ensures cbor_map_disjoint m m1 /\ cbor_map_disjoint m m2)
= ()

let cbor_map_disjoint_union_intro
  (m m1 m2: cbor_map)
: Lemma
  (requires cbor_map_disjoint m m1 /\ cbor_map_disjoint m m2)
  (ensures cbor_map_disjoint m (m1 `cbor_map_union` m2))
= ()

#push-options "--z3rlimit 16"

#restart-solver
let map_group_concat_witness_pred_correct
  (m1 m2: map_group)
  (l: cbor_map)
  (l': (cbor_map & cbor_map))
  (l1l2: ((cbor_map & cbor_map) & (cbor_map & cbor_map)))
: Lemma
  (requires map_group_concat_witness_pred m1 m2 l l' l1l2)
  (ensures map_group_item_post l l' /\
    fst (fst l1l2) `cbor_map_disjoint` fst (snd l1l2))
  [SMTPat (map_group_concat_witness_pred m1 m2 l l' l1l2)]
= let (l1, l2) = l1l2 in
  cbor_map_union_assoc (fst l1) (fst l2) (snd l2);
  assert ((fst l1 `cbor_map_union` fst l2) `cbor_map_union` snd l2 == l);
  assert (fst l1 `cbor_map_disjoint` snd l1);
  assert (snd l1 == fst l2 `cbor_map_union` snd l2);
//  cbor_map_disjoint_union_elim (fst l1) (fst l2) (snd l2);
  assert (fst l1 `cbor_map_disjoint` fst l2);
  assert (fst l2 `cbor_map_disjoint` snd l2);
  assert (cbor_map_disjoint (fst l1 `cbor_map_union` fst l2) (snd l2))

#pop-options

let mps_map_op
  (f: (map_group_item -> map_group_item))
  (accu: MPS.t)
  (x: map_group_item)
: Tot MPS.t
= MPS.union accu (MPS.singleton (f x))

let rec list_fold_mps_map_op
  (f: (map_group_item -> map_group_item))
  (accu: MPS.t)
  (l: list map_group_item)
  (x: map_group_item)
: Lemma
  (ensures (MPS.mem x (List.Tot.fold_left (mps_map_op f) accu l) <==> (MPS.mem x accu \/ (exists x' . List.Tot.memP x' l /\ x == f x'))))
  (decreases l)
  [SMTPat (MPS.mem x (List.Tot.fold_left (mps_map_op f) accu l))]
= match l with
  | [] -> ()
  | a :: q -> list_fold_mps_map_op f (mps_map_op f accu a) q x

let mps_map
  (f: (map_group_item -> map_group_item))
  (s: MPS.t)
: Tot MPS.t
= MPS.fold (mps_map_op f) MPS.empty s

let mps_map_eq
  (f: (map_group_item -> map_group_item))
  (s: MPS.t)
  (x: map_group_item)
: Lemma
  (ensures (MPS.mem x (mps_map f s) <==> (exists x' . MPS.mem x' s /\ x == f x')))
  [SMTPat (MPS.mem x (mps_map f s))]
= let l = MPS.as_list s in
  list_fold_mps_map_op f MPS.empty l x;
  MPS.fold_eq (mps_map_op f) MPS.empty s l

let map_group_concat_result_map
  (consumed: cbor_map)
  (x: map_group_item)
: Tot map_group_item
= (cbor_map_union consumed (fst x), snd x)

let map_group_concat_result_op
  (f: cbor_map)
  (m2: map_group)
  (accu: map_group_post'_t f)
  (l: (cbor_map & cbor_map))
: Tot (map_group_post'_t f)
= if map_group_item_post f l
  then
    match m2 (snd l) with
    | MapGroupResult s ->
      MPS.union accu (mps_map (map_group_concat_result_map (fst l)) s)
    | _ -> accu // dummy, since cut failure is determined separately
  else accu // dummy, since elements of l are already supposed to satisfy map_group_item_post f

let map_group_concat_result_post
  (m2: map_group)
  (l1: map_group_item)
  (l': map_group_item)
: Tot prop
= 
    begin match m2 (snd l1) with
    | MapGroupResult s2 -> exists l2 . MPS.mem l2 s2 /\ cbor_map_equal (fst l') (cbor_map_union (fst l1) (fst l2)) /\ cbor_map_equal (snd l') (snd l2)
    | _ -> False
    end

let rec list_fold_map_group_concat_result_op_eq
  (f: cbor_map)
  (m2: map_group)
  (accu: map_group_post'_t f)
  (l: list (cbor_map & cbor_map))
  (l': map_group_item)
: Lemma
  (ensures (MPS.mem l' (List.Tot.fold_left (map_group_concat_result_op f m2) accu l) <==> (MPS.mem l' accu \/ (exists l1 . List.Tot.memP l1 l /\ map_group_item_post f l1 /\ map_group_concat_result_post m2 l1 l'))))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> list_fold_map_group_concat_result_op_eq f m2 (map_group_concat_result_op f m2 accu a) q l'

let map_group_concat_result
  (f: cbor_map)
  (m2: map_group)
  (s: map_group_post'_t f)
: Tot (map_group_post'_t f)
= MPS.fold (map_group_concat_result_op f m2) MPS.empty s

let map_group_concat_result_eq'
  (f: cbor_map)
  (m2: map_group)
  (s: map_group_post'_t f)
  (l: map_group_item)
: Lemma
  (ensures (MPS.mem l (map_group_concat_result f m2 s) <==> exists l1 . MPS.mem l1 s /\ map_group_concat_result_post m2 l1 l))
  [SMTPat (MPS.mem l (map_group_concat_result f m2 s))]
= let ls = MPS.as_list s in
  list_fold_map_group_concat_result_op_eq f m2 MPS.empty ls l;
  MPS.fold_eq (map_group_concat_result_op f m2) MPS.empty s ls

let map_group_is_cut_failure_on
  (m2: map_group)
  (l: map_group_item)
: Tot bool
= MapGroupCutFailure? (m2 (snd l))

let map_group_concat
  (m1 m2: map_group)
: map_group
= FE.on_dom cbor_map #map_group_codom (fun x ->
  match m1 x with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult s ->
    if mps_exists (map_group_is_cut_failure_on m2) s
    then MapGroupCutFailure
    else MapGroupResult (map_group_concat_result x m2 s)
)    

let map_group_concat_cut_failure_eq
  (m1 m2: map_group)
  (l: cbor_map)
: Lemma
  (MapGroupCutFailure? (map_group_concat m1 m2 l) <==> (
    match m1 l with
    | MapGroupCutFailure -> True
    | MapGroupResult s -> exists l1 . MPS.mem l1 s /\ MapGroupCutFailure? (m2 (snd l1))
  ))
= ()

let map_group_concat_result_eq
  (m1 m2: map_group)
  (l: cbor_map)
  (l': map_group_item)
: Lemma
  (match map_group_concat m1 m2 l with
    | MapGroupResult s -> (MPS.mem l' s <==> MapGroupResult? (m1 l) /\ exists l1 . MPS.mem l1 (MapGroupResult?._0 (m1 l)) /\ MapGroupResult? (m2 (snd l1)) /\ exists l2 . MPS.mem l2 (MapGroupResult?._0 (m2 (snd l1))) /\ cbor_map_equal (fst l') (cbor_map_union (fst l1) (fst l2)) /\ cbor_map_equal (snd l') (snd l2))
    | _ -> True
  )
= ()

let map_group_concat_result_intro
  (m1: map_group)
  (m2: map_group)
  (l: cbor_map)
  (l1: map_group_item)
  (l2: map_group_item)
: Lemma
  (requires (
    MapGroupResult? (map_group_concat m1 m2 l) /\ (
    let MapGroupResult s1 = m1 l in
    MPS.mem l1 s1 /\ (
    let MapGroupResult s2 = m2 (snd l1) in
    MPS.mem l2 s2
  ))))
  (ensures (
    match map_group_concat m1 m2 l with
    | MapGroupResult s12 -> MPS.mem (cbor_map_union (fst l1) (fst l2), snd l2) s12
    | _ -> False
  ))
= ()

let map_group_concat_result_intro_implies
  (m1: map_group)
  (m2: map_group)
  (l: cbor_map)
  (sq: squash (MapGroupResult? (map_group_concat m1 m2 l)))
  (l1: map_group_item)
  (l2: map_group_item)
: Lemma
  (ensures (
    match map_group_concat m1 m2 l with
    | MapGroupResult s12 -> 
      let MapGroupResult s1 = m1 l in
      (MPS.mem l1 s1 /\ (
      let MapGroupResult s2 = m2 (snd l1) in
      MPS.mem l2 s2)) ==>
      MPS.mem (cbor_map_union (fst l1) (fst l2), snd l2) s12
    | _ -> False
  ))
= ()

let map_group_concat_elim
  (m1: map_group)
  (m2: map_group)
  (l: cbor_map)
  (l' : map_group_item)
: Ghost (map_group_item & map_group_item)
    (requires (
      match map_group_concat m1 m2 l with
      | MapGroupResult s12 -> MPS.mem l' s12
      | _ -> False
    ))
    (ensures (fun (l1, l2) ->
      match m1 l with
      | MapGroupResult s1 ->
        MPS.mem l1 s1 /\
        begin match m2 (snd l1) with
        | MapGroupResult s2 ->
          MPS.mem l2 s2 /\
          cbor_map_equal (fst l') (cbor_map_union (fst l1) (fst l2)) /\
          cbor_map_equal (snd l') (snd l2)
        | _ -> False
        end
      | _ -> False
    ))
= let l1 = FStar.IndefiniteDescription.indefinite_description_ghost (map_group_item) (fun l1 ->
      MPS.mem l1 (MapGroupResult?._0 (m1 l)) /\ MapGroupResult? (m2 (snd l1)) /\ exists l2 . MPS.mem l2 (MapGroupResult?._0 (m2 (snd l1))) /\ cbor_map_equal (fst l') (cbor_map_union (fst l1) (fst l2)) /\ cbor_map_equal (snd l') (snd l2))
  in
  let l2 = FStar.IndefiniteDescription.indefinite_description_ghost (map_group_item) (fun l2 -> MPS.mem l2 (MapGroupResult?._0 (m2 (snd l1))) /\ cbor_map_equal (fst l') (cbor_map_union (fst l1) (fst l2)) /\ cbor_map_equal (snd l') (snd l2))
  in
  (l1, l2)

let map_group_concat_cut_failure_witness_pred
  (m1 m2: map_group)
  (l: cbor_map)
  (l1: map_group_item)
: Tot prop
= MapGroupResult? (m1 l) /\
  MPS.mem l1 (MapGroupResult?._0 (m1 l)) /\
  MapGroupCutFailure? (m2 (snd l1))

let map_group_equiv_intro
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf12: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult _ -> MPS.mem l' s1
    | _ -> False
    ))
    (ensures (match m2 l with
    | MapGroupResult s2 -> MPS.mem l' s2
    | _ -> True
    ))
  )
  (prf21: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult _, MapGroupResult s2 -> MPS.mem l' s2
    | _ -> False
    ))
    (ensures (match m1 l with
    | MapGroupResult s1 -> MPS.mem l' s1
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= Classical.forall_intro prf0;
  Classical.forall_intro_2 (fun l l' -> Classical.move_requires (prf12 l) l');
  Classical.forall_intro_2 (fun l l' -> Classical.move_requires (prf21 l) l')

let map_group_equiv_intro_equiv
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf: (l: cbor_map) ->
    (l': _) ->
    Lemma
    (requires (
      MapGroupResult? (m1 l) /\ MapGroupResult? (m2 l)
    ))
    (ensures (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult s2 -> (MPS.mem l' s1 <==> MPS.mem l' s2)
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= map_group_equiv_intro m1 m2 prf0 (fun l l' -> prf0 l; prf l l') (fun l l' -> prf0 l; prf l l')

let map_group_equiv_intro_equiv_rec
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> 
    (prf: (
      (l1: cbor_map { cbor_map_length l1 < cbor_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { cbor_map_length l1 < cbor_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires (
      MapGroupResult? (m1 l) /\ MapGroupResult? (m2 l)
    ))
    (ensures (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult s2 -> (MPS.mem l' s1 <==> MPS.mem l' s2)
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= let rec prf'
      (l: cbor_map)
  : Lemma
      (ensures (m1 l == m2 l))
      (decreases (cbor_map_length l))
  = prf0 l prf';
    match m1 l with
    | MapGroupCutFailure -> ()
    | MapGroupResult s1 ->
      Classical.forall_intro (Classical.move_requires (prf l prf'));
      assert (s1 `MPS.equal` MapGroupResult?._0 (m2 l))
  in
  map_group_equiv_intro_equiv m1 m2 (fun l -> prf' l) (fun l _ -> prf' l)

let map_group_equiv_intro_rec
  (m1 m2: map_group)
  (prf0: (l: cbor_map) -> 
    (prf: (
      (l1: cbor_map { cbor_map_length l1 < cbor_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    Lemma (MapGroupCutFailure? (m1 l) == MapGroupCutFailure? (m2 l)))
  (prf12: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { cbor_map_length l1 < cbor_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult s1, MapGroupResult _ -> MPS.mem l' s1
    | _ -> False
    ))
    (ensures (match m2 l with
    | MapGroupResult s2 -> MPS.mem l' s2
    | _ -> True
    ))
  )
  (prf21: (l: cbor_map) ->
    (prf: (
      (l1: cbor_map { cbor_map_length l1 < cbor_map_length l }) -> Lemma
      (m1 l1 == m2 l1)
    )) ->
    (l': _) ->
    Lemma
    (requires (match m1 l, m2 l with
    | MapGroupResult _, MapGroupResult s2 -> MPS.mem l' s2
    | _ -> False
    ))
    (ensures (match m1 l with
    | MapGroupResult s1 -> MPS.mem l' s1
    | _ -> True
    ))
  )
: Lemma
  (map_group_equiv m1 m2)
= map_group_equiv_intro_equiv_rec m1 m2 prf0 (fun l prf l' ->
    Classical.move_requires (prf12 l prf) l';
    Classical.move_requires (prf21 l prf) l'
  )

let cbor_map_disjoint_union_assoc_domain
  (f1 f2 f3: cbor_map)
: Lemma
  (ensures (
    (f1 `cbor_map_disjoint` f2 /\ (f1 `cbor_map_union` f2) `cbor_map_disjoint` f3) <==>
      (f2 `cbor_map_disjoint` f3 /\ f1 `cbor_map_disjoint` (f2 `cbor_map_union` f3))
  ))
= ()

let cbor_map_disjoint_union_assoc
  (f1 f2 f3: cbor_map)
: Lemma
  (requires
      (f1 `cbor_map_disjoint` f2 /\ (f1 `cbor_map_union` f2) `cbor_map_disjoint` f3) \/
      (f2 `cbor_map_disjoint` f3 /\ f1 `cbor_map_disjoint` (f2 `cbor_map_union` f3))
  )
  (ensures
    (f1 `cbor_map_union` (f2 `cbor_map_union` f3) == (f1 `cbor_map_union` f2) `cbor_map_union` f3)
  )
= assert ((f1 `cbor_map_union` (f2 `cbor_map_union` f3)) `cbor_map_equal` ((f1 `cbor_map_union` f2) `cbor_map_union` f3))

#push-options "--z3rlimit 32 --ifuel 8"

#restart-solver
let map_group_concat_assoc' (m1 m2 m3: map_group) : Lemma
  (map_group_concat m1 (map_group_concat m2 m3) `map_group_equiv` map_group_concat (map_group_concat m1 m2) m3)
= map_group_equiv_intro
    (map_group_concat m1 (map_group_concat m2 m3))
    (map_group_concat (map_group_concat m1 m2) m3)
    (fun l -> match map_group_concat (map_group_concat m1 m2) m3 l with
        | MapGroupCutFailure -> ()
        | _ -> Classical.forall_intro_2 (map_group_concat_result_intro_implies m1 m2 l ())
    )
    (fun l l' ->
      let (l1, l23) = map_group_concat_elim m1 (map_group_concat m2 m3) l l' in
      let (l2, l3) = map_group_concat_elim m2 m3 (snd l1) l23 in
      map_group_concat_result_intro_implies m1 m2 l () l1 l2;
      let l12 : map_group_item = (cbor_map_union (fst l1) (fst l2), snd l2) in
      map_group_concat_result_intro_implies (map_group_concat m1 m2) m3 l () l12 l3;
      let l_ : map_group_item = (cbor_map_union (fst l12) (fst l3), snd l3) in
      assert (cbor_map_equal (fst l_) (fst l'));
      assert (cbor_map_equal (snd l_) (snd l'))
    )
    (fun l l' ->
      let (l12, l3) = map_group_concat_elim (map_group_concat m1 m2) m3 l l' in
      let (l1, l2) = map_group_concat_elim m1 m2 l l12 in
      map_group_concat_result_intro_implies m2 m3 (snd l1) () l2 l3;
      let l23 : map_group_item = ((cbor_map_union (fst l2) (fst l3), snd l3) <: (cbor_map & cbor_map)) in
      map_group_concat_result_intro_implies m1 (map_group_concat m2 m3) l () l1 l23;
      let l_ : map_group_item = (cbor_map_union (fst l1) (fst l23), snd l23) in
      assert (cbor_map_equal (fst l_) (fst l'));
      assert (cbor_map_equal (snd l_) (snd l'))
    )

#pop-options

let map_group_concat_assoc m1 m2 m3 =
  map_group_concat_assoc' m1 m2 m3

#restart-solver
let map_group_concat_nop_l
  (m: map_group)
: Lemma
  (map_group_concat map_group_nop m == m)
= map_group_equiv_intro
    (map_group_concat map_group_nop m)
    m
    (fun l -> match m l with
    | MapGroupCutFailure -> assert (map_group_concat_cut_failure_witness_pred map_group_nop m l (cbor_map_empty, l))
    | MapGroupResult _ -> ()
    )
    (fun l l' ->
      let (l1, l2) = map_group_concat_elim map_group_nop m l l' in
      assert (fst l' `cbor_map_equal` fst l2)
    )
    (fun l l' ->
      assert (map_group_concat_witness_pred map_group_nop m l l' ((cbor_map_empty, l), l'))
    )

let map_group_concat_nop_r
  (m: map_group)
: Lemma
  (map_group_concat m map_group_nop == m)
= map_group_equiv_intro
    (map_group_concat m map_group_nop)
    m
    (fun _ -> ())
    (fun l l' ->
      let (l1, l2) = map_group_concat_elim m map_group_nop l l' in
      assert (fst l' `cbor_map_equal` fst l1)
    )
    (fun l l' -> 
      assert (map_group_concat_witness_pred m map_group_nop l l' (l', (cbor_map_empty, snd l')))
    )

let map_group_concat_always_false
  (m: map_group)
: Lemma
  (map_group_concat map_group_always_false m == map_group_always_false)
= map_group_equiv_intro_equiv
    (map_group_concat map_group_always_false m)
    map_group_always_false
    (fun _ -> ())
    (fun _ _ -> ())

let bound_map_group
  (l0: cbor_map)
  (m: (l: cbor_map { cbor_map_length l < cbor_map_length l0 }) ->
  Pure _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: map_group
= FE.on_dom cbor_map #map_group_codom
    (fun l -> if cbor_map_length l >= cbor_map_length l0 then map_group_nop l else m l)

let bound_map_group_ext
  (l0: cbor_map)
  (m1 m2: (l: cbor_map { cbor_map_length l < cbor_map_length l0 }) ->
  Pure _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
: Lemma
  (requires forall (l: cbor_map { cbor_map_length l < cbor_map_length l0 }) .
    m1 l == m2 l
  )
  (ensures bound_map_group l0 m1 == bound_map_group l0 m2)
= map_group_equiv_intro (bound_map_group l0 m1) (bound_map_group l0 m2)
    (fun l -> ())
    (fun l l' -> ())
    (fun l l' -> ())

let bound_map_group_ext'
  (l0: cbor_map)
  (m1 m2: (l: cbor_map { cbor_map_length l < cbor_map_length l0 }) ->
  Pure _
    (requires True)
    (ensures fun l' -> map_group_post l l')
  )
  (prf: (l: cbor_map { cbor_map_length l < cbor_map_length l0 }) -> Lemma
    (m1 l == m2 l)
  )
: Lemma
  (ensures bound_map_group l0 m1 == bound_map_group l0 m2)
= Classical.forall_intro prf;
  bound_map_group_ext l0 m1 m2

#restart-solver
let map_group_concat_eq_r
  (m1 m2 m2': map_group)
  (l: cbor_map)
  (prf: (l1: _) -> Lemma
    (requires (match m1 l with
    | MapGroupResult s -> MPS.mem l1 s
    | _ -> False
    ))
    (ensures (m2 (snd l1) == m2' (snd l1)))
  )
: Lemma
  ((m1 `map_group_concat` m2) l == (m1 `map_group_concat` m2') l)
= Classical.forall_intro (Classical.move_requires prf);
  begin match (m1 `map_group_concat` m2) l, (m1 `map_group_concat` m2') l with
  | MapGroupResult s1, MapGroupResult s2 -> assert (s1 `MPS.equal` s2)
  | _ -> ()
  end

let map_group_is_productive
  (m: map_group)
: Tot prop
=
  forall l . match m l with
  | MapGroupCutFailure -> True
  | MapGroupResult s -> forall l' . MPS.mem l' s ==> cbor_map_length (snd l') < cbor_map_length l

let map_group_is_productive_always_false = ()

let map_group_is_productive_match_item
  (cut: bool)
  (key value: typ)
: Lemma
  (map_group_is_productive (map_group_match_item cut key value))
= ()

let map_group_is_productive_choice
  (m1 m2: map_group)
: Lemma
  (requires (
    map_group_is_productive m1 /\
    map_group_is_productive m2
  ))
  (ensures (
    map_group_is_productive (m1 `map_group_choice` m2)
  ))
= ()

#push-options "--z3rlimit 16"

#restart-solver
let map_group_is_productive_concat
  (m1 m2: map_group)
: Lemma
  (requires (
    map_group_is_productive m1 \/
    map_group_is_productive m2
  ))
  (ensures (
    map_group_is_productive (m1 `map_group_concat` m2)
  ))
= ()

#pop-options

let map_group_is_productive_concat_bound
  (l0: cbor_map)
  (m1: map_group { map_group_is_productive m1 })
  (l1: cbor_map { cbor_map_length l1 <= cbor_map_length l0 })
  (m2: map_group)
: Lemma
  ((m1 `map_group_concat` bound_map_group l0 m2) l1 == (m1 `map_group_concat` m2) l1)
= map_group_concat_eq_r
    m1 (bound_map_group l0 m2) m2 l1 (fun _ -> ())

// greedy PEG semantics for `*`
let rec map_group_zero_or_more'
  (m: map_group)
  (l: cbor_map)
: Tot (l': _ {
    map_group_post l l'
  })
  (decreases (cbor_map_length l))
= match m l with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult res1 ->
    if res1 = MPS.empty
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l

let map_group_zero_or_more m =
  FE.on_dom cbor_map #map_group_codom (map_group_zero_or_more' m)

let map_group_zero_or_more_eq
  (m: map_group)
  (l: cbor_map)
: Lemma
  (ensures (map_group_zero_or_more m l == (match m l with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult res1 ->
    if res1 = MPS.empty
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more m)) l
  )))
  (decreases (cbor_map_length l))
= assert (forall l . map_group_zero_or_more m l == map_group_zero_or_more' m l);
  assert_norm (map_group_zero_or_more' m l == (match m l with
  | MapGroupCutFailure -> MapGroupCutFailure
  | MapGroupResult res1 ->
    if res1 = MPS.empty
    then map_group_nop l
    else map_group_concat m (bound_map_group l (map_group_zero_or_more' m)) l
  ));
  bound_map_group_ext l (map_group_zero_or_more m) (map_group_zero_or_more' m)

#restart-solver
let map_group_match_item_for_eq_none
  (cut: bool)
  (k: cbor)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (requires (
    ~ (cbor_map_defined k l)
  ))
  (ensures (
    map_group_match_item_for cut k ty l == MapGroupResult MPS.empty
  ))
= match map_group_match_item_for cut k ty l with
  | MapGroupCutFailure -> assert False
  | MapGroupResult s -> assert (s `MPS.equal` MPS.empty)

#restart-solver
let map_group_match_item_for_eq
  (k: cbor)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    map_group_match_item_for false k ty l == begin match cbor_map_get l k with
    | Some v ->
      if ty v
      then
        let s = cbor_map_singleton k v in
        MapGroupResult (MPS.singleton (s, l `cbor_map_sub` s))
      else
        MapGroupResult MPS.empty
    | _ -> MapGroupResult MPS.empty
    end
  ))
= let MapGroupResult s = map_group_match_item_for false k ty l in
  match cbor_map_get l k with
  | Some v ->
    if ty v
    then begin
      let m = cbor_map_singleton k v in
      let x : map_group_item = (m, l `cbor_map_sub` m) in
      assert (MPS.mem x s);
      assert (forall mi . MPS.mem mi s ==> cbor_map_equal (fst mi) m /\ cbor_map_equal (snd mi) (snd x));
      assert (MPS.equal s (MPS.singleton x))
    end
    else assert (MPS.equal s MPS.empty)
  | _ -> assert (MPS.equal s MPS.empty)

#restart-solver
let map_group_match_item_for_eq_gen
  (cut: bool)
  (k: cbor)
  (ty: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    map_group_match_item_for cut k ty l == begin match cbor_map_get l k with
    | Some v ->
      if ty v
      then
        let s = cbor_map_singleton k v in
        MapGroupResult (MPS.singleton (s, l `cbor_map_sub` s))
      else if cut
      then MapGroupCutFailure
      else
        MapGroupResult MPS.empty
    | _ -> MapGroupResult MPS.empty
    end
  ))
= map_group_match_item_for_eq k ty l;
  if cut
  then match cbor_map_get l k with
  | None -> ()
  | Some v ->
    let l1 = cbor_map_singleton k v in
    let l2 = l `cbor_map_sub` l1 in
    if ty v
    then ()
    else begin
      assert (map_group_match_item_for false k ty l == MapGroupResult MPS.empty);
      assert (map_group_match_item_cut_pre l MPS.empty == MPS.singleton (cbor_map_empty, l));
      let s = MPS.singleton (cbor_map_empty, l) in
      assert (map_group_match_item_cut_failure_witness_pred (t_literal k) s (cbor_map_empty, l) (k, v));
      assert (map_group_match_item_cut_exists_pred (t_literal k) s (cbor_map_empty, l));
      assert (mps_exists (map_group_match_item_cut_exists_pred (t_literal k) s) s);
      assert (map_group_match_item_for true k ty l == MapGroupCutFailure)
    end

(*
let gset_equal_intro
  (#t: Type)
  (s1 s2: FStar.GSet.set t)
  (prf12: (x: t) -> Lemma
    (requires FStar.GSet.mem x s1)
    (ensures FStar.GSet.mem x s2)
  )
  (prf21: (x: t) -> Lemma
    (requires FStar.GSet.mem x s2)
    (ensures FStar.GSet.mem x s1)
  )
: Lemma
  (s1 == s2)
= Classical.forall_intro (Classical.move_requires prf12);
  Classical.forall_intro (Classical.move_requires prf21);
  assert (s1 `FStar.GSet.equal` s2)
*)

let map_group_match_item_length
  (key value: typ)
  (l: cbor_map)
  l'
: Lemma
  (requires MPS.mem l' (map_group_match_item' key value l))
  (ensures cbor_map_length (snd l') < cbor_map_length l)
  [SMTPat (MPS.mem l' (map_group_match_item' key value l))]
= ()

#restart-solver
let map_group_zero_or_more_zero_or_one_eq
  (m: map_group)
: Lemma
  (map_group_zero_or_more (map_group_zero_or_one m) == map_group_zero_or_more m)
=
  assert ((cbor_map_empty  `cbor_map_union` cbor_map_empty) `cbor_map_equal` cbor_map_empty);
  map_group_equiv_intro_rec
    (map_group_zero_or_more (map_group_zero_or_one m))
    (map_group_zero_or_more m)
    (fun l prf ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m)
    )
    (fun l prf l' ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      assert (~ (map_group_zero_or_one m l == MapGroupResult MPS.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m);
      let (l1, l2) = map_group_concat_elim (map_group_zero_or_one m) (bound_map_group l (map_group_zero_or_more m)) l l' in
      ()
    )
    (fun l prf l' ->
      map_group_zero_or_more_eq (map_group_zero_or_one m) l;
      map_group_zero_or_more_eq m l;
      assert (~ (map_group_zero_or_one m l == MapGroupResult MPS.empty));
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_zero_or_one m)) (map_group_zero_or_more m);
      if MapGroupResult?._0 (m l) = MPS.empty
      then
        assert (map_group_concat_witness_pred (map_group_zero_or_one m) (bound_map_group l (map_group_zero_or_more m)) l l'
          (
            (cbor_map_empty, l),
            (cbor_map_empty, l)
          )
        )
      else
        let (l1, l2) = map_group_concat_elim m (bound_map_group l (map_group_zero_or_more m)) l l' in
        ()
    )

(*
let apply_map_group_det_old (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)
= match m l with
  | MapGroupCutFailure -> MapGroupCutFail
  | MapGroupResult s ->
  if FStar.StrongExcludedMiddle.strong_excluded_middle (s == FStar.GSet.empty)
  then MapGroupFail
  else if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . s == FStar.GSet.singleton x)
  then
    let x = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun x -> s == FStar.GSet.singleton x) in
    MapGroupDet (fst x) (snd x)
  else MapGroupNonDet

let gset_is_singleton (#t: Type) (s: FStar.GSet.set t) (x: t) : Tot prop =
  s == FStar.GSet.singleton x
*)

let apply_map_group_det (m: map_group) (l: cbor_map) : Pure map_group_result
  (requires True)
  (ensures fun r -> map_group_result_prop l r)
= match m l with
  | MapGroupCutFailure -> MapGroupCutFail
  | MapGroupResult s ->
    if s = MPS.empty
    then
      MapGroupFail
    else if MPS.cardinality s = 1
    then
      let x = mps_singleton_elim s in
      MapGroupDet (fst x) (snd x)
    else
      MapGroupNonDet

(*
let apply_map_group_det_eq_old
  (m: map_group)
  (l: cbor_map)
: Lemma
  (apply_map_group_det m l == apply_map_group_det_old m l)
= ()
*)

#restart-solver
let apply_map_group_det_eq_singleton (m: map_group) (l: cbor_map) (x : (_ & _)) : Lemma
  (requires (match m l with
  | MapGroupResult s -> s `MPS.equal` MPS.singleton x
  | _ -> False
  ))
  (ensures (apply_map_group_det m l == MapGroupDet (fst x) (snd x)))
= let MapGroupResult s = m l in
  assert (s == MPS.singleton x);
  if s = MPS.empty
  then assert (x `MPS.mem` MPS.empty)
  else begin
    assert (exists x . s == MPS.singleton x);
    assert (MapGroupDet? (apply_map_group_det m l))
  end

#restart-solver
let apply_map_group_det_eq_map (m1 m2: map_group) (l: cbor_map) : Lemma
  (requires m1 l == m2 l)
  (ensures apply_map_group_det m1 l == apply_map_group_det m2 l)
= match apply_map_group_det m1 l with
  | MapGroupDet c1 l1 -> apply_map_group_det_eq_singleton m2 l (c1, l1)
  | _ -> ()

let apply_map_group_det_always_false (l: cbor_map) : Lemma
  (apply_map_group_det map_group_always_false l == MapGroupFail)
= ()

#restart-solver
let apply_map_group_det_nop (l: cbor_map) : Lemma
  (apply_map_group_det map_group_nop l == MapGroupDet cbor_map_empty l)
= ()

let apply_map_group_det_end l = ()

let apply_map_group_det_map_group_equiv
  m1 m2
= map_group_equiv_intro m1 m2
    (fun l -> ())
    (fun l l' ->
      let MapGroupDet _ s1 = apply_map_group_det m1 l in
      let (k1, l1) = mps_singleton_elim (MapGroupResult?._0 (m1 l)) in
      let (k2, l2) = mps_singleton_elim (MapGroupResult?._0 (m2 l)) in
      assert (l1 == l2);
      cbor_map_equiv k1 k2
    )
    (fun l l' ->
      let MapGroupDet _ s1 = apply_map_group_det m1 l in
      let (k1, l1) = mps_singleton_elim (MapGroupResult?._0 (m1 l)) in
      let (k2, l2) = mps_singleton_elim (MapGroupResult?._0 (m2 l)) in
      assert (l1 == l2);
      cbor_map_equiv k1 k2
    )

let apply_map_group_det_map_group_equiv' (m1 m2: map_group)
  (phi1: (l: _) -> Lemma
    (~ (MapGroupNonDet? (apply_map_group_det m1 l))
  ))
  (phi2: (l: _) -> Lemma
    (apply_map_group_det m1 l == apply_map_group_det m2 l)
  )
: Lemma
  (ensures m1 == m2)
= Classical.forall_intro phi1;
  Classical.forall_intro phi2;
  apply_map_group_det_map_group_equiv m1 m2

#restart-solver
let apply_map_group_det_choice (m1 m2: map_group) (l: cbor_map)
= match apply_map_group_det m1 l with
  | MapGroupFail -> apply_map_group_det_eq_map (m1 `map_group_choice` m2) m2 l
  | _ -> apply_map_group_det_eq_map (m1 `map_group_choice` m2) m1 l

#push-options "--z3rlimit 32"

let apply_map_group_det_concat (m1 m2: map_group) (l: cbor_map) =
  match apply_map_group_det m1 l with
  | MapGroupCutFail -> ()
  | MapGroupFail ->
    assert (m1 l == MapGroupResult MPS.empty);
    assert (forall x . ~ (MPS.mem x (MapGroupResult?._0 (m1 l))));
    assert (match map_group_concat m1 m2 l with
    | MapGroupResult s -> s `MPS.equal` MPS.empty
    | _ -> False)
  | MapGroupDet c1 lr1 ->
    let l1 = mps_singleton_elim (MapGroupResult?._0 (m1 l)) in
    assert ((c1, lr1) `MPS.mem` MPS.singleton l1);
    begin match apply_map_group_det m2 lr1 with
    | MapGroupCutFail -> assert (map_group_concat_cut_failure_witness_pred m1 m2 l l1)
    | MapGroupFail -> assert (match map_group_concat m1 m2 l with
    | MapGroupResult s -> s `MPS.equal` MPS.empty
    | _ -> False)
    | MapGroupDet c2 lr2 ->
      let l2 = mps_singleton_elim (MapGroupResult?._0 (m2 lr1)) in
      assert ((c2, lr2) `MPS.mem` MPS.singleton l2);
      let l0 = (cbor_map_union (fst l1) (fst l2), snd l2) in
      assert (map_group_concat_witness_pred m1 m2 l l0
        (l1, l2)
      );
      assert (MPS.equal (MapGroupResult?._0 (map_group_concat m1 m2 l))
        (MPS.singleton l0)
      );
      assert (map_group_concat m1 m2 l == MapGroupResult (MPS.singleton l0));
      assert (fst l1 == c1);
      assert (fst l2 == c2);
      assert (snd l2 == lr2)
    | MapGroupNonDet ->
      let s2 = MapGroupResult?._0 (m2 lr1) in
      assert (forall x . (List.Tot.memP x (MPS.as_list s2) <==> MPS.mem x s2));
      assert (Nil? (MPS.as_list s2) ==> MPS.equal s2 MPS.empty);
      let l2 = List.Tot.hd (MPS.as_list s2) in
      let l0 = (cbor_map_union (fst l1) (fst l2), snd l2) in
      assert (map_group_concat_witness_pred m1 m2 l l0
        (l1, l2)
      );
      assert (MPS.mem l0 (MapGroupResult?._0 (map_group_concat m1 m2 l)));
      assert (~ (map_group_concat m1 m2 l == MapGroupResult MPS.empty));
      if FStar.StrongExcludedMiddle.strong_excluded_middle (exists x . map_group_concat m1 m2 l == MapGroupResult (MPS.singleton x))
      then begin
        assert (match map_group_concat m1 m2 l with
        |  MapGroupResult s -> s `MPS.equal` MPS.singleton l0
        | _ -> False);
        assume (MPS.equal
          (MapGroupResult?._0 (m2 lr1))
          (MPS.singleton l2)
        )
(*        
          (fun l2' ->
            let l0' = (cbor_map_union (fst l1) (fst l2'), snd l2') in
            assert (map_group_concat_witness_pred m1 m2 l l0'
              (l1, l2')
            );
            assert (MPS.mem l0' (MapGroupResult?._0 (map_group_concat m1 m2 l)));
            assert (l0' == l0);
            cbor_map_disjoint_mem_union' (fst l1) (fst l2') ();
            cbor_map_disjoint_mem_union' (fst l1) (fst l2) ();
            cbor_map_equiv (fst l2') (fst l2);
            assert (l2' == l2)
          )
          (fun _ -> ())
*)          
      end
      else ()
    end
  | _ -> ()

#pop-options

#restart-solver
let apply_map_group_det_match_item_for
  (cut: bool)
  (k: cbor)
  (ty: typ)
  (l: cbor_map)
= map_group_match_item_for_eq_gen cut k ty l;
  match cbor_map_get l k with
  | Some v ->
    if ty v
    then begin
      let l1 = cbor_map_singleton k v in
      let l2 = cbor_map_filter (CBOR.Spec.Util.notp (matches_map_group_entry (t_literal k) ty)) l in
      cbor_map_equiv
        (l `cbor_map_sub` l1)
        l2;
      let MapGroupResult s = map_group_match_item_for cut k ty l in
      assert (MPS.equal s (MPS.singleton (l1, l2)))
    end
    else ()
  | _ -> ()

let map_group_filter
  f
= FE.on_dom cbor_map #map_group_codom (fun l ->
    MapGroupResult (MPS.singleton (cbor_map_filter (CBOR.Spec.Util.notp f) l, cbor_map_filter f l))
  )

let apply_map_group_det_filter
  f l
= ()

#restart-solver
let map_group_filter_filter
  p1 p2
= apply_map_group_det_map_group_equiv'
    (map_group_filter p1 `map_group_concat` map_group_filter p2)
    (map_group_filter (CBOR.Spec.Util.andp p1 p2))
    (fun l -> map_group_is_det_concat (map_group_filter p1) (map_group_filter p2))
    (fun l ->
      let MapGroupDet c1 l1 = apply_map_group_det (map_group_filter p1) l in
      let MapGroupDet c2 l2 = apply_map_group_det (map_group_filter p2) l1 in
      let MapGroupDet c l = apply_map_group_det (map_group_filter (CBOR.Spec.Util.andp p1 p2)) l in
      assert (cbor_map_equal c (cbor_map_union c1 c2));
      assert (cbor_map_equal l l2)
    )

#restart-solver
let map_group_zero_or_one_match_item_filter_matched
  (key value: typ)
  (p: (cbor & cbor) -> Tot bool)
  (l: cbor_map)
  kv l'
: Lemma
  (requires (
    (forall x . p x ==> CBOR.Spec.Util.notp (matches_map_group_entry key value) x) /\
    map_group_item_post l (cbor_map_singleton (fst kv) (snd kv), l') /\
    matches_map_group_entry key value kv
  ))
  (ensures (
    cbor_map_singleton (fst kv) (snd kv) `cbor_map_union` cbor_map_filter (CBOR.Spec.Util.notp p) l' ==
      cbor_map_filter (CBOR.Spec.Util.notp p) l /\
    cbor_map_filter p l' ==
      cbor_map_filter p l
  ))
= let s = cbor_map_singleton (fst kv) (snd kv) in
  cbor_map_disjoint_union_filter (CBOR.Spec.Util.notp p) s l';
  cbor_map_equiv s (cbor_map_filter (CBOR.Spec.Util.notp p) s);
  cbor_map_disjoint_union_filter p s l';
  cbor_map_equiv cbor_map_empty (cbor_map_filter p s)

#push-options "--z3rlimit 128"

#restart-solver
let map_group_zero_or_one_match_item_filter
  key value p
= map_group_equiv_intro
    (map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` map_group_filter p)
    (map_group_filter p)
    (fun _ -> ())
    (fun l l' ->
      let MapGroupResult s = map_group_match_item false key value l in
      if s = MPS.empty
      then map_group_concat_nop_l (map_group_filter p)
      else begin
        let (l1, _) = map_group_concat_elim (map_group_zero_or_one (map_group_match_item false key value)) (map_group_filter p) l l' in
        let kv = map_group_match_item'_elim key value l l1 in
        assert (fst l1 == cbor_map_singleton (fst kv) (snd kv));
//        assert (map_group_filter p (snd l1) == MapGroupResult (MPS.singleton (cbor_map_gr
//        FStar.GSet.singleton (map_group_filter_item p (snd l1))));
        map_group_zero_or_one_match_item_filter_matched key value p l kv (snd l1);
        assert (snd l' == cbor_map_filter p l)
      end
    )
    (fun l l' ->
      let MapGroupResult s = map_group_match_item false key value l in
      if s = MPS.empty
      then map_group_concat_nop_l (map_group_filter p)
      else assume False
(*      
      | Some l1 ->
        let kv = map_group_match_item_elim key value l l1 in
        map_group_zero_or_one_match_item_filter_matched key value p l kv (snd l1);
        assert (map_group_concat_witness_pred (map_group_zero_or_one (map_group_match_item false key value)) (map_group_filter p) l l' (l1, (cbor_map_filter (notp_g p) (snd l1), cbor_map_filter p (snd l1))))
*)
    )

#restart-solver
let map_group_concat_bound_map_group_elim
  (m1 m2: map_group)
  (l1 l2: cbor_map)
  (prf: (l': _) -> Lemma
    (requires (match m1 l1 with
    | MapGroupResult s -> MPS.mem l' s
    | _ -> False
    ))
    (ensures (cbor_map_length (snd l') < cbor_map_length l2))
  )
: Lemma
  ((m1 `map_group_concat` bound_map_group l2 m2) l1 ==
    (m1 `map_group_concat` m2) l1)
= Classical.forall_intro (Classical.move_requires prf);
  match m1 l1 with
  | MapGroupCutFailure -> ()
  | MapGroupResult s ->
    begin match (m1 `map_group_concat` bound_map_group l2 m2) l1, (m1 `map_group_concat` m2) l1 with
    | MapGroupResult s, MapGroupResult s' -> assert (s `MPS.equal` s')
    | _ -> ()
    end

#pop-options

let map_group_concat_eq_l
  (m1 m1' m2: map_group)
  (l: cbor_map)
: Lemma
  (requires (
    m1 l == m1' l
  ))
  (ensures (
    (m1 `map_group_concat` m2) l ==
      (m1' `map_group_concat` m2) l
  ))
= match (m1 `map_group_concat` m2) l, (m1' `map_group_concat` m2) l with
  | MapGroupResult s, MapGroupResult s' -> assert (s `MPS.equal` s')
  | _ -> ()

#restart-solver
let map_group_zero_or_one_bound_match_item_filter
  (key value: typ)
  (l: cbor_map)
: Lemma
  (ensures (
    let p = CBOR.Spec.Util.notp (matches_map_group_entry key value) in
    (map_group_zero_or_one (map_group_match_item false key value) `map_group_concat` bound_map_group l (map_group_filter p)) l == map_group_filter p l
  ))
= let p = CBOR.Spec.Util.notp (matches_map_group_entry key value) in
//  map_group_match_item_alt_correct key value l;
  if not (cbor_map_exists (matches_map_group_entry key value) l)
  then begin
    assert (MPS.equal (map_group_match_item' key value l) MPS.empty);
    map_group_concat_eq_l (map_group_zero_or_one (map_group_match_item false key value)) map_group_nop (bound_map_group l (map_group_filter p)) l;
    map_group_concat_nop_l (bound_map_group l (map_group_filter p));
    cbor_map_equiv
      (cbor_map_filter (CBOR.Spec.Util.notp p) l)
      cbor_map_empty;
    cbor_map_equiv
      (cbor_map_filter p l)
      l
  end
  else begin
//    assert (Some? (gset_is_empty (map_group_match_item' key value l)));
    map_group_concat_bound_map_group_elim
      (map_group_zero_or_one (map_group_match_item false key value))
      (map_group_filter p)
      l l
      (fun _ -> assume False);
    map_group_zero_or_one_match_item_filter key value p
  end

#restart-solver
let map_group_zero_or_one_map_group_match_item_no_cut_nonempty
  (key value: typ)
  (l: cbor_map)
: Lemma
  (~ (map_group_zero_or_one (map_group_match_item false key value) l == MapGroupResult MPS.empty))
= let MapGroupResult s = map_group_match_item false key value l in
  let MapGroupResult s' = map_group_zero_or_one (map_group_match_item false key value) l in
  if s = MPS.empty
  then assert (MPS.mem (cbor_map_empty, l) s')
  else ()

#push-options "--z3rlimit 16"

#restart-solver
let map_group_zero_or_more_match_item_filter (key value: typ) : Lemma
  (ensures
    map_group_zero_or_more (map_group_match_item false key value) == map_group_filter (CBOR.Spec.Util.notp (matches_map_group_entry key value))
  )
= let f = (CBOR.Spec.Util.notp (matches_map_group_entry key value)) in
  map_group_equiv_intro_equiv_rec
    (map_group_zero_or_more (map_group_match_item false key value))
    (map_group_filter (CBOR.Spec.Util.notp (matches_map_group_entry key value)))
    (fun l prf ->
      map_group_zero_or_more_zero_or_one_eq (map_group_match_item false key value);
      map_group_zero_or_more_eq (map_group_zero_or_one (map_group_match_item false key value)) l;
      map_group_zero_or_one_map_group_match_item_no_cut_nonempty key value l;
      Classical.forall_intro prf    
    )
    (fun l prf l' ->
      map_group_zero_or_more_zero_or_one_eq (map_group_match_item false key value);
      map_group_zero_or_more_eq (map_group_zero_or_one (map_group_match_item false key value)) l;
      map_group_zero_or_one_map_group_match_item_no_cut_nonempty key value l;
      Classical.forall_intro prf;
      bound_map_group_ext l (map_group_zero_or_more (map_group_match_item false key value)) (map_group_filter f);
      map_group_zero_or_one_bound_match_item_filter key value l
    )

#pop-options

let eq_trans
  (#t: Type)
  (x1 x2 x3: t)
  (sq12: squash (x1 == x2))
  (sq23: squash (x2 == x3))
: Tot (squash (x1 == x3))
= ()

let apply_map_group_det_ext
  (m1 m2: map_group)
  (l: cbor_map)
: Lemma
  (requires (m1 l == m2 l))
  (ensures (apply_map_group_det m1 l == apply_map_group_det m2 l))
= ()

#restart-solver
let rec map_group_zero_or_more_det
  (g: det_map_group)
  (l: cbor_map)
: Lemma
  (ensures (~ (MapGroupNonDet? (apply_map_group_det (map_group_zero_or_more g) l))))
  (decreases (cbor_map_length l))
= map_group_zero_or_more_eq g l;
  match apply_map_group_det g l with
  | MapGroupDet consumed rem ->
//    cbor_map_length_is_empty consumed;
    if cbor_map_length consumed = 0
    then begin
      assert (cbor_map_equal consumed cbor_map_empty);
      assert (rem == l);
      map_group_concat_eq_r g (bound_map_group l (map_group_zero_or_more g)) map_group_nop l (fun l' -> ());
      assert (map_group_zero_or_more g l == map_group_concat g map_group_nop l);
      map_group_concat_nop_r g;
      assert (map_group_zero_or_more g l == g l);
      apply_map_group_det_ext (map_group_zero_or_more g) g l
    end
    else begin
      assert (cbor_map_length rem < cbor_map_length l);
      map_group_concat_eq_r g (bound_map_group l (map_group_zero_or_more g)) (map_group_zero_or_more g) l (fun l' -> ());
      apply_map_group_det_ext (map_group_zero_or_more g) (map_group_concat g (map_group_zero_or_more g)) l;
      map_group_zero_or_more_det g rem
    end
  | _ -> ()

#restart-solver
let map_group_zero_or_more_map_group_match_item_for
  (cut: bool)
  (key: cbor)
  (value: typ)
: Lemma
  (map_group_zero_or_more (map_group_match_item_for cut key value) ==
    map_group_zero_or_one (map_group_match_item_for cut key value)
  )
= let g = map_group_match_item_for cut key value in
  apply_map_group_det_map_group_equiv0
    (map_group_zero_or_more g)
    (map_group_zero_or_one g)
    (fun l -> map_group_zero_or_more_det g l)
    (fun l ->
      map_group_zero_or_more_eq g l;
      match apply_map_group_det g l with
      | MapGroupCutFail -> ()
      | MapGroupFail -> ()
      | MapGroupDet consumed rem ->
        assert (cbor_map_length rem < cbor_map_length l);
        map_group_concat_eq_r g (bound_map_group l (map_group_zero_or_more g)) map_group_nop l (fun l' ->
          map_group_zero_or_more_eq g (snd l');
          map_group_match_item_for_eq_gen cut key value (snd l');
          assert (cbor_map_get (snd l') key == None)
        );
        assert (map_group_zero_or_more g l == (g `map_group_concat` map_group_nop) l);
        map_group_concat_nop_r g;
        assert (map_group_zero_or_more g l == g l);
        apply_map_group_det_ext (map_group_zero_or_more g) g l
    )

let map_group_fail_shorten_intro
  (g: map_group)
  (prf: (m1: _) -> (m2: _) -> Lemma
    (requires (cbor_map_disjoint m1 m2 /\
      MapGroupFail? (apply_map_group_det g (m1 `cbor_map_union` m2))
    ))
    (ensures MapGroupFail? (apply_map_group_det g m1))
  )
: Lemma
  (map_group_fail_shorten g)
= Classical.forall_intro_2 (fun m1 -> Classical.move_requires (prf m1))

#restart-solver
let map_group_fail_shorten_match_item
  (cut: bool)
  (key value: typ)
: Lemma
  (map_group_fail_shorten (map_group_match_item cut key value))
= map_group_fail_shorten_intro (map_group_match_item cut key value) (fun m1 m2 ->
//    map_group_match_item_alt_correct key value (m1 `cbor_map_union` m2);
//    map_group_match_item_alt_correct key value m1;
    let s12 = map_group_match_item' key value (m1 `cbor_map_union` m2) in
    if s12 = MPS.empty
    then begin
      assert (forall x . map_group_match_item_alt_pred key value m1 x ==> map_group_match_item_alt_pred key value (m1 `cbor_map_union` m2) x);
//      assert (None? (maybe_indefinite_description_ghost (map_group_match_item_alt_pred key value m1)));
      cbor_map_disjoint_mem_union' m1 m2 ();
      assert (forall l entry . map_group_match_item_cut_failure_witness_pred key (MPS.singleton (cbor_map_empty, m1)) l entry ==> begin
        map_group_match_item_cut_failure_witness_pred key (MPS.singleton (cbor_map_empty, m1 `cbor_map_union` m2)) (cbor_map_empty, m1 `cbor_map_union` m2) entry
      end);
      assume False
    end
    else begin
      assert (forall (kv: (cbor & cbor)) .
        let s = cbor_map_singleton (fst kv) (snd kv) in
        MPS.mem (s, (m1 `cbor_map_union` m2) `cbor_map_sub` s) s12
      )
    end
  )

#restart-solver
let rec map_group_zero_or_more_choice'
  (g1 g2: map_group)
  (l: cbor_map)
: Lemma
  (requires (
    map_group_fail_shorten g1 /\
    map_group_is_productive g1 /\
    map_group_is_productive g2
  ))
  (ensures (
    map_group_zero_or_more (g1 `map_group_choice` g2) l == (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) l
  ))
  (decreases (cbor_map_length l))
= let lhs = map_group_zero_or_more (g1 `map_group_choice` g2) l in
  let rhs = (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) l in
  map_group_zero_or_more_eq (g1 `map_group_choice` g2) l;
  map_group_zero_or_more_eq g1 l;
  match g1 l with
  | MapGroupCutFailure -> ()
  | MapGroupResult s1 ->
    if s1 = MPS.empty
    then begin
      map_group_concat_eq_l
        (map_group_zero_or_more g1)
        map_group_nop
        (map_group_zero_or_more g2)
        l;
      assert (rhs == (map_group_nop `map_group_concat` map_group_zero_or_more g2) l);
      map_group_concat_nop_l (map_group_zero_or_more g2);
      assert (rhs == (map_group_zero_or_more g2) l);
      map_group_zero_or_more_eq g2 l;
      begin match g2 l with
      | MapGroupCutFailure -> ()
      | MapGroupResult s2 ->
        if s2 = MPS.empty
        then begin
          assert (lhs == map_group_nop l);
          assert (rhs == map_group_nop l)
        end else begin
          map_group_concat_eq_l
            (g1 `map_group_choice` g2)
            g2
            (bound_map_group l (map_group_zero_or_more (g1 `map_group_choice` g2)))
            l;
          bound_map_group_ext' l (map_group_zero_or_more (g1 `map_group_choice` g2)) (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) (fun l' -> map_group_zero_or_more_choice' g1 g2 l');
          map_group_is_productive_concat_bound l g2 l (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2);
          map_group_is_productive_concat_bound l g2 l (map_group_zero_or_more g2);
          map_group_concat_eq_r
            g2
            (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)
            (map_group_zero_or_more g2)
            l
            (fun l' ->
              map_group_zero_or_more_eq g1 (snd l');
              map_group_concat_eq_l
                (map_group_zero_or_more g1)
                map_group_nop
                (map_group_zero_or_more g2)
                (snd l');
              ()
            );
          ()
        end
      end
    end else begin
      map_group_concat_eq_l
        (g1 `map_group_choice` g2)
        g1
        (bound_map_group l (map_group_zero_or_more (g1 `map_group_choice` g2)))
        l;
      bound_map_group_ext' l (map_group_zero_or_more (g1 `map_group_choice` g2)) (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2) (fun l' -> map_group_zero_or_more_choice' g1 g2 l');
      map_group_is_productive_concat_bound l g1 l (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2);
      assert (lhs == (g1 `map_group_concat` (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)) l);
      map_group_concat_eq_l
        (map_group_zero_or_more g1)
        (g1 `map_group_concat` bound_map_group l (map_group_zero_or_more g1))
        (map_group_zero_or_more g2)
        l;
      map_group_is_productive_concat_bound l g1 l (map_group_zero_or_more g1);
      map_group_concat_eq_l
        (g1 `map_group_concat` bound_map_group l (map_group_zero_or_more g1))
        (g1 `map_group_concat` map_group_zero_or_more g1)
        (map_group_zero_or_more g2)
        l;
      map_group_concat_assoc g1 (map_group_zero_or_more g1) (map_group_zero_or_more g2);
      assert (rhs == (g1 `map_group_concat` (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)) l)
    end    

let map_group_zero_or_more_choice
  (g1 g2: map_group)
: Lemma
  (requires (
    map_group_fail_shorten g1 /\
    map_group_is_productive g1 /\
    map_group_is_productive g2
  ))
  (ensures (
    map_group_zero_or_more (g1 `map_group_choice` g2) == map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2
  ))
= Classical.forall_intro (Classical.move_requires (map_group_zero_or_more_choice' g1 g2));
  assert (map_group_zero_or_more (g1 `map_group_choice` g2) `FE.feq` (map_group_zero_or_more g1 `map_group_concat` map_group_zero_or_more g2)
  )

let map_group_zero_or_one_choice
  (g1 g2: map_group)
: Lemma
  (map_group_zero_or_one (g1 `map_group_choice` g2) == g1 `map_group_choice` map_group_zero_or_one g2)
= map_group_choice_assoc g1 g2 map_group_nop

let matches_map_group (g: map_group) (m: cbor_map) : Tot bool =
  match g m with
  | MapGroupResult s ->
    s = MPS.singleton (m, cbor_map_empty)
  | _ -> false

let matches_map_group_det (g: map_group) m
= ()

let t_map g = fun x ->
  match unpack x with
  | CMap m ->
    matches_map_group g m
  | _ -> false

let t_map_eq
  g x
= ()
