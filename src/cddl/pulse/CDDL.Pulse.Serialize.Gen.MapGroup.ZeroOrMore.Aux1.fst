module CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore.Aux1
#lang-pulse

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
let map_of_list_serializable_disjoint
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2) ==>
    (Map.disjoint m1 m2 <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))
  ))
= ()

#restart-solver
let map_of_list_is_append_serializable_intro_serializable
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ Map.disjoint m1 m2) ==>
      sp.mg_serializable m
  ))
= ()

#restart-solver
let map_of_list_is_append_serializable_intro
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m1 /\ sp.mg_serializable m2 /\ (Map.disjoint m1 m2 \/ cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2))) ==>
    (Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2) /\
      sp.mg_serializable m /\
      sp.mg_serializer m == (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro_serializable sp1 sp2 except m1 m2 m;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2;
  if sp.mg_serializable m1 && sp.mg_serializable m2 && cbor_map_disjoint_tot (sp.mg_serializer m1) (sp.mg_serializer m2)
  then begin
    let prf_m (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m kv
    in
    let prf_m1 (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m1) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m1 kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m1 kv
    in
    let prf_m2 (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m2) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m2 kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m2 kv
    in
    Classical.forall_intro prf_m;
    Classical.forall_intro prf_m1;
    Classical.forall_intro prf_m2;
    assert (
      forall kv . (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv <==> (map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m1 kv \/ map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m2 kv)
    ));
    cbor_map_mem_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2);
    cbor_map_mem_ext (sp.mg_serializer m) (sp.mg_serializer m1 `cbor_map_union` sp.mg_serializer m2)
  end

#pop-options

let map_of_list_is_append_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (map_of_list_is_append
    m1
    (Map.singleton k (key_eq k) [v])
    (map_of_list_snoc key_eq m1 k v)
  )
= ()

let map_of_list_is_append_cons
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m1: Map.t key (list value))
: Lemma
  (map_of_list_is_append
    (Map.singleton k (key_eq k) [v])
    m1
    (map_of_list_cons key_eq k v m1)
  )
= ()

#push-options "--z3rlimit 128 --split_queries always"

#restart-solver
let map_of_list_is_append_serializable_elim
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
: Lemma
  (requires (
    map_of_list_is_append m1 m2 m /\
    map_of_list_maps_to_nonempty m1 /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  if sp.mg_serializable m
  then begin
    assert (
      sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2
    );
    map_of_list_serializable_disjoint sp1 sp2 except m1 m2
  end

let map_of_list_is_append_serializable_elim'
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (m: Map.t key (list value))
  (sq: squash (map_of_list_is_append m1 m2 m))
  (sq1: squash (map_of_list_maps_to_nonempty m1))
  (sq2: squash (map_of_list_maps_to_nonempty m2))
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    (sp.mg_serializable m
    ) ==> (sp.mg_serializable m1 /\
      sp.mg_serializable m2 /\
      Map.disjoint m1 m2 /\
      cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
    )
  ))
= map_of_list_is_append_serializable_elim sp1 sp2 except m1 m2 m

#pop-options

#push-options "--z3rlimit 64"

#restart-solver
let map_of_list_is_append_serializable_singleton
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (k: key)
  (k_eq: EqTest.eq_test_for k)
  (v: value)
: Lemma
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m = EqTest.map_singleton k k_eq [v] in
    (sp.mg_serializable m <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v)))
    )) /\
    (sp.mg_serializable m ==> (
    sp.mg_serializer m == cbor_map_singleton (sp1.serializer k) (sp2.serializer v)
  ))))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let m = EqTest.map_singleton k k_eq [v] in
  assert (forall kv . Map.mem kv m <==> (fst kv == k /\ snd kv == [v]));
  assert (sp.mg_serializable m <==> (forall kv . Map.mem kv m ==> map_entry_serializable sp1 sp2 except kv));
  assert (sp.mg_serializable m <==> map_entry_serializable sp1 sp2 except (k, [v]));
  if sp.mg_serializable m
  then begin
    let prf (kv: (cbor & cbor)) : Lemma (cbor_map_mem kv (sp.mg_serializer m) <==> map_group_zero_or_more_match_item_serializer'_mem_aux sp1 sp2 except m kv)
    = map_group_zero_or_more_match_item_serializer'_mem sp1 sp2 except m kv
    in
    Classical.forall_intro prf;
    cbor_map_mem_ext
      (sp.mg_serializer m)
      (cbor_map_singleton (sp1.serializer k) (sp2.serializer v))
  end

#pop-options

let map_of_list_maps_to_nonempty_singleton
  (#key: Type)
  (#value: Type)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: list value)
  (sq: squash (Cons? v))
: Lemma
  (map_of_list_maps_to_nonempty (Map.singleton k k_eq v))
= ()

let map_of_list_maps_to_nonempty_cons
  (#key: Type)
  (#value: Type)
  (k_eq: EqTest.eq_test key)
  (k: key)
  (v: value)
  (m: Map.t key (list value))
  (sq: squash (map_of_list_maps_to_nonempty m))
: Lemma
  (map_of_list_maps_to_nonempty (map_of_list_cons k_eq k v m))
= ()

let impl_serialize_map_group_valid_map_zero_or_more_snoc_length
  (ll lm1 lkv lm2: nat)
: Lemma
  ((ll + lm1) + (lkv + lm2) == (ll + (lm1 + lkv)) + lm2)
= ()

#restart-solver

let map_of_list_sub
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
  (lv': list value)
: Pure (Map.t key (list value))
  (requires (
    Map.get m k == Some (v :: lv')
  ))
  (ensures fun m' ->
    (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m') /\
    m == map_of_list_cons key_eq k v m'
  )
=
  let f (kv: (key & list value)) : bool =
    not (key_eq k (fst kv))
  in
  let m' : Map.t key (list value) = match lv' with
  | [] -> Map.filter f m
  | _ -> EqTest.map_set #key #(list value) m k (key_eq k) lv'
  in
  assert (map_of_list_maps_to_nonempty m ==> map_of_list_maps_to_nonempty m');
  assert (Map.equal m (map_of_list_cons key_eq k v m'));
  m'

#restart-solver

let seq_slice_append_pat (#t: Type) (s1 s2: Seq.seq t)
: Lemma
  (ensures Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
  [SMTPat (Seq.append s1 s2)]
= Seq.lemma_split (Seq.append s1 s2) (Seq.length s1);
  Seq.append_slices s1 s2

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_split (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t))
    requires pts_to s #p v ** pure (
      SZ.v i <= Seq.length v
    )
    returns res: (S.slice t & S.slice t)
    ensures (let (s1, s2) = res in exists* v1 v2 .
      pts_to s1 #p v1 **
      pts_to s2 #p v2 **
      S.is_split s s1 s2 **
      pure (slice_split_post i v v1 v2 /\
        SZ.v (S.len s) == Seq.length v /\
        SZ.v (S.len s1) == Seq.length v1 /\
        SZ.v (S.len s2) == Seq.length v2)
    )
{
  S.pts_to_len s;
  Seq.lemma_split v (SZ.v i);
  let (s1, s2) = S.split s i;
  S.pts_to_len s1;
  S.pts_to_len s2;
  (s1, s2)
}

(* Gen iterator core loop function *)

let map_of_list_maps_to_nonempty_snoc
  (#key #value: Type)
  (key_eq: EqTest.eq_test key)
  (m: Map.t key (list value))
  (k: key)
  (v: value)
: Lemma
  (requires map_of_list_maps_to_nonempty m)
  (ensures map_of_list_maps_to_nonempty (map_of_list_snoc key_eq m k v))
= let m' = map_of_list_snoc key_eq m k v in
  let aux (k': key) : Lemma (map_of_list_maps_to_nonempty_at m' k') =
    if key_eq k k' then
      match Map.get m k with
      | None -> ()
      | Some l -> List.Tot.append_length l [v]
    else ()
  in
  Classical.forall_intro aux

// Helper: explicitly apply cbor_parse_prefix_prop to go from pe (slice x 0 n) to pe x
#push-options "--z3rlimit 32"
let cbor_parse_prefix_apply
  (pe: cbor_parser)
  (x: Seq.seq U8.t)
  (n: nat)
: Lemma
  (requires (
    n <= Seq.length x /\
    Some? (pe (Seq.slice x 0 n))
  ))
  (ensures (
    pe x == pe (Seq.slice x 0 n)
  ))
= let y = Seq.slice x 0 n in
  let sn = Some?.v (pe y) in
  assert (0 < snd sn /\ snd sn <= Seq.length y);
  assert (snd sn <= n);
  assert (Seq.length x >= snd sn);
  assert (Seq.equal (Seq.slice y 0 (snd sn)) (Seq.slice x 0 (snd sn)));
  assert (cbor_parse_prefix_prop' pe y x)
#pop-options

#restart-solver
