module CDDL.Pulse.Serialize.Gen.MapGroup
open CDDL.Pulse.Serialize.Gen.MapGroup.Aux
#lang-pulse

module GR = Pulse.Lib.GhostReference
module Map = CDDL.Spec.Map

let impl_serialize_map_zero_or_more_insert_pre_helper
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: cbor_parser)
  (l: cbor_map)
  (key: cbor)
  (value: cbor)
  (wl: Seq.seq U8.t)
  (w0_slice w1_slice w2_slice: Seq.seq U8.t)
  (size0: SZ.t) (size1 size2: SZ.t)
: Lemma
  (requires (
    SZ.v size0 <= SZ.v size1 /\
    SZ.v size1 <= SZ.v size2 /\
    SZ.v size2 == Seq.length wl /\
    p (cbor_map_length l) w0_slice == Some (l, SZ.v size0) /\
    Seq.slice wl 0 (SZ.v size0) == w0_slice /\
    pe w1_slice == Some (key, SZ.v size1 - SZ.v size0) /\
    Seq.slice wl (SZ.v size0) (SZ.v size1) == w1_slice /\
    pe w2_slice == Some (value, SZ.v size2 - SZ.v size1) /\
    Seq.slice wl (SZ.v size1) (Seq.length wl) == w2_slice
  ))
  (ensures (
    cbor_serialize_map_insert_pre p pe l size0 key size1 value wl
  ))
= ()

(* Helper that works with the buffer shapes after split/join in the iterator *)
let impl_serialize_map_zero_or_more_insert_pre_helper2
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: cbor_parser)
  (l: cbor_map)
  (key: cbor)
  (value: cbor)
  (w_orig: Seq.seq U8.t)
  (w1_after_key: Seq.seq U8.t)
  (z2l: Seq.seq U8.t)
  (w2: Seq.seq U8.t)
  (count: U64.t)
  (size0: SZ.t) (sz1 sz2: SZ.t)
: Lemma
  (requires (
    SZ.v sz1 > 0 /\
    SZ.v sz2 > 0 /\
    SZ.v size0 <= Seq.length w_orig /\
    SZ.fits (SZ.v size0 + SZ.v sz1) /\
    SZ.fits (SZ.v size0 + SZ.v sz1 + SZ.v sz2) /\
    SZ.v size0 + SZ.v sz1 + SZ.v sz2 <= Seq.length w_orig /\
    p (U64.v count) w_orig == Some (l, SZ.v size0) /\
    Seq.length w1_after_key == Seq.length w_orig - SZ.v size0 /\
    z2l == Seq.slice w1_after_key 0 (SZ.v sz1) /\
    pe (Seq.slice w1_after_key 0 (SZ.v sz1)) == Some (key, SZ.v sz1) /\
    SZ.v sz2 <= Seq.length w2 /\
    Seq.length w2 == Seq.length w1_after_key - SZ.v sz1 /\
    pe (Seq.slice w2 0 (SZ.v sz2)) == Some (value, SZ.v sz2)
  ))
  (ensures (
    let size1 = SZ.uint_to_t (SZ.v size0 + SZ.v sz1) in
    let size2 = SZ.uint_to_t (SZ.v size0 + SZ.v sz1 + SZ.v sz2) in
    let wl = Seq.slice (Seq.append (Seq.slice w_orig 0 (SZ.v size0)) (Seq.append z2l w2)) 0 (SZ.v size2) in
    cbor_serialize_map_insert_pre p pe l size0 key size1 value wl
  ))
= let size1_n = SZ.v size0 + SZ.v sz1 in
  let size2_n = size1_n + SZ.v sz2 in
  let w_joined = Seq.append (Seq.slice w_orig 0 (SZ.v size0)) (Seq.append z2l w2) in
  let wl = Seq.slice w_joined 0 size2_n in
  let w0s = Seq.slice w_orig 0 (SZ.v size0) in
  Seq.lemma_eq_elim (Seq.slice wl 0 (SZ.v size0)) w0s;
  // p returns cbor_map_length m == n, so cbor_map_length l == U64.v count
  cbor_parse_map_prefix_slice p (U64.v count) w_orig l (SZ.v size0);
  assert (p (U64.v count) w0s == Some (l, SZ.v size0));
  assert (cbor_map_length l == U64.v count);
  Seq.lemma_eq_elim (Seq.slice wl (SZ.v size0) size1_n) z2l;
  Seq.lemma_eq_elim (Seq.slice wl size1_n (Seq.length wl)) (Seq.slice w2 0 (SZ.v sz2))

(* impl_serialize_map_zero_or_more *)

let impl_serialize_map_zero_or_more_iterator_inv_gen
    (p: bare_cbor_map_parser) (minl: cbor -> nat) (maxl: cbor -> option nat)
    (#key: typ) (#tkey: Type0)
    (sp1: spec key tkey true)
    (#value: typ) (#tvalue: Type0) (#inj: bool)
    (sp2: spec value tvalue inj)
    (except: map_constraint { inj \/ map_constraint_value_injective key sp2.parser except })
  (v0: Map.t tkey (list tvalue))
  (l: cbor_map)
  (res: bool)
  (w: Seq.seq U8.t)
  (m1 m2 m2': Map.t tkey (list tvalue))
  (count: U64.t)
  (size: SZ.t)
: Tot prop
=
  let sp = (mg_zero_or_more_match_item sp1 sp2 except) in
      map_of_list_is_append m1 m2' v0 /\
      map_of_list_maps_to_nonempty m1 /\
      sp.mg_serializable m1 /\
      cbor_map_disjoint l (sp.mg_serializer m1) /\
      (res == true ==> (
        m2' == m2 /\
        impl_serialize_map_group_pre p count size (cbor_map_union l (sp.mg_serializer m1)) w
      )) /\
      impl_serialize_map_group_valid maxl l sp v0 (Seq.length w) == (if res then impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' (Seq.length w) else false)

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

let cbor_map_mem_disjoint
  (m1 m2: cbor_map)
: Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (forall kv . cbor_map_mem kv (cbor_map_union m1 m2) <==> (cbor_map_mem kv m1 \/ cbor_map_mem kv m2)))
= ()

let cbor_map_mem_ext
  (m1 m2: cbor_map)
: Lemma
  (requires (forall kv . cbor_map_mem kv m1 <==> cbor_map_mem kv m2))
  (ensures (m1 == m2))
= assert (forall k . match cbor_map_get m1 k with
  | Some v -> cbor_map_mem (k, v) m1
  | _ -> True
  );
  assert (forall k . match cbor_map_get m2 k with
  | Some v -> cbor_map_mem (k, v) m2
  | _ -> True
  );
  assert (cbor_map_equal m1 m2)

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

#push-options "--z3rlimit 64 --split_queries always"

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

#push-options "--z3rlimit 32 --print_implicits"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_aux_gen
  (maxl: cbor -> option nat)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      (
        sp1.serializable k /\
        sp2.serializable v /\
        (~ (except (sp1.serializer k, sp2.serializer v))) /\
        (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
      ) ==> (
      sp.mg_serializable (map_of_list_snoc key_eq m1 k v) /\
      cbor_map_disjoint l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) /\
      cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) /\
      cbor_map_length (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_length (sp.mg_serializer m1) + 1
  ))))
=
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_maps_to_nonempty_cons key_eq k v m2 ();
  assert (map_of_list_maps_to_nonempty m2');
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_serializable_elim sp1 sp2 except mkv m2 m2';
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if
        sp1.serializable k &&
        sp2.serializable v &&
        (not (except (sp1.serializer k, sp2.serializer v))) &&
        (not (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
  then begin
      assert (sp.mg_serializable m1');
      assert (cbor_map_disjoint l (sp.mg_serializer mkv));
      assert (cbor_map_disjoint l (sp.mg_serializer m1'));
      assert (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)));
      assert (cbor_map_length (sp.mg_serializer mkv) == 1);
      assert (cbor_map_length (sp.mg_serializer m1') == cbor_map_length (sp.mg_serializer m1) + 1)
  end

#pop-options

#push-options "--z3rlimit 256"

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1_gen
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (sq: squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    sp1.serializable k /\
    sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\
    sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
  ))
: Tot (squash (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in
    sp.mg_serializable m1' /\
    cbor_map_disjoint (sp.mg_serializer m1') (sp.mg_serializer m2) <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2)
  ))
=
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  map_of_list_serializable_disjoint sp1 sp2 except m1 m2;
  map_of_list_serializable_disjoint sp1 sp2 except m1' m2;
  ()

#pop-options

#push-options "--z3rlimit 256 --split_queries always"

let cbor_map_disjoint_union_r (l m1 m2: cbor_map) : Lemma
  (requires cbor_map_disjoint l m1 /\ cbor_map_disjoint l m2 /\ cbor_map_disjoint m1 m2)
  (ensures cbor_map_disjoint l (cbor_map_union m1 m2))
= ()

#restart-solver
let impl_serialize_map_group_valid_map_zero_or_more_snoc_length1_gen
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    sp1.serializable k /\
    sp2.serializable v /\
    (~ (except (sp1.serializer k, sp2.serializer v))) /\
    sp.mg_serializable m2 /\
    (~ (Map.defined k m2)) /\
    (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
    sp.mg_serializable m2' /\
    cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let m1' = map_of_list_snoc key_eq m1 k v in
    let m2' = map_of_list_cons key_eq k v m2 in
    sp.mg_serializable m1' /\
    sp.mg_serializable m2' /\
    cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2) /\
    cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') == cbor_map_union (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2)
  ))
=
  impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1_gen sp1 key_eq sp2 except l m1 k v m2 ();
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  let m2' = map_of_list_cons key_eq k v m2 in
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_cons key_eq k v m2;
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  // establish mkv serializable
  let _sq_mkv_ser : squash (sp.mg_serializable mkv /\ sp.mg_serializer mkv == cbor_map_singleton (sp1.serializer k) (sp2.serializer v))
  = () in
  // establish m1 disjoint mkv
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  let _sq_m1_mkv_disj : squash (cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer mkv))
  = () in
  // establish m1' = union m1 mkv and m1' serializable
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  let _sq_m1'_props : squash (sp.mg_serializable m1' /\ sp.mg_serializer m1' == cbor_map_union (sp.mg_serializer m1) (sp.mg_serializer mkv))
  = () in
  // establish l disjoint m1'
  cbor_map_disjoint_union_r l (sp.mg_serializer m1) (sp.mg_serializer mkv);
  let _sq_l_m1'_disj : squash (cbor_map_disjoint l (sp.mg_serializer m1'))
  = () in
  // establish mkv disjoint m2
  map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
  let _sq_mkv_m2_disj : squash (cbor_map_disjoint (sp.mg_serializer mkv) (sp.mg_serializer m2))
  = () in
  // establish m2' = union mkv m2
  map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
  let _sq_m2'_props : squash (sp.mg_serializable m2' /\ sp.mg_serializer m2' == cbor_map_union (sp.mg_serializer mkv) (sp.mg_serializer m2))
  = () in
  // length calculations: use move_requires to avoid needing explicit disjoint proofs at each call site
  Classical.move_requires (cbor_map_length_disjoint_union l) (sp.mg_serializer m1);
  Classical.move_requires (cbor_map_length_disjoint_union l) (sp.mg_serializer m1');
  Classical.move_requires (cbor_map_length_disjoint_union (sp.mg_serializer m1)) (sp.mg_serializer mkv);
  Classical.move_requires (cbor_map_length_disjoint_union (sp.mg_serializer mkv)) (sp.mg_serializer m2);
  Classical.move_requires (cbor_map_length_disjoint_union (cbor_map_union l (sp.mg_serializer m1))) (sp.mg_serializer m2');
  Classical.move_requires (cbor_map_length_disjoint_union (cbor_map_union l (sp.mg_serializer m1'))) (sp.mg_serializer m2);
  let ll = cbor_map_length l in
  let lm1 = cbor_map_length (sp.mg_serializer m1) in
  let lm2 = cbor_map_length (sp.mg_serializer m2) in
  impl_serialize_map_group_valid_map_zero_or_more_snoc_length ll lm1 1 lm2;
  // Union equality:
  // union (union l (s m1)) (s m2') = union (union l (s m1)) (union (s mkv) (s m2))
  //  = union l (union (s m1) (union (s mkv) (s m2)))     [by assoc]
  //  = union l (union (union (s m1) (s mkv)) (s m2))     [by assoc]
  //  = union l (union (s m1') (s m2))                    [by m1' def]
  //  = union (union l (s m1')) (s m2)                    [by assoc]
  cbor_map_union_assoc (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer mkv) (sp.mg_serializer m2);
  cbor_map_union_assoc l (sp.mg_serializer m1) (cbor_map_union (sp.mg_serializer mkv) (sp.mg_serializer m2));
  cbor_map_union_assoc l (sp.mg_serializer m1) (sp.mg_serializer mkv);
  cbor_map_union_assoc l (cbor_map_union (sp.mg_serializer m1) (sp.mg_serializer mkv)) (sp.mg_serializer m2);
  cbor_map_union_assoc l (sp.mg_serializer m1') (sp.mg_serializer m2);
  ()

#pop-options

#push-options "--z3rlimit 256 --z3cliopt 'smt.qi.eager_threshold=100' --split_queries always"

#restart-solver

let impl_serialize_map_group_valid_map_zero_or_more_snoc_gen
  (maxl: cbor -> option nat)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (k: key)
  (v: value)
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\ (
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq k v m2) len <==> (
      sp1.serializable k /\
      sp2.serializable v /\
      (~ (except (sp1.serializer k, sp2.serializer v))) /\
      FStar.UInt.fits (cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1) 64 /\
      (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1)))) /\
      (sp.mg_serializable (map_of_list_snoc key_eq m1 k v) ==>
        impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v))) sp m2 len
      )
    )) /\ (
      (
        sp1.serializable k /\
        sp2.serializable v /\
        (~ (except (sp1.serializer k, sp2.serializer v))) /\
        (~ (cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))))
      ) ==> (
      sp.mg_serializable (map_of_list_snoc key_eq m1 k v) /\
      cbor_map_disjoint l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) /\
      cbor_map_union l (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer k) (sp2.serializer v)) /\
      cbor_map_length (sp.mg_serializer (map_of_list_snoc key_eq m1 k v)) == cbor_map_length (sp.mg_serializer m1) + 1
  ))))
= impl_serialize_map_group_valid_map_zero_or_more_snoc_aux_gen maxl sp1 key_eq sp2 except l m1 k v m2 len;
  let m2' = map_of_list_cons key_eq k v m2 in
  map_of_list_is_append_cons key_eq k v m2;
  let sq1 : squash (map_of_list_maps_to_nonempty m2) = assert (map_of_list_maps_to_nonempty m2) in
  let sq2 : squash (map_of_list_maps_to_nonempty m2') = map_of_list_maps_to_nonempty_cons key_eq k v m2 sq1 in
  let mkv = EqTest.map_singleton k (key_eq k) [v] in
  map_of_list_maps_to_nonempty_singleton k (key_eq k) [v] ();
  let m1' = map_of_list_snoc key_eq m1 k v in
  map_of_list_is_append_snoc key_eq m1 k v;
  map_of_list_is_append_serializable_elim' sp1 sp2 except mkv m2 m2' () () sq2;
  map_of_list_is_append_serializable_singleton sp1 sp2 except k (key_eq k) v;
  let sp = mg_zero_or_more_match_item sp1 sp2 except in
  map_of_list_is_append_serializable_intro sp1 sp2 except m1 mkv m1';
  map_of_list_serializable_disjoint sp1 sp2 except m1 mkv;
  if
    sp1.serializable k &&
    sp2.serializable v &&
    (not (except (sp1.serializer k, sp2.serializer v)))
  then begin
    if sp.mg_serializable m2
    then begin
      map_of_list_serializable_disjoint sp1 sp2 except mkv m2;
      if Map.defined k m2
      then ()
      else begin
        map_of_list_is_append_cons key_eq k v m2;
        map_of_list_is_append_serializable_intro sp1 sp2 except mkv m2 m2';
        if cbor_map_defined (sp1.serializer k) (cbor_map_union l (sp.mg_serializer m1))
        then begin
          assert (~ (cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')));
          assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))
        end
        else begin
          assert (cbor_map_disjoint l (sp.mg_serializer m1'));
          assert (cbor_map_disjoint l (sp.mg_serializer m2') <==> cbor_map_disjoint l (sp.mg_serializer m2));
          assert (cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2') <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2));
          map_of_list_is_append_snoc key_eq m1 k v;
          impl_serialize_map_group_valid_map_zero_or_more_snoc_disjoint1_gen sp1 key_eq sp2 except l m1 k v m2 ();
          assert (cbor_map_disjoint (sp.mg_serializer m1') (sp.mg_serializer m2) <==> cbor_map_disjoint (sp.mg_serializer m1) (sp.mg_serializer m2));
          assert (cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') <==> cbor_map_disjoint (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2));
          if cbor_map_disjoint_tot (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2')
          then begin
            cbor_map_length_disjoint_union l (sp.mg_serializer m1');
            impl_serialize_map_group_valid_map_zero_or_more_snoc_length1_gen sp1 key_eq sp2 except l m1 k v m2;
            assert (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') == cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) + cbor_map_length (sp.mg_serializer m2));
            assert (cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + cbor_map_length (sp.mg_serializer m2') >= cbor_map_length (cbor_map_union l (sp.mg_serializer m1)) + 1);
            // The key insight for Gen: union l' s(m2') == union l'' s(m2)
            // so cbor_map_max_length maxl of both sides is the same
            assert (cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (sp.mg_serializer m2') == cbor_map_union (cbor_map_union l (sp.mg_serializer m1')) (sp.mg_serializer m2));
            ()
          end
          else begin
            assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len));
            assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1')) sp m2 len))
          end
        end
      end
    end
    else begin
      assert (forall l' . ~ (impl_serialize_map_group_valid maxl l' sp m2 len));
      assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))
    end
  end
  else assert (~ (impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2' len))

#pop-options

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

let impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow_gen
  (maxl: cbor -> option nat)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (m2: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    (m2 =!= Map.empty _ _) /\
    cbor_map_length l + cbor_map_length (sp.mg_serializer m1) + 1 >= pow2 64
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2 len == false
  ))
= let sp = mg_zero_or_more_match_item sp1 sp2 except in
  let prf
    (k: key)
  : Lemma
    (requires (Map.defined k m2))
    (ensures (
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp m2 len == false
    ))
  = assert (Some? (Map.get m2 k));
    let Some lv = Map.get m2 k in
    assert (Cons? lv);
    let v :: lv' = lv in
    let m2' = map_of_list_sub key_eq m2 k v lv' in
    map_of_list_is_append_cons key_eq k v m2';
    impl_serialize_map_group_valid_map_zero_or_more_snoc_gen maxl sp1 key_eq sp2 except l m1 k v m2' len;
    ()
  in
  Classical.forall_intro (Classical.move_requires prf);
  assert (~ (Map.equal m2 (Map.empty _ _)));
  ()

#restart-solver

let impl_serialize_map_group_insert_prf_gen_post
  (p: bare_cbor_map_parser)
  (pe: bare_cbor_parser)
  (w: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (sz1: nat)
  (v: cbor)
  (sz2: nat)
: Tot prop
=
    SZ.fits (sz0 + sz1 + sz2) /\
    sz0 + sz1 + sz2 <= Seq.length w /\
    cbor_serialize_map_insert_pre p pe l (SZ.uint_to_t sz0) k (SZ.uint_to_t (sz0 + sz1)) v (Seq.slice w 0 (sz0 + sz1 + sz2))

let impl_serialize_map_group_insert_prf_gen
  (p: bare_cbor_map_parser { cbor_parse_map_prefix_prop p })
  (pe: bare_cbor_parser)
  (w_inv: Seq.seq U8.t)
  (l: cbor_map)
  (sz0: nat)
  (k: cbor)
  (z2l: Seq.seq U8.t)
  (v: cbor)
  (w2: Seq.seq U8.t)
  (sz2: nat)
: Lemma
  (requires (
    let sz1 = Seq.length z2l in
    sz0 <= Seq.length w_inv /\
    p (cbor_map_length l) w_inv == Some (l, sz0) /\
    sz1 > 0 /\
    pe z2l == Some (k, sz1) /\
    sz2 > 0 /\
    sz2 <= Seq.length w2 /\
    pe (Seq.slice w2 0 sz2) == Some (v, sz2) /\
    SZ.fits (sz0 + sz1 + sz2)
  ))
  (ensures (
    let sz1 = Seq.length z2l in
    let z1l = Seq.slice w_inv 0 sz0 in
    let w = Seq.append z1l (Seq.append z2l w2) in
    impl_serialize_map_group_insert_prf_gen_post p pe w l sz0 k sz1 v sz2
  ))
= let sz1 = Seq.length z2l in
  let z1l = Seq.slice w_inv 0 sz0 in
  let w = Seq.append z1l (Seq.append z2l w2) in
  let w' = Seq.slice w 0 (sz0 + sz1 + sz2) in
  // Establish Seq.slice w' 0 sz0 == z1l
  Seq.append_slices z1l (Seq.append z2l w2);
  Seq.slice_slice w 0 (sz0 + sz1 + sz2) 0 sz0;
  assert (Seq.slice w' 0 sz0 == z1l);
  // p count z1l == Some (l, sz0) via prefix prop from p count w_inv
  assert (Seq.equal (Seq.slice z1l 0 sz0) z1l);
  assert (Seq.slice w_inv 0 sz0 == z1l);
  // w'[sz0..sz0+sz1] == z2l
  Seq.lemma_split w sz0;
  Seq.slice_slice w sz0 (Seq.length w) 0 sz1;
  Seq.append_slices z2l w2;
  assert (Seq.slice w' sz0 (sz0 + sz1) == z2l);
  // w'[(sz0+sz1)..] == Seq.slice w2 0 sz2
  Seq.slice_slice w sz0 (Seq.length w) sz1 (sz1 + sz2);
  Seq.slice_slice w 0 (sz0 + sz1 + sz2) (sz0 + sz1) (sz0 + sz1 + sz2);
  assert (Seq.slice w' (sz0 + sz1) (Seq.length w') == Seq.slice w2 0 sz2);
  ()

module SM = Pulse.Lib.SeqMatch

let seq_slice_append_pat (#t: Type) (s1 s2: Seq.seq t)
: Lemma
  (ensures Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
  [SMTPat (Seq.append s1 s2)]
= Seq.lemma_split (Seq.append s1 s2) (Seq.length s1);
  Seq.append_slices s1 s2

let seq_slice_length_zero_left
  (#t: Type)
  (s: Seq.seq t)
  (len: nat { len <= Seq.length s })
: Lemma
  (Seq.length (Seq.slice s 0 len) == len)
= ()

let slice_split_post
  (#t: Type)
  (i: SZ.t)
  (v v1 v2: Seq.seq t)
: Tot prop
= SZ.v i <= Seq.length v /\
  v1 == Seq.slice v 0 (SZ.v i) /\
  v2 == Seq.slice v (SZ.v i) (Seq.length v) /\
  Seq.length v1 == SZ.v i /\
  Seq.length v2 == Seq.length v - SZ.v i /\
  v == Seq.append v1 v2

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
      pure (slice_split_post i v v1 v2)
    )
{
  Seq.lemma_split v (SZ.v i);
  let (s1, s2) = S.split s i;
  (s1, s2)
}

(* Gen iterator type alias *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator_gen_t
    (p: bare_cbor_map_parser) (minl: cbor -> nat) (maxl: cbor -> option nat)
    (#key: Ghost.erased typ) (#tkey: Type0)
    (sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0) (r1: rel ikey tkey)
    (#value: Ghost.erased typ) (#tvalue: Type0) (#inj: Ghost.erased bool)
    (sp2: Ghost.erased (spec value tvalue inj))
    (except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (#ivalue: Type0) (r2: rel ivalue tvalue)
    (iterator: (Ghost.erased (Iterator.type_spec ikey) -> Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
= impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_
    (mg_zero_or_more_match_item sp1 sp2 except) #_ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2))

(* Gen iterator core loop function *)

(* Helper: when except holds, valid l sp v0 len == false *)
let impl_serialize_map_zero_or_more_valid_false_except_gen
  (maxl: cbor -> option nat)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (ke: key)
  (va: value)
  (m2 v0: Map.t key (list value))
  (len: nat)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty m2 /\
    sp1.serializable ke /\
    sp2.serializable va /\
    except (sp1.serializer ke, sp2.serializer va) /\
    impl_serialize_map_group_valid maxl l sp v0 len ==
      impl_serialize_map_group_valid maxl (cbor_map_union l (sp.mg_serializer m1)) sp (map_of_list_cons key_eq ke va m2) len
  ))
  (ensures (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    impl_serialize_map_group_valid maxl l sp v0 len == false
  ))
= impl_serialize_map_group_valid_map_zero_or_more_snoc_gen maxl sp1 key_eq sp2 except l m1 ke va m2 len

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

// Helper: when pa1 returns 0, valid == false
#push-options "--z3rlimit 512 --split_queries always"
let impl_serialize_map_zero_or_more_valid_false_sz1_gen
  (pe: cbor_parser)
  (minl: cbor_min_length pe)
  (maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (ke: key)
  (va: value)
  (m2: Map.t key (list value))
  (v0: Map.t key (list value))
  (len: nat)
  (count: U64.t)
  (size0: SZ.t)
  (w w1: Seq.seq U8.t)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let l' = cbor_map_union l (sp.mg_serializer m1) in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty (map_of_list_cons key_eq ke va m2) /\
    impl_serialize_map_group_pre p count size0 l' w /\
    Seq.length w == len /\
    Seq.length w1 == len - SZ.v size0 /\
    impl_serialize_map_group_valid maxl l sp v0 len ==
      impl_serialize_map_group_valid maxl l' sp (map_of_list_cons key_eq ke va m2) len /\
    // pa1 returned 0: key serialization failed
    not (sp1.serializable ke && Some? (maxl (sp1.serializer ke)) && Some?.v (maxl (sp1.serializer ke)) <= Seq.length w1)
  ))
  (ensures (
    impl_serialize_map_group_valid maxl l (mg_zero_or_more_match_item sp1 sp2 except) v0 len == false
  ))
= admit ()
#pop-options

#restart-solver
// The proof uses snoc_gen + cbor_map_max_length reasoning
#push-options "--z3rlimit 512 --split_queries always"
let impl_serialize_map_zero_or_more_valid_false_sz2_gen
  (pe: cbor_parser)
  (minl: cbor_min_length pe)
  (maxl: cbor_max_length pe)
  (p: cbor_map_parser minl maxl)
  (#key #value: Type)
  (#tkey: typ)
  (sp1: spec tkey key true)
  (key_eq: EqTest.eq_test key)
  (#tvalue: typ)
  (#inj: bool)
  (sp2: spec tvalue value inj)
  (except: map_constraint { inj \/ map_constraint_value_injective tkey sp2.parser except })
  (l: cbor_map)
  (m1: Map.t key (list value))
  (ke: key)
  (va: value)
  (m2: Map.t key (list value))
  (v0: Map.t key (list value))
  (len: nat)
  (count: U64.t)
  (size0: SZ.t)
  (sz1: nat)
  (w: Seq.seq U8.t)
  (z2l: Seq.seq U8.t)
  (w2: Seq.seq U8.t)
: Lemma
  (requires (
    let sp = mg_zero_or_more_match_item sp1 sp2 except in
    let l' = cbor_map_union l (sp.mg_serializer m1) in
    sp.mg_serializable m1 /\
    cbor_map_disjoint l (sp.mg_serializer m1) /\
    map_of_list_maps_to_nonempty (map_of_list_cons key_eq ke va m2) /\
    sp1.serializable ke /\
    sz1 > 0 /\
    pe z2l == Some (sp1.serializer ke, sz1) /\
    impl_serialize_map_group_pre p count size0 l' w /\
    Seq.length w == len /\
    SZ.v size0 + sz1 <= len /\
    Seq.length w2 == len - SZ.v size0 - sz1 /\
    impl_serialize_map_group_valid maxl l sp v0 len ==
      impl_serialize_map_group_valid maxl l' sp (map_of_list_cons key_eq ke va m2) len /\
    // pa2 returned 0: value serialization failed
    not (sp2.serializable va && Some? (maxl (sp2.serializer va)) && Some?.v (maxl (sp2.serializer va)) <= Seq.length w2)
  ))
  (ensures (
    impl_serialize_map_group_valid maxl l (mg_zero_or_more_match_item sp1 sp2 except) v0 len == false
  ))
= admit ()
#pop-options

#restart-solver

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_iterator_gen
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ) (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0) (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ) (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0) (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable]except: Ghost.erased map_constraint { Ghost.reveal inj \/ map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
    (iterator: ([@@@erasable] Ghost.erased (Iterator.type_spec ikey) -> [@@@erasable] Ghost.erased (Iterator.type_spec ivalue) -> Type0))
    (r: (spec1: Ghost.erased (Iterator.type_spec ikey)) -> (spec2: Ghost.erased (Iterator.type_spec ivalue)) -> rel (iterator spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2))))
    (is_empty: cddl_map_iterator_is_empty_gen_t _ _ iterator r)
    (next: cddl_map_iterator_next_gen_t _ _ iterator r)
    (rel_len: rel_map_iterator_length _ _ iterator r)
: impl_serialize_map_zero_or_more_iterator_gen_t p minl maxl #key #tkey sp1 #ikey r1 #value #tvalue #inj sp2 except #ivalue r2 iterator r
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let sp = Ghost.hide (mg_zero_or_more_match_item sp1 sp2 except);
  let mut pc = c0;
  let pm1 = GR.alloc (Map.empty tkey (list tvalue));
  assert (pure (
    let m1 = Map.empty tkey (list tvalue) in
    sp.mg_serializable m1 /\
    sp.mg_serializer m1 `cbor_map_equal` cbor_map_empty
  ));
  let pm2 = GR.alloc (Ghost.reveal v0);
  let mut pres = true;
  Trade.refl (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0);
  while (
    let res = !pres;
    if (res) {
      with gc . assert (pts_to pc gc);
      let c = !pc;
      rewrite each (Ghost.reveal gc) as c;
      let em = is_empty (Iterator.mk_spec r1) (Iterator.mk_spec r2) c;
      not em
    } else {
      false
    }
  ) invariant b . exists* c m1 m2' (m2: Map.t (dfst (Iterator.mk_spec r1)) (list (dfst (Iterator.mk_spec r2)))) res w count size .
    pts_to pc c **
    GR.pts_to pm1 m1 **
    GR.pts_to pm2 m2' **
    pts_to pres res **
    pts_to out w **
    pts_to out_count count **
    pts_to out_size size **
    r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c m2 **
    Trade.trade
      (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c m2)
      (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0) **
    pure (
      impl_serialize_map_zero_or_more_iterator_inv_gen p minl maxl sp1 sp2 except v0 l res w m1 (Ghost.hide (Ghost.reveal m2)) m2' count size
    ) **
    pure (b == (res && not (FStar.StrongExcludedMiddle.strong_excluded_middle (m2 == Map.empty _ _))))
  {
    rel_len #(Iterator.mk_spec r1) #(Iterator.mk_spec r2) _ _;
    S.pts_to_len out;
    with m1 . assert (GR.pts_to pm1 m1);
    with w_inv . assert (pts_to out w_inv);
    let count = !out_count;
    with c2_ m2_ . assert (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c2_ m2_);
    if (count = pow2_64_m1) {
      impl_serialize_map_group_valid_map_zero_or_more_snoc_overflow_gen maxl sp1 key_eq sp2 except l m1 m2_ (SZ.v (S.len out));
      pres := false
    } else {
      assert (pure (U64.v count < U64.v pow2_64_m1));
      let count' = U64.add count 1uL;
      let (ck, cv) = next (Iterator.mk_spec r1) (Iterator.mk_spec r2) pc;
      with ke_ va_ . assert (dsnd (Iterator.mk_spec r1) (fst (ck, cv)) ke_ ** dsnd (Iterator.mk_spec r2) (snd (ck, cv)) va_);
      let ke : Ghost.erased tkey = Ghost.hide (Ghost.reveal ke_);
      let va : Ghost.erased tvalue = Ghost.hide (Ghost.reveal va_);
      Trade.rewrite_with_trade
        (dsnd (Iterator.mk_spec r1) (fst (ck, cv)) _ ** dsnd (Iterator.mk_spec r2) (snd (ck, cv)) _)
        (r1 ck ke ** r2 cv va);
      Trade.trans_hyp_l (r1 ck ke ** r2 cv va) _ _ _;
      Trade.trans _ _ (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c0 v0);
      with c2 m2 . assert (r (Iterator.mk_spec r1) (Iterator.mk_spec r2) c2 m2);
      let m2_rem : Ghost.erased (Map.t tkey (list tvalue)) = Ghost.hide (Ghost.reveal m2);
      rel_len #(Iterator.mk_spec r1) #(Iterator.mk_spec r2) _ _;
      impl_serialize_map_group_valid_map_zero_or_more_snoc_gen maxl sp1 key_eq sp2 except l m1 ke va m2_rem (SZ.v (S.len out));
      let mkv : Ghost.erased (Map.t tkey (list tvalue)) = EqTest.map_singleton (Ghost.reveal ke) (Ghost.reveal key_eq ke) [Ghost.reveal va];
      let m2' : Ghost.erased (Map.t tkey (list tvalue)) = map_of_list_cons key_eq (Ghost.reveal ke) (Ghost.reveal va) m2_rem;
      Classical.forall_intro (EqTest.eq_test_unique key_eq);
      assert (pure (m2' == m2_));
      map_of_list_is_append_cons_snoc_equiv key_eq m1 ke va m2_rem v0;
      let m1' : Ghost.erased (Map.t tkey (list tvalue)) = map_of_list_snoc key_eq m1 (Ghost.reveal ke) (Ghost.reveal va);
      let size0 = !out_size;
      with w . assert (pts_to out w);
      Seq.lemma_split w (SZ.v size0);
      let (outl1, out1) = S.split out size0;
      with z1l . assert (pts_to outl1 z1l);
      let sz1 = pa1 ck out1;
      S.pts_to_len out1;
      if (sz1 = 0sz) {
        with w1 . assert (pts_to out1 w1);
        S.pts_to_len out1;
        S.join _ _ out;
        S.pts_to_len out;
        Trade.elim_hyp_l _ _ _;
        impl_serialize_map_zero_or_more_valid_false_sz1_gen pe minl maxl p sp1 key_eq sp2 except l m1 ke va m2_rem v0 (SZ.v (S.len out)) count size0 w_inv w1;
        pres := false
      } else {
        with w1 . assert (pts_to out1 w1);
        S.pts_to_len out1;
        Seq.lemma_split w1 (SZ.v sz1);
        let (outl2, out2) = S.split out1 sz1;
        with z2l . assert (pts_to outl2 z2l);
        S.pts_to_len out2;
        let sz2 = pa2 cv out2;
        with w2 . assert (pts_to out2 w2);
        S.pts_to_len out2;
        S.pts_to_len outl2;
        Trade.elim_hyp_l _ _ _;
        if (sz2 = 0sz) {
          // Value serialization failed — call helper lemma
          S.join _ _ out1;
          S.pts_to_len out1;
          S.pts_to_len outl1;
          S.join _ _ out;
          S.pts_to_len out;
          impl_serialize_map_zero_or_more_valid_false_sz2_gen pe minl maxl p sp1 key_eq sp2 except l m1 ke va m2_rem v0 (SZ.v (S.len out)) count size0 (SZ.v sz1) w_inv (Ghost.reveal z2l) w2;
          pres := false
        } else {
          // Parse key
          let oo1 = parse outl2;
          match oo1 {
            Some oo1s -> {
              let (o1, orem1) = oo1s;
              rewrite (cbor_parse_post (Ghost.reveal pe) vmatch' outl2 1.0R (Ghost.reveal z2l) (Some (o1, orem1)))
                as (cbor_parse_post_some (Ghost.reveal pe) vmatch' outl2 1.0R (Ghost.reveal z2l) o1 orem1);
              unfold (cbor_parse_post_some (Ghost.reveal pe) vmatch' outl2 1.0R (Ghost.reveal z2l) o1 orem1);
              with ke' . assert (vmatch' 1.0R o1 ke');
              with w1'' . assert (pts_to orem1 w1'');
              // Parse value
              let oo2 = parse out2;
              match oo2 {
                Some oo2s -> {
                  let (o2, orem2) = oo2s;
                  rewrite (cbor_parse_post (Ghost.reveal pe) vmatch' out2 1.0R w2 (Some (o2, orem2)))
                    as (cbor_parse_post_some (Ghost.reveal pe) vmatch' out2 1.0R w2 o2 orem2);
                  unfold (cbor_parse_post_some (Ghost.reveal pe) vmatch' out2 1.0R w2 o2 orem2);
                  with va' . assert (vmatch' 1.0R o2 va');
                  with (w2'' : Seq.seq U8.t) . assert (pts_to orem2 w2'');
                  // Establish ke' == sp1.serializer ke and va' == sp2.serializer va
                  // ke': parse on z2l gives pe z2l == Some (ke', _)
                  //       pa1 gives pe z2l == Some (sp1.serializer ke, sz1) since z2l == Seq.slice w1 0 sz1
                  assert (pure (Ghost.reveal ke' == sp1.serializer ke));
                  // va': parse on w2 gives pe w2 == Some (va', _)
                  //       pa2 gives pe (Seq.slice w2 0 sz2) == Some (sp2.serializer va, sz2)
                  //       prefix property: pe w2 == pe (Seq.slice w2 0 sz2)
                  cbor_parse_prefix_apply pe w2 (SZ.v sz2);
                  assert (pure (Ghost.reveal va' == sp2.serializer va));
                  // Make map entry and check except
                  let o = mk_map_entry o1 o2;
                  let is_except = va_ex o;
                  // Give back resources
                  Trade.elim (vmatch2' 1.0R o _) _;
                  Trade.elim (vmatch' 1.0R o2 va' ** pts_to orem2 w2'') (pts_to out2 w2);
                  Trade.elim (vmatch' 1.0R o1 ke' ** pts_to orem1 _) (pts_to outl2 _);
                  S.join outl2 out2 out1;
                  S.join outl1 out1 out;
                  S.pts_to_len out;
                  if (is_except) {
                    // except holds, so valid == false
                    impl_serialize_map_zero_or_more_valid_false_except_gen maxl sp1 key_eq sp2 except l m1 ke va m2_rem v0 (SZ.v (S.len out));
                    pres := false
                  } else {
                    let size1 = SZ.add size0 sz1;
                    let size2 = SZ.add size1 sz2;
                    with w' . assert (pts_to out w');
                    // w' == Seq.append z1l (Seq.append z2l w2) from the joins
                    // z1l = Seq.slice w 0 size0 (from first split)
                    // z2l = Seq.slice w1 0 sz1 (from second split), pe z2l == Some (ke, sz1) from pa1
                    // w2 is out2 content, pe (Seq.slice w2 0 sz2) == Some (va, sz2) from pa2
                    impl_serialize_map_group_insert_prf_gen p pe w (cbor_map_union l (sp.mg_serializer m1)) (SZ.v size0) (sp1.serializer ke) z2l (sp2.serializer va) w2 (SZ.v sz2);
                    assert (pure (
                      let z1l = Seq.slice w 0 (SZ.v size0) in
                      w' == Seq.append z1l (Seq.append (Ghost.reveal z2l) w2)
                    ));
                    assert (pure (
                      impl_serialize_map_group_insert_prf_gen_post p pe w' (cbor_map_union l (sp.mg_serializer m1)) (SZ.v size0) (sp1.serializer ke) (SZ.v sz1) (sp2.serializer va) (SZ.v sz2)
                    ));
                    let (outl, outr) = slice_split out size2;
                    S.pts_to_len outl;
                    S.pts_to_len outr;
                    with wl . assert (pts_to outl wl);
                    with wr . assert (pts_to outr wr);
                    let inserted = insert outl (cbor_map_union l (sp.mg_serializer m1)) size0 (sp1.serializer ke) size1 (sp2.serializer va);
                    S.pts_to_len outl;
                    with wl' . assert (pts_to outl wl');
                    S.join _ _ out;
                    S.pts_to_len out;
                    if (not inserted) {
                      // insert returned false: key already defined in map
                      // From snoc_gen condition 5: valid requires not (defined key l')
                      // insert post gives defined key l', so valid == false
                      impl_serialize_map_group_valid_map_zero_or_more_snoc_gen maxl sp1 key_eq sp2 except l m1 ke va m2_rem (SZ.v (S.len out));
                      pres := false
                    } else {
                      GR.op_Colon_Equals pm1 m1';
                      GR.op_Colon_Equals pm2 m2;
                      out_count := count';
                      out_size := size2;
                      with w_ . assert (pts_to out w_);
                      seq_slice_append_pat wl' wr;
                      // Re-establish invariant
                      // insert postcond: p (cbor_map_length m') wl' == Some (m', Seq.length wl')
                      // where m' = union (union l (sm m1)) (singleton ke va) == union l (sm m1')
                      // and wl' == Seq.slice w_ 0 size2
                      assert (pure (Seq.slice w_ 0 (SZ.v size2) == wl'));
                      assert (pure (cbor_map_length (cbor_map_union l (sp.mg_serializer m1')) == U64.v count'));
                      // prefix prop: p count' wl' == Some(...) and Seq.slice w_ 0 size2 == wl' 
                      // => p count' w_ == Some(...)
                      // Connect insert postcond with snoc_gen
                      assert (pure (
                        cbor_map_union (cbor_map_union l (sp.mg_serializer m1)) (cbor_map_singleton (sp1.serializer ke) (sp2.serializer va)) == cbor_map_union l (sp.mg_serializer m1')
                      ));
                      assert (pure (Seq.length wl' == SZ.v size2));
                      assert (pure (Seq.slice w_ 0 (SZ.v size2) == wl'));
                      assert (pure (Seq.length w_ >= SZ.v size2));
                      // Explicitly instantiate prefix property
                      assert (pure (Seq.equal (Seq.slice wl' 0 (SZ.v size2)) wl'));
                      assert (pure (Seq.slice wl' 0 (SZ.v size2) == Seq.slice w_ 0 (SZ.v size2)));
                      assert (pure (cbor_parse_map_prefix_prop' p (U64.v count') wl' w_));
                      assert (pure (Ghost.reveal p (U64.v count') wl' == Ghost.reveal p (U64.v count') w_));
                      assert (pure (
                        impl_serialize_map_group_pre p count' size2 (cbor_map_union l (sp.mg_serializer m1')) w_
                      ));
                      assert (pure (map_of_list_is_append m1' m2 v0));
                      map_of_list_maps_to_nonempty_snoc key_eq m1 (Ghost.reveal ke) (Ghost.reveal va);
                      assert (pure (map_of_list_maps_to_nonempty m1'));
                      assert (pure (sp.mg_serializable m1'));
                      assert (pure (cbor_map_disjoint l (sp.mg_serializer m1')));
                      ()
                    }
                  }
                }
                None -> {
                  // Value parse None: contradicts pa2's postcondition
                  // pe w2 == None (from parse) but pe (Seq.slice w2 0 sz2) == Some (...) (from pa2)
                  // prefix apply: pe w2 == pe (Seq.slice w2 0 sz2) == Some (...)
                  rewrite (cbor_parse_post (Ghost.reveal pe) vmatch' out2 1.0R w2 None)
                    as (pts_to out2 #1.0R w2 ** pure (None? (Ghost.reveal pe w2)));
                  cbor_parse_prefix_apply pe w2 (SZ.v sz2);
                  assert (pure (Some? (Ghost.reveal pe w2)));
                  assert (pure False);
                  // Give back key resources before joining
                  Trade.elim (vmatch' 1.0R o1 ke' ** pts_to orem1 _) (pts_to outl2 _);
                  S.join outl2 out2 out1;
                  S.join outl1 out1 out;
                  S.pts_to_len out;
                  pres := false
                }
              }
            }
            None -> {
              // Key parse None: contradicts pa1's postcondition
              // pe z2l == None (from parse) but pe z2l == Some (sp1.serializer ke, sz1) (from pa1)
              rewrite (cbor_parse_post (Ghost.reveal pe) vmatch' outl2 1.0R (Ghost.reveal z2l) None)
                as (pts_to outl2 #1.0R (Ghost.reveal z2l) ** pure (None? (Ghost.reveal pe (Ghost.reveal z2l))));
              assert (pure (Some? (Ghost.reveal pe (Ghost.reveal z2l))));
              // Contradiction: None? and Some? on same value
              assert (pure False);
              S.join outl2 out2 out1;
              S.join outl1 out1 out;
              S.pts_to_len out;
              pres := false
            }
          }
        }
      }
    }
  };
  Trade.elim _ _;
  with m1 . assert (GR.pts_to pm1 m1);
  GR.free pm1;
  GR.free pm2;
  Classical.move_requires (map_of_list_is_append_nil_r_elim m1) v0;
  !pres
}

#pop-options

(* Slice iterator types and functions *)

inline_for_extraction
noeq
type map_slice_iterator_t
  (impl_elt1: Type0) (impl_elt2: Type0)
  ([@@@erasable]spec1: Ghost.erased (Iterator.type_spec impl_elt1)) ([@@@erasable]spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: Type0
= {
  base: (slice (impl_elt1 & impl_elt2));
  key_eq: Ghost.erased (EqTest.eq_test (dfst spec1));
}

let rel_map_slice_iterator
  (impl_elt1: Type0) (impl_elt2: Type0)
  (spec1: Ghost.erased (Iterator.type_spec impl_elt1)) (spec2: Ghost.erased (Iterator.type_spec impl_elt2))
: rel (map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2) (Map.t (dfst spec1) (list (dfst spec2)))
= mk_rel (fun s l -> rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) s.key_eq (dsnd spec1) (dsnd spec2) s.base l)

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_is_empty
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_is_empty_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _)
  (spec2: _)
  (s: _)
  (#l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  unfold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  S.pts_to_len s.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false s.base l');
  fold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  s.key_eq (dsnd spec1) (dsnd spec2) s.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 s l);
  Classical.forall_intro (map_of_list_pair_mem_fst s.key_eq l');
  (S.len s.base.s = 0sz)
}

ghost
fn map_slice_iterator_length
  (impl_elt1: Type0) (impl_elt2: Type0)
: rel_map_iterator_length _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (#spec1: _)
  (#spec2: _)
  (i: _)
  (l: _)
{
  unfold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  unfold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  unfold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  S.pts_to_len i.base.s;
  SM.seq_list_match_length (rel_pair (dsnd spec1) (dsnd spec2)) _ _;
  fold (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l');
  fold (rel_slice_of_table  #_ #(dfst spec1) #_ #(dfst spec2)  i.key_eq (dsnd spec1) (dsnd spec2) i.base l);
  fold (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i l);
  ()
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn map_slice_iterator_next
  (impl_elt1: Type0) (impl_elt2: Type0)
: cddl_map_iterator_next_gen_t _ _ (map_slice_iterator_t impl_elt1 impl_elt2) (rel_map_slice_iterator _ _)
= (spec1: _)
  (spec2: _)
  (pi: _)
  (#gi: _)
  (#m: _)
{
  let i = !pi;
  let r : rel (impl_elt1 & impl_elt2) (dfst spec1 & dfst spec2) = (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2));
  Trade.rewrite_with_trade
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m)
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  with l . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l);
  rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i.base l)
    as (rel_slice_of_list r false i.base l);
  unfold (rel_slice_of_list r false i.base l);
  S.pts_to_len i.base.s;
  with s . assert (pts_to i.base.s #i.base.p s);
  SM.seq_list_match_length r _ _;
  Seq.lemma_split s 1;
  SM.seq_list_match_cons_elim _ _ r;
  with gres gv . assert (r gres gv);
  let res = S.op_Array_Access i.base.s 0sz;
  rewrite each gres as res;
  let (il, ir) = S.split i.base.s 1sz;
  with sl . assert (pts_to il #i.base.p sl);
  with sr . assert (pts_to ir #i.base.p sr);
  let i' : map_slice_iterator_t impl_elt1 impl_elt2 spec1 spec2 = {
    base = {
      s = ir;
      p = i.base.p;
    };
    key_eq = i.key_eq;
  };
  rewrite (pts_to ir #(i.base.p) sr) as (pts_to i'.base.s #i'.base.p (Seq.tail s));
  fold (rel_slice_of_list r false i'.base (List.Tot.tl l));
  rewrite (rel_slice_of_list r false i'.base (List.Tot.tl l))
    as (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base (List.Tot.tl l));
  let m' = Ghost.hide (map_of_list_pair i'.key_eq (List.Tot.tl l));
  fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
  Trade.rewrite_with_trade
    (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m')
    (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 i' m');
  intro
    (Trade.trade
      (
        r res gv ** rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m'
      )
      (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m)
    )
    #(S.is_split i.base.s il ir ** pts_to il #i.base.p sl)
    fn _
  {
    unfold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i'.key_eq (dsnd spec1) (dsnd spec2) i'.base m');
    with l' . assert (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l');
    rewrite (rel_slice_of_list (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2)) false i'.base l')
      as (rel_slice_of_list r false i'.base l');
    unfold (rel_slice_of_list r false i'.base l');
    with s' . assert (pts_to i'.base.s #i'.base.p s');
    SM.seq_list_match_cons_intro res (Ghost.reveal gv) s' l' r;
    rewrite (S.is_split i.base.s il ir) as (S.is_split i.base.s il i'.base.s);
    S.join il i'.base.s i.base.s;
    with sj . assert (pts_to i.base.s #i.base.p sj);
    assert (pure (Seq.equal sj (Seq.cons (Seq.index s 0) s')));
    rewrite each (Seq.cons (Seq.index s 0) s') as sj;
    fold (rel_slice_of_list
      (rel_pair #_ #(dfst spec1) (dsnd spec1) #_ #(dfst spec2) (dsnd spec2))
      false
      i.base
      (Ghost.reveal gv :: l')
    );
    fold (rel_slice_of_table #_ #(dfst spec1) #_ #(dfst spec2) i.key_eq (dsnd spec1) (dsnd spec2) i.base m);
  };
  Trade.trans_hyp_r _ _ _ _;
  Trade.trans _ _ (rel_map_slice_iterator impl_elt1 impl_elt2 spec1 spec2 gi m);
  Trade.rewrite_with_trade
    (r res gv)
    (dsnd spec1 (fst res) (fst gv) ** dsnd spec2 (snd res) (snd gv));
  Trade.trans_hyp_l _ (r res gv) _ _;
  pi := i';
  res
}

(* Slice sub-implementation *)

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_serialize_map_zero_or_more_slice
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#[@@@erasable]key: Ghost.erased typ)
    (#[@@@erasable]tkey: Type0)
    ([@@@erasable]key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#[@@@erasable]sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#[@@@erasable]r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#[@@@erasable]value: Ghost.erased typ)
    (#[@@@erasable]tvalue: Type0)
    (#[@@@erasable]inj: Ghost.erased bool)
    (#[@@@erasable]sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#[@@@erasable]r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#[@@@erasable]except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_slice_of_table key_eq r1 r2)
=
    (c0: _)
    (#v0: _)
    (out: _)
    (out_count: _)
    (out_size: _)
    (l: _)
{
  let i : map_slice_iterator_t ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) = {
    base = c0;
    key_eq = key_eq;
  };
  Trade.rewrite_with_trade
    (rel_slice_of_table key_eq r1 r2 c0 v0)
    (rel_map_slice_iterator ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2) i v0);
  let mut pi = i;
  let res = impl_serialize_map_zero_or_more_iterator_gen
    parse
    mk_map_entry
    insert
    key_eq
    pa1
    pa2
    va_ex
    (map_slice_iterator_t _ _)
    (rel_map_slice_iterator _ _)
    (map_slice_iterator_is_empty _ _)
    (map_slice_iterator_next _ _)
    (map_slice_iterator_length _ _)
    i
    out
    out_count
    out_size
    l;
  Trade.elim _ _;
  res
}

(* Iterator sub-implementation *)

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_serialize_map_zero_or_more_iterator
  (#pe: Ghost.erased cbor_parser)
  (#minl: Ghost.erased (cbor_min_length pe))
  (#maxl: Ghost.erased (cbor_max_length pe))
  (#p: Ghost.erased (cbor_map_parser minl maxl))
  (#ty: Type0) (#vmatch: perm -> ty -> cbor -> slprop)
  (#cbor_map_iterator_t: Type0) (#cbor_map_iterator_match: perm -> cbor_map_iterator_t -> list (cbor & cbor) -> slprop)
  (#ty2: Type0) (#vmatch2: perm -> ty2 -> (cbor & cbor) -> slprop)
  (map_share: share_t cbor_map_iterator_match)
  (map_gather: gather_t cbor_map_iterator_match)
  (map_is_empty: map_iterator_is_empty_t cbor_map_iterator_match)
  (map_next: map_iterator_next_t vmatch2 cbor_map_iterator_match)
  (map_entry_key: map_entry_key_t vmatch2 vmatch)
  (map_entry_value: map_entry_value_t vmatch2 vmatch)
  (map_entry_share: share_t vmatch2)
  (map_entry_gather: gather_t vmatch2)
  (#ty': Type0) (#vmatch': perm -> ty' -> cbor -> slprop)
  (#ty2': Type0) (#vmatch2': perm -> ty2' -> cbor & cbor -> slprop)
  (parse: cbor_parse_t pe vmatch')
  (mk_map_entry: mk_map_entry_t vmatch' vmatch2')
  (insert: cbor_serialize_map_insert_t p pe)
    (#key: Ghost.erased typ)
    (#tkey: Type0)
    (key_eq: Ghost.erased (EqTest.eq_test tkey))
    (#sp1: Ghost.erased (spec key tkey true))
    (#ikey: Type0)
    (#r1: rel ikey tkey)
    (pa1: impl_serialize minl maxl sp1 r1)
    (#value: Ghost.erased typ)
    (#tvalue: Type0)
    (#inj: Ghost.erased bool)
    (#sp2: Ghost.erased (spec value tvalue inj))
    (#ivalue: Type0)
    (#r2: rel ivalue tvalue)
    (pa2: impl_serialize minl maxl sp2 r2)
    (#except: Ghost.erased map_constraint { map_constraint_value_injective key sp2.parser except })
    (va_ex: impl_map_entry_cond vmatch2' except)
: impl_serialize_map_group p minl maxl #(map_group_filtered_table key value except) #_ #_ #_ (mg_zero_or_more_match_item sp1 sp2 except) #_ (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match ikey ivalue (Iterator.mk_spec r1) (Iterator.mk_spec r2))
= impl_serialize_map_zero_or_more_iterator_gen
    parse
    mk_map_entry
    insert
    key_eq
    pa1
    pa2
    va_ex
    (map_iterator_t cbor_map_iterator_t _ _ vmatch vmatch2)
    (rel_map_iterator vmatch vmatch2 cbor_map_iterator_match _ _)
    (cddl_map_iterator_is_empty map_is_empty map_next map_entry_key map_entry_value _ _)
    (cddl_map_iterator_next map_share map_gather map_next map_entry_key map_entry_value map_entry_share map_entry_gather _ _)
    (rel_map_iterator_prop' cbor_map_iterator_match)

(* Final composition: impl_serialize_map_zero_or_more *)

let impl_serialize_map_zero_or_more
  #pe #minl #maxl #p #ty #vmatch #cbor_map_iterator_t #cbor_map_iterator_match #ty2 #vmatch2
  map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather
  #ty' #ty2' #vmatch' #vmatch2'
  parse mk_map_entry insert #key #tkey key_eq #sp1 #ikey #r1 pa1 #value #tvalue #inj #sp2 #ivalue #r2 pa2 #except va_ex
= impl_serialize_map_group_either_left
    (impl_serialize_map_zero_or_more_slice
      parse mk_map_entry insert key_eq pa1 pa2 va_ex)
    (impl_serialize_map_zero_or_more_iterator
      map_share map_gather map_is_empty map_next map_entry_key map_entry_value map_entry_share map_entry_gather
      parse mk_map_entry insert key_eq pa1 pa2 va_ex)
