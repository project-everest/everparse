module CBOR.Pulse.Raw.Match.Perm
open CBOR.Pulse.Raw.Util

```pulse
ghost
fn rec cbor_raw_share_array
  (p: perm)
  (c: Seq.seq cbor_raw)
  (r: list raw_data_item)
  (cbor_raw_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (r': raw_data_item { r' << r }) ->
    stt_ghost unit emp_inames
      (cbor_match p' c' r')
      (fun _ -> cbor_match (p' /. 2.0R) c' r' **
        cbor_match (p' /. 2.0R) c' r'
      )
  ))
  (_: unit)
requires
  PM.seq_list_match c r (cbor_match p)
ensures
  PM.seq_list_match c r (cbor_match (p /. 2.0R)) **
  PM.seq_list_match c r (cbor_match (p /. 2.0R))
decreases r
{
  match r {
    Nil -> {
      PM.seq_list_match_nil_elim c r (cbor_match p);
      PM.seq_list_match_nil_intro c r (cbor_match (p /. 2.0R));      
      PM.seq_list_match_nil_intro c r (cbor_match (p /. 2.0R))
    }
    a :: q -> {
      PM.seq_list_match_cons_elim c r (cbor_match p);
      cbor_raw_share p (Seq.head c) a;
      cbor_raw_share_array p (Seq.tail c) q cbor_raw_share ();
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match (p /. 2.0R));
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match (p /. 2.0R));
    }
  }
}
```

```pulse
ghost
fn rec cbor_raw_share_map
  (r0: raw_data_item)
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (r: list (raw_data_item & raw_data_item) { r << r0 }) 
  (cbor_raw_share: (
    (p': perm) ->
    (c': cbor_raw) ->
    (r': raw_data_item { r' << r0 }) ->
    stt_ghost unit emp_inames
      (cbor_match p' c' r')
      (fun _ -> cbor_match (p' /. 2.0R) c' r' **
        cbor_match (p' /. 2.0R) c' r'
      )
  ))
  (_: unit)
requires
  PM.seq_list_match c r (cbor_match_map_entry0 r0 (cbor_match p))
ensures
  PM.seq_list_match c r (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R))) **
  PM.seq_list_match c r (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)))
decreases r
{
  match r {
    Nil -> {
      PM.seq_list_match_nil_elim c r (cbor_match_map_entry0 r0 (cbor_match p));
      PM.seq_list_match_nil_intro c r (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)));
      PM.seq_list_match_nil_intro c r (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)));
    }
    a :: q -> {
      PM.seq_list_match_cons_elim c r (cbor_match_map_entry0 r0 (cbor_match p));
      unfold (cbor_match_map_entry0 r0 (cbor_match p) (Seq.head c) a);
      cbor_raw_share p (Seq.head c).cbor_map_entry_key (fst a);
      cbor_raw_share p (Seq.head c).cbor_map_entry_value (snd a);
      fold (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)) (Seq.head c) a);
      fold (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)) (Seq.head c) a);
      cbor_raw_share_map r0 p (Seq.tail c) q cbor_raw_share ();
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)));
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)));
    }
  }
}
```

```pulse
ghost
fn rec cbor_raw_share
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
  requires
    cbor_match p c r
  ensures
    cbor_match (p /. 2.0R) c r **
    cbor_match (p /. 2.0R) c r
  decreases r
{
  cbor_match_cases c;
  match c {
    CBOR_Case_String v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_string v p r);
      unfold (cbor_match_string v p r);
      S.share v.cbor_string_ptr;
      half_mul_l p v.cbor_string_perm;
      fold (cbor_match_string v (p /. 2.0R) r);
      fold (cbor_match_string v (p /. 2.0R) r);
      rewrite (cbor_match_string v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      rewrite (cbor_match_string v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r)
    }
    CBOR_Case_Int v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_int v r);
      unfold (cbor_match_int v r);
      fold (cbor_match_int v r);
      rewrite (cbor_match_int v r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_int v r);
      rewrite (cbor_match_int v r)
        as (cbor_match (p /. 2.0R) c r)
    }
    CBOR_Case_Simple v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_simple v r);
      unfold (cbor_match_simple v r);
      fold (cbor_match_simple v r);
      rewrite (cbor_match_simple v r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_simple v r);
      rewrite (cbor_match_simple v r)
        as (cbor_match (p /. 2.0R) c r)
    }
    CBOR_Case_Tagged v -> {
      cbor_match_eq_tagged p v r;
      rewrite (cbor_match p c r)
        as (cbor_match_tagged v p r cbor_match);
      unfold (cbor_match_tagged v p r cbor_match);
      cbor_raw_share _ _ _;
      R.share v.cbor_tagged_ptr;
      half_mul_l p v.cbor_tagged_ref_perm;
      half_mul_l p v.cbor_tagged_payload_perm;
      fold (cbor_match_tagged v (p /. 2.0R) r cbor_match);
      cbor_match_eq_tagged (p /. 2.0R) v r;
      rewrite (cbor_match_tagged v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_tagged v (p /. 2.0R) r cbor_match);
      rewrite (cbor_match_tagged v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r)
    }
    CBOR_Case_Array v -> {
      cbor_match_eq_array p v r;
      rewrite (cbor_match p c r)
        as (cbor_match_array v p r cbor_match);
      unfold (cbor_match_array v p r cbor_match);
      S.share v.cbor_array_ptr;
      cbor_raw_share_array _ _ (Array?.v r) cbor_raw_share ();
      half_mul_l p v.cbor_array_array_perm;
      half_mul_l p v.cbor_array_payload_perm;
      fold (cbor_match_array v (p /. 2.0R) r cbor_match);
      cbor_match_eq_array (p /. 2.0R) v r;
      rewrite (cbor_match_array v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_array v (p /. 2.0R) r cbor_match);
      rewrite (cbor_match_array v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r)
    }
    CBOR_Case_Map v -> {
      cbor_match_eq_map0 p v r;
      rewrite (cbor_match p c r)
        as (cbor_match_map0 v p r cbor_match);
      unfold (cbor_match_map0 v p r cbor_match);
      S.share v.cbor_map_ptr;
      cbor_raw_share_map r _ _ (Map?.v r) cbor_raw_share ();
      half_mul_l p v.cbor_map_array_perm;
      half_mul_l p v.cbor_map_payload_perm;
      fold (cbor_match_map0 v (p /. 2.0R) r cbor_match);
      cbor_match_eq_map0 (p /. 2.0R) v r;
      rewrite (cbor_match_map0 v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_map0 v (p /. 2.0R) r cbor_match);
      rewrite (cbor_match_map0 v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r)
    }
    CBOR_Case_Serialized_Tagged v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_serialized_tagged v p r);
      unfold (cbor_match_serialized_tagged v p r);
      cbor_match_serialized_payload_tagged_share _ _ _;
      half_mul_l p v.cbor_serialized_perm;
      fold (cbor_match_serialized_tagged v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_tagged v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_serialized_tagged v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_tagged v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
    }
    CBOR_Case_Serialized_Array v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_serialized_array v p r);
      unfold (cbor_match_serialized_array v p r);
      cbor_match_serialized_payload_array_share _ _ _;
      half_mul_l p v.cbor_serialized_perm;
      fold (cbor_match_serialized_array v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_array v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_serialized_array v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_array v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
    }
    CBOR_Case_Serialized_Map v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_serialized_map v p r);
      unfold (cbor_match_serialized_map v p r);
      cbor_match_serialized_payload_map_share _ _ _;
      half_mul_l p v.cbor_serialized_perm;
      fold (cbor_match_serialized_map v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_map v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_serialized_map v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_map v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
    }
  }
}
```

```pulse
ghost
fn rec cbor_raw_gather_array
  (p1: perm)
  (c: Seq.seq cbor_raw)
  (r1: list raw_data_item)
  (p2: perm)
  (r2: list raw_data_item)
  (cbor_raw_gather: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (r1': raw_data_item) ->
    (p2': perm) ->
    (r2': raw_data_item { r1' << r1 }) ->
    stt_ghost unit emp_inames
      (cbor_match p1' c' r1' ** cbor_match p2' c' r2')
      (fun _ -> cbor_match (p1' +. p2') c' r1' **
        pure (r1' == r2')
      )
  ))
  (_: unit)
requires
  PM.seq_list_match c r1 (cbor_match (p1)) **
  PM.seq_list_match c r2 (cbor_match (p2))
ensures
  PM.seq_list_match c r1 (cbor_match (p1 +. p2)) **
  pure (r1 == r2)
decreases r1
{
  match r1 {
    Nil -> {
      PM.seq_list_match_nil_elim c r1 (cbor_match p1);
      PM.seq_list_match_nil_elim c r2 (cbor_match p2);
      PM.seq_list_match_nil_intro c r1 (cbor_match (p1 +. p2));
    }
    a1 :: q1 -> {
      PM.seq_list_match_cons_elim c r1 (cbor_match p1);
      PM.seq_list_match_cons_elim c r2 (cbor_match p2);
      let a2 = List.Tot.hd r2;
      let q2 = List.Tot.tl r2;
      cbor_raw_gather p1 (Seq.head c) a1 p2 a2;
      cbor_raw_gather_array p1 (Seq.tail c) q1 p2 q2 cbor_raw_gather ();
      PM.seq_list_match_cons_intro (Seq.head c) a1 (Seq.tail c) q1 (cbor_match (p1 +. p2));
    }
  }
}
```

```pulse
ghost
fn rec cbor_raw_gather_map
  (r01: raw_data_item)
  (p1: perm)
  (c: Seq.seq cbor_map_entry)
  (r1: list (raw_data_item & raw_data_item) { r1 << r01 })
  (r02: raw_data_item)
  (p2: perm)
  (r2: list (raw_data_item & raw_data_item) { r2 << r02 })
  (cbor_raw_gather: (
    (p1': perm) ->
    (c': cbor_raw) ->
    (r1': raw_data_item) ->
    (p2': perm) ->
    (r2': raw_data_item { r1' << r01 }) ->
    stt_ghost unit emp_inames
      (cbor_match p1' c' r1' ** cbor_match p2' c' r2')
      (fun _ -> cbor_match (p1' +. p2') c' r1' **
        pure (r1' == r2')
      )
  ))
  (_: unit)
requires
  PM.seq_list_match c r1 (cbor_match_map_entry0 r01 (cbor_match (p1))) **
  PM.seq_list_match c r2 (cbor_match_map_entry0 r02 (cbor_match (p2)))
ensures
  PM.seq_list_match c r1 (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2))) **
  pure ((r1 <: list (raw_data_item & raw_data_item)) == (r2 <: list (raw_data_item & raw_data_item)))
decreases r1
{
  match r1 {
    Nil -> {
      PM.seq_list_match_nil_elim c r1 (cbor_match_map_entry0 r01 (cbor_match (p1)));
      PM.seq_list_match_nil_elim c r2 (cbor_match_map_entry0 r02 (cbor_match (p2)));
      PM.seq_list_match_nil_intro c r1 (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2)));
    }
    a1 :: q1 -> {
      PM.seq_list_match_cons_elim c r1 (cbor_match_map_entry0 r01 (cbor_match (p1)));
      PM.seq_list_match_cons_elim c r2 (cbor_match_map_entry0 r02 (cbor_match (p2)));
      let a2 = List.Tot.hd r2;
      let q2 = List.Tot.tl r2;
      unfold (cbor_match_map_entry0 r01 (cbor_match p1) (Seq.head c) a1);
      unfold (cbor_match_map_entry0 r02 (cbor_match p2) (Seq.head c) a2);
      cbor_raw_gather p1 (Seq.head c).cbor_map_entry_key (fst a1) p2 (fst a2);
      cbor_raw_gather p1 (Seq.head c).cbor_map_entry_value (snd a1) p2 (snd a2);
      fold (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2)) (Seq.head c) a1);
      cbor_raw_gather_map r01 p1 (Seq.tail c) q1 r02 p2 q2 cbor_raw_gather ();
      PM.seq_list_match_cons_intro (Seq.head c) a1 (Seq.tail c) q1 (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2)));
    }
  }
}
```

```pulse
ghost
fn rec cbor_raw_gather
  (p1: perm)
  (c: cbor_raw)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
  requires
    cbor_match p1 c r1 **
    cbor_match p2 c r2
  ensures
    cbor_match (p1 +. p2) c r1 **
    pure (r1 == r2)
  decreases r1
{
  cbor_match_cases c #p1;
  cbor_match_cases c #p2;
  match c {
    CBOR_Case_String v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_string v p1 r1);
      unfold (cbor_match_string v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_string v p2 r2);
      unfold (cbor_match_string v p2 r2);
      S.gather v.cbor_string_ptr;
      perm_mul_add_l p1 p2 v.cbor_string_perm;
      fold (cbor_match_string v (p1 +. p2) r1);
      rewrite (cbor_match_string v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Int v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_int v r1);
      unfold (cbor_match_int v r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_int v r2);
      unfold (cbor_match_int v r2);
      fold (cbor_match_int v r1);
      rewrite (cbor_match_int v r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Simple v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_simple v r1);
      unfold (cbor_match_simple v r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_simple v r2);
      unfold (cbor_match_simple v r2);
      fold (cbor_match_simple v r1);
      rewrite (cbor_match_simple v r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Tagged v -> {
      cbor_match_eq_tagged p1 v r1;
      rewrite (cbor_match p1 c r1)
        as (cbor_match_tagged v p1 r1 cbor_match);
      unfold (cbor_match_tagged v p1 r1 cbor_match);
      cbor_match_eq_tagged p2 v r2;
      rewrite (cbor_match p2 c r2)
        as (cbor_match_tagged v p2 r2 cbor_match);
      unfold (cbor_match_tagged v p2 r2 cbor_match);
      R.gather v.cbor_tagged_ptr;
      cbor_raw_gather _ _ (Tagged?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_tagged_ref_perm;
      perm_mul_add_l p1 p2 v.cbor_tagged_payload_perm;
      fold (cbor_match_tagged v (p1 +. p2) r1 cbor_match);
      cbor_match_eq_tagged (p1 +. p2) v r1;
      rewrite (cbor_match_tagged v (p1 +. p2) r1 cbor_match)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Array v -> {
      cbor_match_eq_array p1 v r1;
      rewrite (cbor_match p1 c r1)
        as (cbor_match_array v p1 r1 cbor_match);
      unfold (cbor_match_array v p1 r1 cbor_match);
      cbor_match_eq_array p2 v r2;
      rewrite (cbor_match p2 c r2)
        as (cbor_match_array v p2 r2 cbor_match);
      unfold (cbor_match_array v p2 r2 cbor_match);
      S.gather v.cbor_array_ptr;
      cbor_raw_gather_array _ _ (Array?.v r1) _ _ cbor_raw_gather ();
      perm_mul_add_l p1 p2 v.cbor_array_array_perm;
      perm_mul_add_l p1 p2 v.cbor_array_payload_perm;
      fold (cbor_match_array v (p1 +. p2) r1 cbor_match);
      cbor_match_eq_array (p1 +. p2) v r1;
      rewrite (cbor_match_array v (p1 +. p2) r1 cbor_match)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Map v -> {
      cbor_match_eq_map0 p1 v r1;
      rewrite (cbor_match p1 c r1)
        as (cbor_match_map0 v p1 r1 cbor_match);
      unfold (cbor_match_map0 v p1 r1 cbor_match);
      cbor_match_eq_map0 p2 v r2;
      rewrite (cbor_match p2 c r2)
        as (cbor_match_map0 v p2 r2 cbor_match);
      unfold (cbor_match_map0 v p2 r2 cbor_match);
      S.gather v.cbor_map_ptr;
      cbor_raw_gather_map r1 _ _ (Map?.v r1) r2 _ _ cbor_raw_gather ();
      perm_mul_add_l p1 p2 v.cbor_map_array_perm;
      perm_mul_add_l p1 p2 v.cbor_map_payload_perm;
      fold (cbor_match_map0 v (p1 +. p2) r1 cbor_match);
      cbor_match_eq_map0 (p1 +. p2) v r1;
      rewrite (cbor_match_map0 v (p1 +. p2) r1 cbor_match)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Serialized_Tagged v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_serialized_tagged v p1 r1);
      unfold (cbor_match_serialized_tagged v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_serialized_tagged v p2 r2);
      unfold (cbor_match_serialized_tagged v p2 r2);
      cbor_match_serialized_payload_tagged_gather _ _ (Tagged?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_serialized_perm;
      fold (cbor_match_serialized_tagged v (p1 +. p2) r1);
      rewrite (cbor_match_serialized_tagged v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Serialized_Array v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_serialized_array v p1 r1);
      unfold (cbor_match_serialized_array v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_serialized_array v p2 r2);
      unfold (cbor_match_serialized_array v p2 r2);
      cbor_match_serialized_payload_array_gather _ _ (Array?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_serialized_perm;
      fold (cbor_match_serialized_array v (p1 +. p2) r1);
      rewrite (cbor_match_serialized_array v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Serialized_Map v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_serialized_map v p1 r1);
      unfold (cbor_match_serialized_map v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_serialized_map v p2 r2);
      unfold (cbor_match_serialized_map v p2 r2);
      cbor_match_serialized_payload_map_gather _ _ (Map?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_serialized_perm;
      fold (cbor_match_serialized_map v (p1 +. p2) r1);
      rewrite (cbor_match_serialized_map v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
  }
}
```
