module CBOR.Pulse.Raw.Match.Perm
#lang-pulse
open CBOR.Pulse.Raw.Util

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
      cbor_raw_share p (Seq.head c) _;
      cbor_raw_share_array p (Seq.tail c) q cbor_raw_share ();
      PM.seq_list_match_cons_intro (Seq.head c) _ (Seq.tail c) q (cbor_match (p /. 2.0R));
      PM.seq_list_match_cons_intro (Seq.head c) _ (Seq.tail c) q (cbor_match (p /. 2.0R));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

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
      rewrite each (List.Tot.Base.hd r) as a;
      unfold (cbor_match_map_entry0 r0 (cbor_match p) (Seq.head c) a);
      cbor_raw_share p (Seq.head c).cbor_map_entry_key (fst a);
      cbor_raw_share p (Seq.head c).cbor_map_entry_value (snd a);
      fold (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)) (Seq.head c) a);
      fold (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)) (Seq.head c) a);
      cbor_raw_share_map r0 p (Seq.tail c) q cbor_raw_share ();
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)));
      PM.seq_list_match_cons_intro (Seq.head c) a (Seq.tail c) q (cbor_match_map_entry0 r0 (cbor_match (p /. 2.0R)));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

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
    norewrite
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
    norewrite
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
    norewrite
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
    norewrite
    CBOR_Case_Tagged v -> {
      cbor_match_eq_tagged p v r;
      rewrite (cbor_match p c r)
        as (cbor_match_tagged v p r cbor_match);
      unfold (cbor_match_tagged v p r cbor_match);
      cbor_raw_share _ _ _;
      R.share v.cbor_tagged_ptr;
      half_mul_l p v.cbor_tagged_ref_perm;
      half_mul_l p v.cbor_tagged_payload_perm;
      with c' . rewrite cbor_match (perm_mul p v.cbor_tagged_payload_perm /. 2.0R) c' (Tagged?.v r) as cbor_match (perm_mul (p /. 2.0R) v.cbor_tagged_payload_perm) c' (Tagged?.v r);
      fold (cbor_match_tagged v (p /. 2.0R) r cbor_match);
      cbor_match_eq_tagged (p /. 2.0R) v r;
      with c' . rewrite cbor_match (perm_mul p v.cbor_tagged_payload_perm /. 2.0R) c' (Tagged?.v r) as cbor_match (perm_mul (p /. 2.0R) v.cbor_tagged_payload_perm) c' (Tagged?.v r);
      fold (cbor_match_tagged v (p /. 2.0R) r cbor_match);
      rewrite (cbor_match_tagged v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r);
      rewrite (cbor_match_tagged v (p /. 2.0R) r cbor_match)
        as (cbor_match (p /. 2.0R) c r)
    }
    norewrite
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
    norewrite
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
    norewrite
    CBOR_Case_Serialized_Tagged v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_serialized_tagged v p r);
      unfold (cbor_match_serialized_tagged v p r);
      cbor_match_serialized_payload_tagged_share _ _ _;
      half_mul_l p v.cbor_serialized_perm;
      rewrite each cbor_match_serialized_payload_tagged v.cbor_serialized_payload
        (perm_mul p v.cbor_serialized_perm /. 2.0R)
        (Tagged?.v r) as cbor_match_serialized_payload_tagged v.cbor_serialized_payload
        (perm_mul (p /. 2.0R) v.cbor_serialized_perm)
        (Tagged?.v r);
      fold (cbor_match_serialized_tagged v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_tagged v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_serialized_tagged v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_tagged v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_serialized_array v p r);
      unfold (cbor_match_serialized_array v p r);
      cbor_match_serialized_payload_array_share _ _ _;
      half_mul_l p v.cbor_serialized_perm;
      rewrite each cbor_match_serialized_payload_array v.cbor_serialized_payload
      (perm_mul p v.cbor_serialized_perm /. 2.0R)
      (Array?.v r)
       as cbor_match_serialized_payload_array v.cbor_serialized_payload
      (perm_mul (p /. 2.0R) v.cbor_serialized_perm)
      (Array?.v r);
      fold (cbor_match_serialized_array v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_array v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_serialized_array v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_array v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
    }
    norewrite
    CBOR_Case_Serialized_Map v -> {
      rewrite (cbor_match p c r)
        as (cbor_match_serialized_map v p r);
      unfold (cbor_match_serialized_map v p r);
      cbor_match_serialized_payload_map_share _ _ _;
      half_mul_l p v.cbor_serialized_perm;
      rewrite each cbor_match_serialized_payload_map v.cbor_serialized_payload
      (perm_mul p v.cbor_serialized_perm /. 2.0R)
      (Map?.v r)
       as cbor_match_serialized_payload_map v.cbor_serialized_payload
      (perm_mul (p /. 2.0R) v.cbor_serialized_perm)
      (Map?.v r);
      fold (cbor_match_serialized_map v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_map v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
      fold (cbor_match_serialized_map v (p /. 2.0R) r);
      rewrite (cbor_match_serialized_map v (p /. 2.0R) r)
        as (cbor_match (p /. 2.0R) c r);
    }
  }
}

ghost
fn rec __cbor_raw_gather_array
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
    [] -> {
      PM.seq_list_match_nil_elim c [] (cbor_match p1);
      PM.seq_list_match_nil_elim c r2 (cbor_match p2);
      PM.seq_list_match_nil_intro c r1 (cbor_match (p1 +. p2));
    }
    a1 :: q1 -> {
      PM.seq_list_match_cons_elim c (a1 :: q1) (cbor_match p1);
      PM.seq_list_match_cons_elim c r2 (cbor_match p2);
      let a2 :: q2 = r2;
      cbor_raw_gather p1 (Seq.head c) a1 p2 a2;
      __cbor_raw_gather_array p1 (Seq.tail c) q1 p2 q2 cbor_raw_gather ();
      PM.seq_list_match_cons_intro (Seq.head c) a1 (Seq.tail c) q1 (cbor_match (p1 +. p2));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ()
    }
  }
}

ghost
fn cbor_raw_gather_array
  (p1: perm)
  (c: cbor_array)
  (r1: raw_data_item {Array? r1})
  (p2: perm)
  (r2: raw_data_item {Array? r2})
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
  cbor_match_array c p1 r1 cbor_match **
  cbor_match_array c p2 r2 cbor_match
ensures
  cbor_match_array c (p1 +. p2) r1 cbor_match **
  pure (r1 == r2)
decreases r1
{
  unfold cbor_match_array c p1 r1 cbor_match;
  with v1 _pm1. assert S.pts_to c.cbor_array_ptr #_pm1 v1;
  unfold cbor_match_array c p2 r2 cbor_match;
  with v2 _pm2. assert S.pts_to c.cbor_array_ptr #_pm1 v1 ** S.pts_to c.cbor_array_ptr #_pm2 v2;
  (* ^note: asserting the previous one to disambiguate *)
  assert PM.seq_list_match v1 (Array?.v r1) (cbor_match (p1 `perm_mul` c.cbor_array_payload_perm));
  assert PM.seq_list_match v2 (Array?.v r2) (cbor_match (p2 `perm_mul` c.cbor_array_payload_perm));
  S.gather c.cbor_array_ptr #_ #_ #_pm1 #_pm2; // This is @@allow_ambiguous, but we want the permissions added in the right order (sigh)
  assert (pure (v1 == v2));
  rewrite each v2 as v1;
  __cbor_raw_gather_array _ v1 (Array?.v r1) _ _ cbor_raw_gather ();
  perm_mul_add_l p1 p2 c.cbor_array_array_perm;
  perm_mul_add_l p1 p2 c.cbor_array_payload_perm;
  rewrite each (p1 `perm_mul` c.cbor_array_payload_perm +. p2 `perm_mul` c.cbor_array_payload_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_array_payload_perm);
  rewrite each (p1 `perm_mul` c.cbor_array_array_perm +. p2 `perm_mul` c.cbor_array_array_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_array_array_perm);
  fold cbor_match_array c (p1 +. p2) r1 cbor_match;
  ();
}

ghost
fn rec __cbor_raw_gather_map0
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
    [] -> {
      PM.seq_list_match_nil_elim c [] (cbor_match_map_entry0 r01 (cbor_match (p1)));
      PM.seq_list_match_nil_elim c r2 (cbor_match_map_entry0 r02 (cbor_match (p2)));
      PM.seq_list_match_nil_intro c r1 (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2)));
    }
    a1 :: q1 -> {
      PM.seq_list_match_cons_elim c (a1 :: q1) (cbor_match_map_entry0 r01 (cbor_match (p1)));
      PM.seq_list_match_cons_elim c r2 (cbor_match_map_entry0 r02 (cbor_match (p2)));
      let a2 :: q2 = r2;
      unfold (cbor_match_map_entry0 r02 (cbor_match p2) (Seq.head c) a2);
      unfold (cbor_match_map_entry0 r01 (cbor_match p1) (Seq.head c) a1);
      cbor_raw_gather p1 (Seq.head c).cbor_map_entry_key (fst a1) p2 (fst a2);
      cbor_raw_gather p1 (Seq.head c).cbor_map_entry_value (snd a1) p2 (snd a2);
      fold (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2)) (Seq.head c) a1);
      __cbor_raw_gather_map0 r01 p1 (Seq.tail c) q1 r02 p2 q2 cbor_raw_gather ();
      PM.seq_list_match_cons_intro (Seq.head c) a1 (Seq.tail c) q1 (cbor_match_map_entry0 r01 (cbor_match (p1 +. p2)));
      rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
      ();
    }
  }
}

ghost
fn cbor_raw_gather_map
  (p1: perm)
  (c: cbor_map)
  (r1: raw_data_item {Map? r1 })
  (p2: perm)
  (r2: raw_data_item {Map? r2})
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
  cbor_match_map0 c p1 r1 cbor_match **
  cbor_match_map0 c p2 r2 cbor_match
ensures
  cbor_match_map0 c (p1 +. p2) r1 cbor_match **
  pure (eq2 #raw_data_item r1 r2)
decreases r1
{
  unfold cbor_match_map0 c p1 r1 cbor_match;
  with v1 _pm1. assert S.pts_to c.cbor_map_ptr #_pm1 v1;
  unfold cbor_match_map0 c p2 r2 cbor_match;
  with v2 _pm2. assert S.pts_to c.cbor_map_ptr #_pm1 v1 ** S.pts_to c.cbor_map_ptr #_pm2 v2;
  (* ^note: asserting the previous one to disambiguate *)
  assert PM.seq_list_match v1 (Map?.v r1) (cbor_match_map_entry0 r1 (cbor_match (p1 `perm_mul` c.cbor_map_payload_perm)));
  assert PM.seq_list_match v2 (Map?.v r2) (cbor_match_map_entry0 r2 (cbor_match (p2 `perm_mul` c.cbor_map_payload_perm)));
  S.gather c.cbor_map_ptr #_ #_ #_pm1 #_pm2; // This is @@allow_ambiguous, but we want the permissions added in the right order (sigh)
  assert (pure (v1 == v2));
  rewrite each v2 as v1;
  __cbor_raw_gather_map0 r1 _ v1 (Map?.v r1) r2 _ (Map?.v r2) cbor_raw_gather ();
  perm_mul_add_l p1 p2 c.cbor_map_payload_perm;
  perm_mul_add_l p1 p2 c.cbor_map_array_perm;
  rewrite each (p1 `perm_mul` c.cbor_map_payload_perm +. p2 `perm_mul` c.cbor_map_payload_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_map_payload_perm);
  rewrite each (p1 `perm_mul` c.cbor_map_array_perm +. p2 `perm_mul` c.cbor_map_array_perm)
            as ((p1 +. p2) `perm_mul` c.cbor_map_array_perm);
  fold cbor_match_map0 c (p1 +. p2) r1 cbor_match;
  ();
}

(* This function is quite complicated to work with in Pulse. It would
be good to find a better way of writing this. *)
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
      unfold cbor_match p1 (CBOR_Case_String v) r1;
      unfold cbor_match p2 (CBOR_Case_String v) r2;
      let String t1 l1 v1 = r1;
      let String t2 l2 v2 = r2;
      unfold cbor_match_string v p1 (String t1 l1 v1);
      unfold cbor_match_string v p2 (String t2 l2 v2);
      S.gather v.cbor_string_ptr;
      assert (pure (r1 == r2));
      perm_mul_add_l p1 p2 v.cbor_string_perm;
      fold cbor_match_string v (p1 +. p2) (String t1 l1 v1);
      fold cbor_match (p1 +. p2) (CBOR_Case_String v) (String t1 l1 v1);
      rewrite cbor_match (p1 +. p2) (CBOR_Case_String v) (String t1 l1 v1) as cbor_match (p1 +. p2) c r1;
      ()
    }
    CBOR_Case_Int v -> {
      unfold cbor_match p1 (CBOR_Case_Int v) r1;
      unfold cbor_match p2 (CBOR_Case_Int v) r2;
      let Int64 t1 v1 = r1;
      let Int64 t2 v2 = r2;
      unfold cbor_match_int v (Int64 t1 v1);
      unfold cbor_match_int v (Int64 t2 v2);
      (* permissions do not show up in cbor_match_int *)
      fold cbor_match_int v (Int64 t1 v1);
      fold cbor_match (p1 +. p2) (CBOR_Case_Int v) (Int64 t1 v1);
      rewrite cbor_match (p1 +. p2) (CBOR_Case_Int v) (Int64 t1 v1) as cbor_match (p1 +. p2) c r1;
    }
    CBOR_Case_Simple v -> {
      unfold cbor_match p1 (CBOR_Case_Simple v) r1;
      unfold cbor_match p2 (CBOR_Case_Simple v) r2;
      let Simple v1 = r1;
      let Simple v2 = r2;
      unfold cbor_match_simple v (Simple v1);
      unfold cbor_match_simple v (Simple v2);
      (* permissions do not show up in cbor_match_simple *)
      fold cbor_match_simple v (Simple v1);
      fold cbor_match (p1 +. p2) (CBOR_Case_Simple v) (Simple v1);
      rewrite cbor_match (p1 +. p2) (CBOR_Case_Simple v) (Simple v1) as cbor_match (p1 +. p2) c r1;
    }
    norewrite
    CBOR_Case_Tagged v -> {
      cbor_match_eq_tagged p1 v r1;
      rewrite (cbor_match p1 c r1)
        as (cbor_match_tagged v p1 r1 cbor_match);
      unfold (cbor_match_tagged v p1 r1 cbor_match);
      with q1 c1 . assert (R.pts_to v.cbor_tagged_ptr #q1 c1);
      cbor_match_eq_tagged p2 v r2;
      rewrite (cbor_match p2 c r2)
        as (cbor_match_tagged v p2 r2 cbor_match);
      unfold (cbor_match_tagged v p2 r2 cbor_match);
      with q2 c2 . assert (R.pts_to v.cbor_tagged_ptr #q1 c1 ** R.pts_to v.cbor_tagged_ptr #q2 c2);
      R.gather v.cbor_tagged_ptr;
      rewrite each c2 as c1;
      cbor_raw_gather _ _ (Tagged?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_tagged_ref_perm;
      perm_mul_add_l p1 p2 v.cbor_tagged_payload_perm;
      rewrite each (perm_mul p1 v.cbor_tagged_payload_perm +.
        perm_mul p2 v.cbor_tagged_payload_perm) as (perm_mul (p1 +. p2) v.cbor_tagged_payload_perm);
      fold (cbor_match_tagged v (p1 +. p2) r1 cbor_match);
      cbor_match_eq_tagged (p1 +. p2) v r1;
      rewrite (cbor_match_tagged v (p1 +. p2) r1 cbor_match)
        as (cbor_match (p1 +. p2) c r1);
    }
    CBOR_Case_Array v -> {
      unfold cbor_match p1 (CBOR_Case_Array v) r1;
      unfold cbor_match p2 (CBOR_Case_Array v) r2;
      let Array len1 a1 = r1;
      let Array len2 a2 = r2;
      cbor_raw_gather_array p1 v (Array len1 a1) p2 (Array len2 a2) cbor_raw_gather ();
      fold cbor_match (p1 +. p2) (CBOR_Case_Array v) (Array len1 a1);
      rewrite cbor_match (p1 +. p2) (CBOR_Case_Array v) (Array len1 a1) as cbor_match (p1 +. p2) c r1
    }
    CBOR_Case_Map v -> {
      unfold cbor_match p1 (CBOR_Case_Map v) r1;
      unfold cbor_match p2 (CBOR_Case_Map v) r2;
      let Map len1 a1 = r1;
      let Map len2 a2 = r2;
      cbor_raw_gather_map p1 v (Map len1 a1) p2 (Map len2 a2) cbor_raw_gather ();
      fold cbor_match (p1 +. p2) (CBOR_Case_Map v) (Map len1 a1);
      rewrite cbor_match (p1 +. p2) (CBOR_Case_Map v) (Map len1 a1) as cbor_match (p1 +. p2) c r1
    }
    norewrite
    CBOR_Case_Serialized_Tagged v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_serialized_tagged v p1 r1);
      unfold (cbor_match_serialized_tagged v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_serialized_tagged v p2 r2);
      unfold (cbor_match_serialized_tagged v p2 r2);
      cbor_match_serialized_payload_tagged_gather _ _ (Tagged?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_serialized_perm;
      rewrite each (perm_mul p1 v.cbor_serialized_perm +.
        perm_mul p2 v.cbor_serialized_perm) as (perm_mul (p1 +. p2) v.cbor_serialized_perm);
      fold (cbor_match_serialized_tagged v (p1 +. p2) r1);
      rewrite (cbor_match_serialized_tagged v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Serialized_Array v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_serialized_array v p1 r1);
      unfold (cbor_match_serialized_array v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_serialized_array v p2 r2);
      unfold (cbor_match_serialized_array v p2 r2);
      cbor_match_serialized_payload_array_gather _ _ (Array?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_serialized_perm;
      rewrite each (perm_mul p1 v.cbor_serialized_perm +.
        perm_mul p2 v.cbor_serialized_perm) as (perm_mul (p1 +. p2) v.cbor_serialized_perm);
      fold (cbor_match_serialized_array v (p1 +. p2) r1);
      rewrite (cbor_match_serialized_array v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
    norewrite
    CBOR_Case_Serialized_Map v -> {
      rewrite (cbor_match p1 c r1)
        as (cbor_match_serialized_map v p1 r1);
      unfold (cbor_match_serialized_map v p1 r1);
      rewrite (cbor_match p2 c r2)
        as (cbor_match_serialized_map v p2 r2);
      unfold (cbor_match_serialized_map v p2 r2);
      cbor_match_serialized_payload_map_gather _ _ (Map?.v r1) _ _;
      perm_mul_add_l p1 p2 v.cbor_serialized_perm;
      rewrite each (perm_mul p1 v.cbor_serialized_perm +.
        perm_mul p2 v.cbor_serialized_perm) as (perm_mul (p1 +. p2) v.cbor_serialized_perm);
      fold (cbor_match_serialized_map v (p1 +. p2) r1);
      rewrite (cbor_match_serialized_map v (p1 +. p2) r1)
        as (cbor_match (p1 +. p2) c r1);
    }
  }
}
