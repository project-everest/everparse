module LowParse.PulseParse.Iterator.Sorted
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open LowParse.PulseParse.Iterator

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module LPS = LowParse.Pulse.Base
module SM = Pulse.Lib.SeqMatch

open FStar.Real

// ===== mixed_list_insert_sorted =====

// Sorted predicate for a list with respect to a strict total order
// Comparison function type: compares two elements, preserving vmatch.
// Returns 0sz if v1 < v2, 1sz if v1 == v2, 2sz if v2 < v1.
inline_for_extraction
let cmp_t
  (#t #u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (lt_spec: u -> u -> bool)
=
  (x1: t) -> (x2: t) ->
  (#pm1: perm) -> (#v1: Ghost.erased u) ->
  (#pm2: perm) -> (#v2: Ghost.erased u) ->
  stt SZ.t
    (vmatch pm1 x1 (Ghost.reveal v1) ** vmatch pm2 x2 (Ghost.reveal v2))
    (fun r ->
      vmatch pm1 x1 (Ghost.reveal v1) **
      vmatch pm2 x2 (Ghost.reveal v2) **
      pure (
        (SZ.v r == 0 <==> lt_spec (Ghost.reveal v1) (Ghost.reveal v2) == true) /\
        (SZ.v r == 1 <==> (Ghost.reveal v1 == Ghost.reveal v2)) /\
        (SZ.v r == 2 <==> lt_spec (Ghost.reveal v2) (Ghost.reveal v1) == true) /\
        SZ.v r <= 2
      ))

// Lemma: List.Tot.Properties.sorted is preserved for suffixes
let sorted_suffix (#u: Type) (lt_spec: u -> u -> bool) (l: list u)
  : Lemma (requires Cons? l /\ List.Tot.Properties.sorted lt_spec l)
          (ensures List.Tot.Properties.sorted lt_spec (List.Tot.tl l))
= match l with
  | [_] -> ()
  | _ :: _ -> ()

// Lemma: in a sorted list, lt l[i] l[i+1] for valid i
let rec sorted_adjacent (#u: Type) (lt_spec: u -> u -> bool) (l: list u) (i: nat)
  : Lemma (requires List.Tot.Properties.sorted lt_spec l /\ i + 1 < List.Tot.length l)
          (ensures lt_spec (List.Tot.index l i) (List.Tot.index l (i + 1)) == true)
          (decreases i)
= match l with
  | _ :: tl ->
    if i = 0 then ()
    else sorted_adjacent lt_spec tl (i - 1)

// Lemma: sorted insertion preserves sortedness
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec sorted_insert_lemma (#u: Type) (lt_spec: u -> u -> bool) (l: list u) (y: u) (k: nat)
  : Lemma
    (requires
      List.Tot.Properties.sorted lt_spec l /\
      k <= List.Tot.length l /\
      (forall (i: nat). i < k ==> i < List.Tot.length l /\ lt_spec (List.Tot.index l i) y == true) /\
      (k == List.Tot.length l \/ (k < List.Tot.length l /\ lt_spec y (List.Tot.index l k) == true)) /\
      (forall (a b c: u). lt_spec a b == true /\ lt_spec b c == true ==> lt_spec a c == true))
    (ensures (
      let (l1, l2) = List.Tot.splitAt k l in
      List.Tot.Properties.sorted lt_spec (List.Tot.append l1 (y :: l2)) == true))
    (decreases k)
= if k = 0 then ()
  else
    match l with
    | [] -> ()
    | x :: tl ->
      assert (List.Tot.Properties.sorted lt_spec tl);
      assert (k - 1 <= List.Tot.length tl);
      let aux (i: nat) : Lemma (requires i < k - 1) (ensures i < List.Tot.length tl /\ lt_spec (List.Tot.index tl i) y == true)
        = assert (List.Tot.index tl i == List.Tot.index l (i + 1));
          assert (i + 1 < k)
      in
      Classical.forall_intro (Classical.move_requires aux);
      sorted_insert_lemma lt_spec tl y (k - 1)
#pop-options

// Lemma: list_narrow relates to splitAt
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let list_narrow_splitAt (#a: Type) (l: list a) (k: nat)
  : Lemma (requires k <= List.Tot.length l)
          (ensures list_narrow l 0 k == fst (List.Tot.splitAt k l) /\
                   list_narrow l k (List.Tot.length l - k) == snd (List.Tot.splitAt k l))
= // list_narrow l 0 k = fst (splitAt k (snd (splitAt 0 l))) = fst (splitAt k l)
  assert (snd (List.Tot.splitAt 0 l) == l);
  FStar.List.Pure.Properties.splitAt_length k l;
  // list_narrow l k (len-k) = fst (splitAt (len-k) (snd (splitAt k l)))
  // length (snd (splitAt k l)) == len - k
  FStar.List.Tot.Base.lemma_splitAt_snd_length k l;
  FStar.List.Pure.Properties.splitAt_length (List.Tot.length l - k) (snd (List.Tot.splitAt k l));
  FStar.List.Pure.Properties.splitAt_length_total (snd (List.Tot.splitAt k l))
#pop-options

// Postcondition for mixed_list_insert_sorted
let mixed_list_insert_sorted_post
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (lt_spec: u -> u -> bool)
  (pm: perm) (pm_y: perm)
  (ml: mixed_list t) (l: Ghost.erased (list u))
  (y_elem: t) (y: Ghost.erased u)
  (r1 r2 r3 r4: R.ref (mixed_list t)) (ry: R.ref t)
  (res: bool)
: Tot slprop
= if res then
    exists* (ml_result: mixed_list t) (pm_result: perm) (l_result: list u).
      mixed_list_match vmatch p pm_result ml_result l_result **
      trade (mixed_list_match vmatch p pm_result ml_result l_result)
            (mixed_list_match vmatch p pm ml (Ghost.reveal l) **
             vmatch pm_y y_elem (Ghost.reveal y) **
             (exists* v1 v2 v3 v4 vy.
               R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)) **
      pure (
        (exists (k_pos: nat).
          k_pos <= List.Tot.length (Ghost.reveal l) /\
          l_result == List.Tot.append (list_narrow (Ghost.reveal l) 0 k_pos) (Ghost.reveal y :: list_narrow (Ghost.reveal l) k_pos (List.Tot.length (Ghost.reveal l) - k_pos))) /\
        List.Tot.Properties.sorted lt_spec l_result == true
      )
  else
    mixed_list_match vmatch p pm ml (Ghost.reveal l) **
    vmatch pm_y y_elem (Ghost.reveal y) **
    (exists* v1 v2 v3 v4 vy.
      R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy) **
    pure (List.Tot.memP (Ghost.reveal y) (Ghost.reveal l))

// Helper: perm equality lemma for pm *. (1.0R /. pm) == 1.0R
let perm_mul_div_cancel (a: perm) : Lemma (a *. (1.0R /. a) == 1.0R)
= let open FStar.Real in
  assert (a *. (1.0R /. a) == 1.0R)

// Helper: perm equality lemma for pm *. (b /. pm) == b
let perm_mul_div_cancel' (a b: perm) : Lemma (a *. (b /. a) == b)
= let open FStar.Real in
  assert (a *. (b /. a) == b)

// Helper: hd of list_narrow l k 1 == index l k
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let list_narrow_index_hd (#a: Type) (l: list a) (k: nat)
  : Lemma (requires k < List.Tot.length l)
          (ensures Cons? (list_narrow l k 1) /\ List.Tot.hd (list_narrow l k 1) == List.Tot.index l k)
= FStar.List.Pure.Properties.lemma_splitAt_index_hd k l;
  FStar.List.Tot.Base.lemma_splitAt_snd_length k l;
  let tl = snd (List.Tot.splitAt k l) in
  // tl has length >= 1, hd tl == index l k
  // list_narrow l k 1 == fst (splitAt 1 tl) == [hd tl]
  assert (fst (List.Tot.splitAt 1 tl) == [List.Tot.hd tl])
#pop-options

#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

```pulse
fn mixed_list_insert_sorted_find
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (lt_spec: Ghost.erased (u -> u -> bool))
  (cmp: cmp_t vmatch (Ghost.reveal lt_spec))
  (pm: perm) (pm_y: perm)
  (ml: mixed_list t) (l: Ghost.erased (list u))
  (y_elem: t) (y: Ghost.erased u)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (zcp: zero_copy_parse_strong_prefix (vmatch 1.0R) p)
  (r_k: R.ref SZ.t) (r_continue: R.ref bool) (r_found: R.ref SZ.t)
  (total_sz: SZ.t)
requires
  R.pts_to r_k 0sz **
  R.pts_to r_continue true **
  R.pts_to r_found 0sz **
  mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l) **
  mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l) **
  vmatch pm_y y_elem (Ghost.reveal y) **
  pure (
    SZ.v total_sz == List.Tot.length (Ghost.reveal l) /\
    SZ.fits (List.Tot.length (Ghost.reveal l) + 1) /\
    (forall (a b c: u). Ghost.reveal lt_spec a b == true /\ Ghost.reveal lt_spec b c == true ==> Ghost.reveal lt_spec a c == true) /\
    (forall (a: u). Ghost.reveal lt_spec a a == false)
  )
ensures exists* (k_val: SZ.t) (found_val: SZ.t).
  R.pts_to r_k k_val **
  R.pts_to r_continue false **
  R.pts_to r_found found_val **
  mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l) **
  mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l) **
  vmatch pm_y y_elem (Ghost.reveal y) **
  pure (
    SZ.v k_val <= SZ.v total_sz /\
    SZ.v total_sz == List.Tot.length (Ghost.reveal l) /\
    (SZ.v found_val == 0 \/ SZ.v found_val == 1 \/ SZ.v found_val == 2) /\
    (SZ.v found_val == 0 ==> SZ.v k_val < SZ.v total_sz /\
      Ghost.reveal lt_spec (Ghost.reveal y) (List.Tot.index (Ghost.reveal l) (SZ.v k_val)) == true) /\
    (SZ.v found_val == 1 ==> SZ.v k_val < SZ.v total_sz /\
      Ghost.reveal y == List.Tot.index (Ghost.reveal l) (SZ.v k_val)) /\
    (SZ.v found_val == 2 ==> SZ.v k_val == SZ.v total_sz) /\
    (forall (i: nat). i < SZ.v k_val ==> i < List.Tot.length (Ghost.reveal l) /\
      Ghost.reveal lt_spec (List.Tot.index (Ghost.reveal l) i) (Ghost.reveal y) == true)
  )
{
  mixed_list_match_n_length vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l);
  while (
    let c = !r_continue;
    c
  ) invariant exists* b (k_val: SZ.t) (found_val: SZ.t).
    R.pts_to r_k k_val **
    R.pts_to r_continue b **
    R.pts_to r_found found_val **
    mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l) **
    mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l) **
    vmatch pm_y y_elem (Ghost.reveal y) **
    pure (
      SZ.v k_val <= SZ.v total_sz /\
      SZ.v total_sz == List.Tot.length (Ghost.reveal l) /\
      (b == true ==> SZ.v found_val == 0) /\
      (SZ.v found_val == 0 \/ SZ.v found_val == 1 \/ SZ.v found_val == 2) /\
      (b == false ==> (
        (SZ.v found_val == 0 ==> SZ.v k_val < SZ.v total_sz /\
          Ghost.reveal lt_spec (Ghost.reveal y) (List.Tot.index (Ghost.reveal l) (SZ.v k_val)) == true) /\
        (SZ.v found_val == 1 ==> SZ.v k_val < SZ.v total_sz /\
          Ghost.reveal y == List.Tot.index (Ghost.reveal l) (SZ.v k_val)) /\
        (SZ.v found_val == 2 ==> SZ.v k_val == SZ.v total_sz)
      )) /\
      (forall (i: nat). i < SZ.v k_val ==> i < List.Tot.length (Ghost.reveal l) /\
        Ghost.reveal lt_spec (List.Tot.index (Ghost.reveal l) i) (Ghost.reveal y) == true)
    )
  {
    let k_val = !r_k;
    if (SZ.eq k_val total_sz) {
      r_found := 2sz;
      r_continue := false;
    } else {
      mixed_list_match_n_length vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l);
      let ml_k = mixed_list_narrow_n vmatch p j 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)
        k_val 1sz vmatch_share vmatch_gather;
      let l_k : Ghost.erased (list u) = list_narrow (Ghost.reveal l) (SZ.v k_val - 0) 1;
      rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_k (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v 1sz)))
        as (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      rewrite (trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_k (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v 1sz)))
                     (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)))
        as (trade (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k))
                  (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)));
      unfold (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_k)) (pm /. 4.0R) ml_k (Ghost.reveal l_k))
        as (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      let res_extract = mixed_list_extract_first_base_loop vmatch p j 0 1 0sz 1sz (pm /. 4.0R) ml_k (Ghost.reveal l_k);
      let bi_k = fst res_extract;
      let len_bi = snd res_extract;
      rewrite (
        (let (bi'', len'') = res_extract in
         base_mixed_list_match vmatch p (pm /. 4.0R) bi'' (list_narrow (Ghost.reveal l_k) 0 (SZ.v len'')) **
         trade (base_mixed_list_match vmatch p (pm /. 4.0R) bi'' (list_narrow (Ghost.reveal l_k) 0 (SZ.v len'')))
              (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k)) **
         pure (SZ.v len'' == SZ.v (base_mixed_list_length bi'') /\ SZ.v len'' > 0 /\ SZ.v len'' <= 1)))
        as (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)) **
            trade (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
                 (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k)) **
            pure (SZ.v len_bi == SZ.v (base_mixed_list_length bi_k) /\ SZ.v len_bi > 0 /\ SZ.v len_bi <= 1));
      assert (pure (SZ.v len_bi == 1));
      rewrite (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
        as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi_k)) (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)));
      rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi_k)) (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
        as (base_mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) bi_k (Ghost.reveal l_k));
      let x_elem = base_mixed_list_next_n vmatch p 0 1 0sz 1sz (pm /. 4.0R) bi_k (Ghost.reveal l_k) vmatch_share vmatch_gather j zcp;
      unfold (mixed_list_next_n_post vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k) x_elem);
      with pm_v hd_val tl_val . assert (
        vmatch pm_v x_elem hd_val **
        mixed_list_match_n vmatch p 1 0 ((pm /. 4.0R) /. 2.0R) (Base bi_k) tl_val **
        trade (vmatch pm_v x_elem hd_val ** mixed_list_match_n vmatch p 1 0 ((pm /. 4.0R) /. 2.0R) (Base bi_k) tl_val)
              (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k)) **
        pure (1 > 0 /\ Ghost.reveal l_k == hd_val :: tl_val)
      );
      let cmp_result = cmp x_elem y_elem #pm_v #hd_val #pm_y #y;
      Trade.elim
        (vmatch pm_v x_elem hd_val ** mixed_list_match_n vmatch p 1 0 ((pm /. 4.0R) /. 2.0R) (Base bi_k) tl_val)
        (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k));
      rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k))
        as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length (Base bi_k))) (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k));
      unfold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length (Base bi_k))) (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k));
      rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi_k)) (pm /. 4.0R) bi_k (Ghost.reveal l_k))
        as (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)));
      Trade.elim
        (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
        (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k))
        as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_k)) (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      fold (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      Trade.elim
        (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k))
        (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l));
      list_narrow_index_hd (Ghost.reveal l) (SZ.v k_val);
      assert (pure (Ghost.reveal hd_val == List.Tot.index (Ghost.reveal l) (SZ.v k_val)));
      if (SZ.eq cmp_result 0sz) {
        r_k := SZ.add k_val 1sz;
      } else if (SZ.eq cmp_result 1sz) {
        r_found := 1sz;
        r_continue := false;
      } else {
        r_found := 0sz;
        r_continue := false;
      }
    }
  }
}
```

#pop-options

#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

```pulse
ghost fn mixed_list_insert_sorted_trade_body
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm) (pm_y: perm)
  (ml: mixed_list t) (l: Ghost.erased (list u))
  (y_elem: t) (y: Ghost.erased u)
  (r1: R.ref (mixed_list t)) (r2: R.ref (mixed_list t))
  (r3: R.ref (mixed_list t)) (r4: R.ref (mixed_list t))
  (ry: R.ref t)
  (vmatch_gather: gather_t vmatch)
  (k_val: SZ.t) (rest_sz: SZ.t) (total_sz: SZ.t)
  (ml_before: Ghost.erased (mixed_list t))
  (ml_after: Ghost.erased (mixed_list t))
  (l_before: Ghost.erased (list u))
  (l_after: Ghost.erased (list u))
  (l_result: Ghost.erased (list u))
  (sp_val: Ghost.erased perm)
  (sv_val: Ghost.erased perm)
  (bp_val: Ghost.erased perm)
  (outer_depth: Ghost.erased nat)
  (inner_depth: Ghost.erased nat)
  (sq_fits: squash (SZ.fits (SZ.v k_val + 1 + SZ.v rest_sz) /\ SZ.fits (1 + SZ.v rest_sz)))
  (sq_total: squash (SZ.v total_sz == SZ.v k_val + SZ.v rest_sz))
  (sq_len: squash (SZ.v total_sz == List.Tot.length (Ghost.reveal l)))
requires
  mixed_list_match vmatch p (pm /. 4.0R)
    (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2)
    (Ghost.reveal l_result) **
  trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)))
        (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)) **
  trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)))
        (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)) **
  R.pts_to r1 #(1.0R /. 2.0R) ml_before **
  R.pts_to r2 #(1.0R /. 2.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) **
  R.pts_to r3 #(1.0R /. 2.0R) (Base #t (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) **
  R.pts_to r4 #(1.0R /. 2.0R) ml_after **
  R.pts_to ry #(1.0R /. 2.0R) y_elem **
  vmatch (pm_y /. 2.0R) y_elem (Ghost.reveal y) **
  pure (
    (pm /. 4.0R) *. Ghost.reveal bp_val == 1.0R /. 2.0R /\
    (pm /. 4.0R) *. Ghost.reveal sp_val == 1.0R /. 2.0R /\
    (pm /. 4.0R) *. Ghost.reveal sv_val == pm_y /. 2.0R /\
    (pm /. 2.0R) /. 2.0R == pm /. 4.0R /\
    Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
    Ghost.reveal l_before == list_narrow (Ghost.reveal l) 0 (SZ.v k_val) /\
    Ghost.reveal l_after == list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz) /\
    List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
    List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
    SZ.v (mixed_list_length (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2)) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
    SZ.v (mixed_list_length (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4)) == 1 + SZ.v rest_sz /\
    SZ.v (mixed_list_length (Ghost.reveal ml_before)) == SZ.v k_val /\
    SZ.v (mixed_list_length (Ghost.reveal ml_after)) == SZ.v rest_sz /\
    SZ.v (mixed_list_length ml) == SZ.v total_sz
  )
ensures
  mixed_list_match vmatch p pm ml (Ghost.reveal l) **
  vmatch pm_y y_elem (Ghost.reveal y) **
  (exists* v1 v2 v3 v4 vy.
    R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)
{
  let result_ml : mixed_list t = Append (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2;
  let inner_ml : mixed_list t = Append (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4;
  let singleton_ml : mixed_list t = Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
  rewrite (mixed_list_match vmatch p (pm /. 4.0R)
    (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2)
    (Ghost.reveal l_result))
    as (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result));
  rewrite (R.pts_to r2 #(1.0R /. 2.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4))
    as (R.pts_to r2 #(1.0R /. 2.0R) inner_ml);
  rewrite (R.pts_to r3 #(1.0R /. 2.0R) (Base #t (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)))
    as (R.pts_to r3 #(1.0R /. 2.0R) singleton_ml);
  // Trade body: unfold result, gather refs, recover originals
  // Step 1: Unfold outer Append
  unfold (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result));
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) result_ml (Ghost.reveal l_result))
    as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) (Append (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2) (Ghost.reveal l_result));
  unfold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) (Append (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2) (Ghost.reveal l_result));
  with ib_u ia_u l1_u l2_u . assert (
    pts_to r1 #((pm /. 4.0R) *. Ghost.reveal bp_val) ib_u **
    mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ib_u l1_u **
    pts_to r2 #((pm /. 4.0R) *. Ghost.reveal bp_val) ia_u **
    mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v k_val)) (append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ia_u l2_u
  );
  // Step 2: Gather r1 — proves ib_u == ml_before
  rewrite (pts_to r1 #((pm /. 4.0R) *. Ghost.reveal bp_val) ib_u)
    as (R.pts_to r1 #(1.0R /. 2.0R) ib_u);
  R.gather r1;
  drop_ (pure (reveal ml_before == reveal ib_u));
  rewrite (R.pts_to r1 #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_before)
    as (R.pts_to r1 ml_before);
  // Step 3: Gather r2 — proves ia_u == inner_ml
  rewrite (pts_to r2 #((pm /. 4.0R) *. Ghost.reveal bp_val) ia_u)
    as (R.pts_to r2 #(1.0R /. 2.0R) ia_u);
  R.gather r2;
  drop_ (pure (reveal inner_ml == reveal ia_u));
  rewrite (R.pts_to r2 #(1.0R /. 2.0R +. 1.0R /. 2.0R) inner_ml)
    as (R.pts_to r2 inner_ml);
  // Step 4: slprop_rw on before match: ib_u → ml_before
  mixed_list_match_n_length vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ib_u l1_u;
  list_narrow_length (Ghost.reveal l) 0 (SZ.v k_val);
  List.Tot.Properties.append_injective l1_u (Ghost.reveal l_before) l2_u (Ghost.reveal y :: Ghost.reveal l_after);
  with ib_x . assert (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ib_x l1_u);
  slprop_rw
    (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ib_x l1_u)
    (mixed_list_match_n vmatch p 0 (SZ.v k_val) (pm /. 4.0R) ml_before (Ghost.reveal l_before))
    (Pulse.Lib.Core.slprop_equiv_ext'
      (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ib_x l1_u)
      (mixed_list_match_n vmatch p 0 (SZ.v k_val) (pm /. 4.0R) ml_before (Ghost.reveal l_before))
      ());
  // Step 5: slprop_rw on after match: ia_u → inner_ml
  with ia_x . assert (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v k_val)) (append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ia_x l2_u);
  slprop_rw
    (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v k_val)) (append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ia_x l2_u)
    (mixed_list_match_n vmatch p 0 (SZ.v (SZ.add 1sz rest_sz)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after))
    (Pulse.Lib.Core.slprop_equiv_ext'
      (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v k_val)) (append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ia_x l2_u)
      (mixed_list_match_n vmatch p 0 (SZ.v (SZ.add 1sz rest_sz)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after))
      ());
  // Step 6: Unfold inner Append
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (SZ.add 1sz rest_sz)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after))
    as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) (Append (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) (Ghost.reveal y :: Ghost.reveal l_after));
  unfold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) (Append (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) (Ghost.reveal y :: Ghost.reveal l_after));
  with sing_u rest_u ls_u lr_u . assert (
    pts_to r3 #((pm /. 4.0R) *. Ghost.reveal bp_val) sing_u **
    mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) sing_u ls_u **
    pts_to r4 #((pm /. 4.0R) *. Ghost.reveal bp_val) rest_u **
    mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v 1sz)) (append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) rest_u lr_u
  );
  // Step 7: Gather r3 — proves sing_u == singleton_ml
  rewrite (pts_to r3 #((pm /. 4.0R) *. Ghost.reveal bp_val) sing_u)
    as (R.pts_to r3 #(1.0R /. 2.0R) sing_u);
  R.gather r3;
  drop_ (pure (reveal singleton_ml == reveal sing_u));
  rewrite (R.pts_to r3 #(1.0R /. 2.0R +. 1.0R /. 2.0R) singleton_ml)
    as (R.pts_to r3 singleton_ml);
  // Step 8: Gather r4 — proves rest_u == ml_after
  rewrite (pts_to r4 #((pm /. 4.0R) *. Ghost.reveal bp_val) rest_u)
    as (R.pts_to r4 #(1.0R /. 2.0R) rest_u);
  R.gather r4;
  drop_ (pure (reveal ml_after == reveal rest_u));
  rewrite (R.pts_to r4 #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_after)
    as (R.pts_to r4 ml_after);
  // Step 9: slprop_rw on singleton match: sing_u → singleton_ml
  mixed_list_match_n_length vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) sing_u ls_u;
  List.Tot.Properties.append_injective ls_u [Ghost.reveal y] lr_u (Ghost.reveal l_after);
  with sing_x . assert (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) sing_x ls_u);
  slprop_rw
    (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) sing_x ls_u)
    (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) singleton_ml [Ghost.reveal y])
    (Pulse.Lib.Core.slprop_equiv_ext'
      (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) sing_x ls_u)
      (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) singleton_ml [Ghost.reveal y])
      ());
  // Step 10: slprop_rw on rest match: rest_u → ml_after
  with rest_x . assert (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v 1sz)) (append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) rest_x lr_u);
  slprop_rw
    (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v 1sz)) (append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) rest_x lr_u)
    (mixed_list_match_n vmatch p 0 (SZ.v rest_sz) (pm /. 4.0R) ml_after (Ghost.reveal l_after))
    (Pulse.Lib.Core.slprop_equiv_ext'
      (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v 1sz)) (append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) rest_x lr_u)
      (mixed_list_match_n vmatch p 0 (SZ.v rest_sz) (pm /. 4.0R) ml_after (Ghost.reveal l_after))
      ());
  // Step 11: Unfold Singleton to get ry and vmatch
  rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) singleton_ml [Ghost.reveal y])
    as (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
  unfold (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
  unfold (base_mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
  with x_sing y_sing . assert (
    pts_to ry #((pm /. 4.0R) *. Ghost.reveal sp_val) x_sing **
    vmatch ((pm /. 4.0R) *. Ghost.reveal sv_val) x_sing y_sing
  );
  // Step 12: Gather ry — proves x_sing == y_elem
  rewrite (pts_to ry #((pm /. 4.0R) *. Ghost.reveal sp_val) x_sing)
    as (R.pts_to ry #(1.0R /. 2.0R) x_sing);
  R.gather ry;
  drop_ (pure (reveal y_elem == reveal x_sing));
  rewrite (R.pts_to ry #(1.0R /. 2.0R +. 1.0R /. 2.0R) y_elem)
    as (R.pts_to ry y_elem);
  // Step 13: Gather vmatch — proves y_sing == y
  rewrite (vmatch ((pm /. 4.0R) *. Ghost.reveal sv_val) x_sing y_sing)
    as (vmatch (pm_y /. 2.0R) y_elem (Ghost.reveal y_sing));
  vmatch_gather y_elem #(pm_y /. 2.0R) #(Ghost.reveal y) #(pm_y /. 2.0R) #(Ghost.reveal y_sing);
  drop_ (pure (Ghost.reveal y == Ghost.reveal y_sing));
  rewrite (vmatch (pm_y /. 2.0R +. pm_y /. 2.0R) y_elem (Ghost.reveal y))
    as (vmatch pm_y y_elem (Ghost.reveal y));
  // Step 14: Recover copy1 via before narrow trade
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v k_val) (pm /. 4.0R) ml_before (Ghost.reveal l_before))
    as (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)));
  Trade.elim
    (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)))
    (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l));
  // Step 15: Recover copy2 via after narrow trade
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v rest_sz) (pm /. 4.0R) ml_after (Ghost.reveal l_after))
    as (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)));
  Trade.elim
    (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)))
    (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l));
  // Step 16: Gather two copies of original
  mixed_list_match_n_gather vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) (pm /. 2.0R) ml (Ghost.reveal l) (Ghost.reveal l) vmatch_gather;
  drop_ (pure (Ghost.reveal l == Ghost.reveal l));
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v total_sz) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l))
    as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l));
  fold (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l));
  rewrite (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l))
    as (mixed_list_match vmatch p pm ml (Ghost.reveal l));
  // Step 17: Pack refs existential
  fold (exists* v1 v2 v3 v4 vy.
    R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy);
}
```

#pop-options

#push-options "--z3rlimit 16000 --fuel 2 --ifuel 1 --ext no:context_pruning --z3refresh --split_queries always"

```pulse
fn mixed_list_insert_sorted
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (lt_spec: Ghost.erased (u -> u -> bool))
  (cmp: cmp_t vmatch (Ghost.reveal lt_spec))
  (pm: perm) (pm_y: perm)
  (ml: mixed_list t) (l: Ghost.erased (list u))
  (y_elem: t) (y: Ghost.erased u)
  (r1: R.ref (mixed_list t)) (r2: R.ref (mixed_list t))
  (r3: R.ref (mixed_list t)) (r4: R.ref (mixed_list t))
  (ry: R.ref t)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (zcp: zero_copy_parse_strong_prefix (vmatch 1.0R) p)
requires
  mixed_list_match vmatch p pm ml (Ghost.reveal l) **
  vmatch pm_y y_elem (Ghost.reveal y) **
  (exists* v1 v2 v3 v4 vy.
    R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy) **
  pure (
    List.Tot.Properties.sorted (Ghost.reveal lt_spec) (Ghost.reveal l) == true /\
    SZ.fits (List.Tot.length (Ghost.reveal l) + 1) /\
    (forall (a b c: u). Ghost.reveal lt_spec a b == true /\ Ghost.reveal lt_spec b c == true ==> Ghost.reveal lt_spec a c == true) /\
    (forall (a: u). Ghost.reveal lt_spec a a == false)
  )
returns res: bool
ensures
  mixed_list_insert_sorted_post vmatch p (Ghost.reveal lt_spec) pm pm_y ml l y_elem y r1 r2 r3 r4 ry res
{
  // Get total length
  let total_sz = mixed_list_length ml;
  // Share the mixed_list → two copies at pm/2
  unfold (mixed_list_match vmatch p pm ml (Ghost.reveal l));
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml (Ghost.reveal l))
    as (mixed_list_match_n vmatch p 0 (SZ.v total_sz) pm ml (Ghost.reveal l));
  mixed_list_match_n_share vmatch p 0 (SZ.v total_sz) pm ml (Ghost.reveal l) vmatch_share;
  // copy1 and copy2 both at pm/2
  // Search loop: find insertion position k (delegated to helper)
  let mut r_k = 0sz;
  let mut r_continue = true;
  let mut r_found = 0sz; // 0 = found (insert before k), 1 = duplicate at k, 2 = insert at end
  mixed_list_match_n_length vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l);
  mixed_list_insert_sorted_find vmatch p j lt_spec cmp pm pm_y ml l y_elem y vmatch_share vmatch_gather zcp r_k r_continue r_found total_sz;
  // After loop: check result
  let k_val = !r_k;
  let found_val = !r_found;
  if (SZ.eq found_val 1sz) {
    // Duplicate: gather copies back and return false
    mixed_list_match_n_gather vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) (pm /. 2.0R) ml (Ghost.reveal l) (Ghost.reveal l) vmatch_gather;
    drop_ (pure (Ghost.reveal l == Ghost.reveal l));
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v total_sz) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l))
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l));
    fold (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l));
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l))
      as (mixed_list_match vmatch p pm ml (Ghost.reveal l));
    // Pack refs back
    List.Tot.Properties.lemma_index_memP (Ghost.reveal l) (SZ.v k_val);
    fold (exists* v1 v2 v3 v4 vy.
      R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy);
    rewrite (
      mixed_list_match vmatch p pm ml (Ghost.reveal l) **
      vmatch pm_y y_elem (Ghost.reveal y) **
      (exists* v1 v2 v3 v4 vy.
        R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy) **
      pure (List.Tot.memP (Ghost.reveal y) (Ghost.reveal l)))
    as (mixed_list_insert_sorted_post vmatch p (Ghost.reveal lt_spec) pm pm_y ml l y_elem y r1 r2 r3 r4 ry false);
    false
  } else {
    // Success: build result
    // Narrow copy1 to [0, k): before part
    let k_nat : Ghost.erased nat = SZ.v k_val;
    let rest_sz = SZ.sub total_sz k_val;
    let ml_before = mixed_list_narrow_n vmatch p j 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)
      0sz k_val vmatch_share vmatch_gather;
    // ml_before matches l[0..k) at pm/4
    // Narrow copy2 to [k, total-k): after part
    let ml_after = mixed_list_narrow_n vmatch p j 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)
      k_val rest_sz vmatch_share vmatch_gather;
    // ml_after matches l[k..total) at pm/4
    // Write refs and share for half-perm pattern
    R.write ry y_elem;
    R.share ry;
    // Share vmatch to get two halves at pm_y/2
    vmatch_share y_elem;
    // Build Singleton: Base (Singleton sp sv ry) matching [y]
    let sp_val : Ghost.erased perm = 0.5R /. (pm /. 4.0R);
    let sv_val : Ghost.erased perm = (pm_y /. 2.0R) /. (pm /. 4.0R);
    let singleton_ml : mixed_list t = Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
    // Write inner append refs and share
    R.write r3 singleton_ml;
    R.share r3;
    R.write r4 ml_after;
    R.share r4;
    // Build inner Append
    let bp_val : Ghost.erased perm = 0.5R /. (pm /. 4.0R);
    let inner_depth : Ghost.erased nat = mixed_list_depth ml_after + 1;
    let inner_ml : mixed_list t = Append (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4;
    // Write outer append refs and share
    R.write r1 ml_before;
    R.share r1;
    R.write r2 inner_ml;
    R.share r2;
    // Build outer Append
    let outer_depth : Ghost.erased nat = (if mixed_list_depth ml_before > Ghost.reveal inner_depth then mixed_list_depth ml_before else Ghost.reveal inner_depth) + 1;
    let result_ml : mixed_list t = Append (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2;
    // The result matches l[0..k) @ [y] @ l[k..total)
    let l_before : Ghost.erased (list u) = list_narrow (Ghost.reveal l) 0 (SZ.v k_val);
    let l_after : Ghost.erased (list u) = list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz);
    let l_result : Ghost.erased (list u) = List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after);
    // Establish List.Tot.Properties.sorted on result
    assert (pure (
      SZ.v k_val <= List.Tot.length (Ghost.reveal l) /\
      (SZ.v k_val == List.Tot.length (Ghost.reveal l) \/
       (SZ.v k_val < List.Tot.length (Ghost.reveal l) /\
        Ghost.reveal lt_spec (Ghost.reveal y) (List.Tot.index (Ghost.reveal l) (SZ.v k_val)) == true))
    ));
    sorted_insert_lemma (Ghost.reveal lt_spec) (Ghost.reveal l) (Ghost.reveal y) (SZ.v k_val);
    list_narrow_splitAt (Ghost.reveal l) (SZ.v k_val);
    // Fold Singleton match using half-perm refs and vmatch
    perm_mul_div_cancel' (pm /. 4.0R) 0.5R;
    perm_mul_div_cancel' (pm /. 4.0R) (pm_y /. 2.0R);
    rewrite (R.pts_to ry #(1.0R /. 2.0R) y_elem)
      as (pts_to ry #((pm /. 4.0R) *. Ghost.reveal sp_val) y_elem);
    rewrite (vmatch (pm_y /. 2.0R) y_elem (Ghost.reveal y))
      as (vmatch ((pm /. 4.0R) *. Ghost.reveal sv_val) y_elem (Ghost.reveal y));
    fold (base_mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
    fold (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
    rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y])
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length singleton_ml)) (pm /. 4.0R) singleton_ml [Ghost.reveal y]);
    fold (mixed_list_match vmatch p (pm /. 4.0R) singleton_ml [Ghost.reveal y]);
    // Fold inner Append match
    rewrite (R.pts_to r3 #(1.0R /. 2.0R) singleton_ml)
      as (pts_to r3 #((pm /. 4.0R) *. Ghost.reveal bp_val) singleton_ml);
    rewrite (R.pts_to r4 #(1.0R /. 2.0R) ml_after)
      as (pts_to r4 #((pm /. 4.0R) *. Ghost.reveal bp_val) ml_after);
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)))
      as (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v 1sz)) (append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) ml_after (Ghost.reveal l_after));
    rewrite (mixed_list_match vmatch p (pm /. 4.0R) singleton_ml [Ghost.reveal y])
      as (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v 1sz)) (append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz)) (pm /. 4.0R) singleton_ml [Ghost.reveal y]);
    list_narrow_length (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz);
    intro_pure (
      0 + SZ.v (mixed_list_length inner_ml) <= SZ.v 1sz + SZ.v rest_sz /\
      SZ.v 0sz + SZ.v 1sz <= SZ.v (mixed_list_length singleton_ml) /\
      SZ.v 0sz + SZ.v rest_sz <= SZ.v (mixed_list_length ml_after) /\
      List.Tot.length [Ghost.reveal y] == append_n_before 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz) /\
      List.Tot.length (Ghost.reveal l_after) == append_n_after 0 (SZ.v (mixed_list_length inner_ml)) (SZ.v 1sz) /\
      (Ghost.reveal y :: Ghost.reveal l_after) == List.Tot.append [Ghost.reveal y] (Ghost.reveal l_after) /\
      mixed_list_depth singleton_ml < Ghost.reveal inner_depth /\
      mixed_list_depth ml_after < Ghost.reveal inner_depth
    ) ();
    fold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) (Ghost.reveal y :: Ghost.reveal l_after));
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4) (Ghost.reveal y :: Ghost.reveal l_after))
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length inner_ml)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after));
    fold (mixed_list_match vmatch p (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after));
    // Fold outer Append match
    rewrite (R.pts_to r1 #(1.0R /. 2.0R) ml_before)
      as (pts_to r1 #((pm /. 4.0R) *. Ghost.reveal bp_val) ml_before);
    rewrite (R.pts_to r2 #(1.0R /. 2.0R) inner_ml)
      as (pts_to r2 #((pm /. 4.0R) *. Ghost.reveal bp_val) inner_ml);
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)))
      as (mixed_list_match_n vmatch p (append_off_before 0 0 (SZ.v k_val)) (append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) ml_before (Ghost.reveal l_before));
    rewrite (mixed_list_match vmatch p (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after))
      as (mixed_list_match_n vmatch p (append_off_after 0 0 (SZ.v k_val)) (append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val)) (pm /. 4.0R) inner_ml (Ghost.reveal y :: Ghost.reveal l_after));
    list_narrow_length (Ghost.reveal l) 0 (SZ.v k_val);
    intro_pure (
      0 + SZ.v (mixed_list_length result_ml) <= SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
      SZ.v 0sz + SZ.v k_val <= SZ.v (mixed_list_length ml_before) /\
      SZ.v 0sz + SZ.v (SZ.add 1sz rest_sz) <= SZ.v (mixed_list_length inner_ml) /\
      List.Tot.length (Ghost.reveal l_before) == append_n_before 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val) /\
      List.Tot.length (Ghost.reveal y :: Ghost.reveal l_after) == append_n_after 0 (SZ.v (mixed_list_length result_ml)) (SZ.v k_val) /\
      Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
      mixed_list_depth ml_before < Ghost.reveal outer_depth /\
      mixed_list_depth inner_ml < Ghost.reveal outer_depth
    ) ();
    fold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2) (Ghost.reveal l_result));
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2) (Ghost.reveal l_result))
      as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length result_ml)) (pm /. 4.0R) result_ml (Ghost.reveal l_result));
    fold (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result));
    // Establish pure facts for trade frame (must be before trade intro)
    list_narrow_length (Ghost.reveal l) 0 (SZ.v k_val);
    list_narrow_length (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz);
    perm_mul_div_cancel' (pm /. 4.0R) 0.5R;
    perm_mul_div_cancel' (pm /. 4.0R) (pm_y /. 2.0R);
    intro_pure (
      (pm /. 4.0R) *. Ghost.reveal bp_val == 1.0R /. 2.0R /\
      (pm /. 4.0R) *. Ghost.reveal sp_val == 1.0R /. 2.0R /\
      (pm /. 4.0R) *. Ghost.reveal sv_val == pm_y /. 2.0R /\
      (pm /. 2.0R) /. 2.0R == pm /. 4.0R /\
      Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
      Ghost.reveal l_before == list_narrow (Ghost.reveal l) 0 (SZ.v k_val) /\
      Ghost.reveal l_after == list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz) /\
      List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
      List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
      SZ.v (mixed_list_length result_ml) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
      SZ.v (mixed_list_length inner_ml) == 1 + SZ.v rest_sz /\
      SZ.v (mixed_list_length ml_before) == SZ.v k_val /\
      SZ.v (mixed_list_length ml_after) == SZ.v rest_sz /\
      SZ.v (mixed_list_length ml) == SZ.v total_sz
    ) ();
    // Build the trade: result_match → original + vmatch + refs
    // Frame: halves of all refs + vmatch half + narrow trades + pure facts
    intro (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result) @==>
           (mixed_list_match vmatch p pm ml (Ghost.reveal l) **
            vmatch pm_y y_elem (Ghost.reveal y) **
            (exists* v1 v2 v3 v4 vy.
              R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy)))
      #(trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_before (list_narrow (Ghost.reveal l) (0 - 0) (SZ.v k_val)))
              (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)) **
        trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_after (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v rest_sz)))
              (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)) **
        R.pts_to r1 #(1.0R /. 2.0R) ml_before **
        R.pts_to r2 #(1.0R /. 2.0R) inner_ml **
        R.pts_to r3 #(1.0R /. 2.0R) singleton_ml **
        R.pts_to r4 #(1.0R /. 2.0R) ml_after **
        R.pts_to ry #(1.0R /. 2.0R) y_elem **
        vmatch (pm_y /. 2.0R) y_elem (Ghost.reveal y) **
        pure (
          (pm /. 4.0R) *. Ghost.reveal bp_val == 1.0R /. 2.0R /\
          (pm /. 4.0R) *. Ghost.reveal sp_val == 1.0R /. 2.0R /\
          (pm /. 4.0R) *. Ghost.reveal sv_val == pm_y /. 2.0R /\
          (pm /. 2.0R) /. 2.0R == pm /. 4.0R /\
          Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
          Ghost.reveal l_before == list_narrow (Ghost.reveal l) 0 (SZ.v k_val) /\
          Ghost.reveal l_after == list_narrow (Ghost.reveal l) (SZ.v k_val) (SZ.v rest_sz) /\
          List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
          List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
          SZ.v (mixed_list_length result_ml) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
          SZ.v (mixed_list_length inner_ml) == 1 + SZ.v rest_sz /\
          SZ.v (mixed_list_length ml_before) == SZ.v k_val /\
          SZ.v (mixed_list_length ml_after) == SZ.v rest_sz /\
          SZ.v (mixed_list_length ml) == SZ.v total_sz
        ))
      fn _ {
        // Trade body extracted to mixed_list_insert_sorted_trade_body
        rewrite (mixed_list_match vmatch p (pm /. 4.0R) result_ml (Ghost.reveal l_result))
          as (mixed_list_match vmatch p (pm /. 4.0R)
                (Append #t (Ghost.reveal outer_depth) k_val (SZ.add 1sz rest_sz) 0sz (Ghost.reveal bp_val) r1 0sz (Ghost.reveal bp_val) r2)
                (Ghost.reveal l_result));
        rewrite (R.pts_to r2 #(1.0R /. 2.0R) inner_ml)
          as (R.pts_to r2 #(1.0R /. 2.0R) (Append #t (Ghost.reveal inner_depth) 1sz rest_sz 0sz (Ghost.reveal bp_val) r3 0sz (Ghost.reveal bp_val) r4));
        rewrite (R.pts_to r3 #(1.0R /. 2.0R) singleton_ml)
          as (R.pts_to r3 #(1.0R /. 2.0R) (Base #t (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)));
        mixed_list_insert_sorted_trade_body vmatch p pm pm_y ml l y_elem y r1 r2 r3 r4 ry vmatch_gather
          k_val rest_sz total_sz ml_before ml_after l_before l_after l_result sp_val sv_val bp_val outer_depth inner_depth () () ();
      };
    // Establish postcondition pure
    intro_pure (
      (exists (k_pos: nat).
        k_pos <= List.Tot.length (Ghost.reveal l) /\
        Ghost.reveal l_result == List.Tot.append (list_narrow (Ghost.reveal l) 0 k_pos) (Ghost.reveal y :: list_narrow (Ghost.reveal l) k_pos (List.Tot.length (Ghost.reveal l) - k_pos))) /\
      List.Tot.Properties.sorted (Ghost.reveal lt_spec) (Ghost.reveal l_result) == true
    ) ();
    // Fold postcondition explicitly (Pulse can't auto-unfold the let definition)
    fold (mixed_list_insert_sorted_post vmatch p (Ghost.reveal lt_spec) pm pm_y ml l y_elem y r1 r2 r3 r4 ry true);
    true
  }
}
```

#pop-options
