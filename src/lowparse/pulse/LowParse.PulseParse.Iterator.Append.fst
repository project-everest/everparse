module LowParse.PulseParse.Iterator.Append
#lang-pulse

(* Structural construction of mixed_list values: empty, singleton, and the
   O(1) append of two mixed_lists. These are the building blocks used by the
   CBOR array builder API (empty array, singleton array, append two arrays).

   Unlike LowParse.PulseParse.Iterator.Sorted.mixed_list_insert_sorted, these
   operations do not search, sort, or split: append simply nests the two input
   mixed_lists under a fresh Append node. As a consequence both inputs must be
   held at the SAME ambient permission [pm] (the Append match predicate uses a
   single ambient for both children), and the result is produced at that same
   ambient [pm]. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open LowParse.PulseParse.Iterator.Type
open LowParse.PulseParse.Iterator

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

open FStar.Real

let perm_mul_div_cancel' (a b: perm) : Lemma (a *. (b /. a) == b)
= let open FStar.Real in
  assert (a *. (b /. a) == b)

(* ================================================================ *)
(* Empty mixed_list                                                  *)
(* ================================================================ *)

ghost
fn mixed_list_empty
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm)
requires emp
ensures mixed_list_match vmatch p pm (Base Empty) []
{
  fold (base_mixed_list_match_n vmatch p 0 0 pm (Empty #t) []);
  fold (mixed_list_match_n vmatch p 0 0 pm (Base (Empty #t)) []);
  rewrite (mixed_list_match_n vmatch p 0 0 pm (Base (Empty #t)) [])
    as (mixed_list_match vmatch p pm (Base (Empty #t)) []);
}

(* ================================================================ *)
(* Singleton mixed_list                                              *)
(* ================================================================ *)

(* Build a one-element mixed_list from an element [y_elem] (matching [y] at
   permission [pm_y]) stored into the caller-provided reference [ry]. The
   result is produced at ambient permission 1.0R, with a trade returning the
   element match and the reference. *)
inline_for_extraction
fn mixed_list_singleton
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm_y: perm)
  (y_elem: t) (y: Ghost.erased u)
  (ry: R.ref t)
  (vmatch_gather: gather_t vmatch)
requires
  vmatch pm_y y_elem (Ghost.reveal y) **
  (exists* vy. R.pts_to ry vy)
returns ml_res: mixed_list t
ensures
  mixed_list_match vmatch p 1.0R ml_res [Ghost.reveal y] **
  Trade.trade
    (mixed_list_match vmatch p 1.0R ml_res [Ghost.reveal y])
    (vmatch pm_y y_elem (Ghost.reveal y) ** (exists* vy. R.pts_to ry vy)) **
  pure (mixed_list_length ml_res == 1sz)
{
  with vy0. assert (R.pts_to ry vy0);
  R.write ry y_elem;
  R.share ry;
  let sp_val : Ghost.erased perm = 1.0R /. 2.0R;
  let sv_val : Ghost.erased perm = pm_y;
  let ml_res : mixed_list t = Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
  rewrite (R.pts_to ry #(1.0R /. 2.0R) y_elem)
    as (pts_to ry #(1.0R *. Ghost.reveal sp_val) y_elem);
  rewrite (vmatch pm_y y_elem (Ghost.reveal y))
    as (vmatch (1.0R *. Ghost.reveal sv_val) y_elem (Ghost.reveal y));
  fold (base_mixed_list_match_n vmatch p 0 1 1.0R (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
  fold (mixed_list_match_n vmatch p 0 1 1.0R (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
  rewrite (mixed_list_match_n vmatch p 0 1 1.0R (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y])
    as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) 1.0R ml_res [Ghost.reveal y]);
  fold (mixed_list_match vmatch p 1.0R ml_res [Ghost.reveal y]);
  Trade.intro_trade
    (mixed_list_match vmatch p 1.0R ml_res [Ghost.reveal y])
    (vmatch pm_y y_elem (Ghost.reveal y) ** (exists* vy. R.pts_to ry vy))
    (R.pts_to ry #(1.0R /. 2.0R) y_elem)
    fn _ {
      unfold (mixed_list_match vmatch p 1.0R ml_res [Ghost.reveal y]);
      rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) 1.0R ml_res [Ghost.reveal y])
        as (mixed_list_match_n vmatch p 0 1 1.0R (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
      unfold (mixed_list_match_n vmatch p 0 1 1.0R (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
      unfold (base_mixed_list_match_n vmatch p 0 1 1.0R (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
      with x_sing y_sing. assert (
        pts_to ry #(1.0R *. Ghost.reveal sp_val) x_sing **
        vmatch (1.0R *. Ghost.reveal sv_val) x_sing y_sing
      );
      rewrite (pts_to ry #(1.0R *. Ghost.reveal sp_val) x_sing)
        as (R.pts_to ry #(1.0R /. 2.0R) x_sing);
      R.gather ry;
      rewrite (vmatch (1.0R *. Ghost.reveal sv_val) x_sing y_sing)
        as (vmatch pm_y y_elem (Ghost.reveal y));
      drop_ (pure (Ghost.reveal y_elem == Ghost.reveal x_sing));
      rewrite (R.pts_to ry #(1.0R /. 2.0R +. 1.0R /. 2.0R) y_elem)
        as (R.pts_to ry y_elem);
      fold (exists* vy. R.pts_to ry vy);
    };
  ml_res
}

(* Generalization of [mixed_list_singleton] to an arbitrary target ambient
   permission [a]. The [Singleton] node permissions are scaled by [1/a] so that
   after multiplying by the ambient [a] they cancel back to the concrete
   reference half-permission [1/2] and the element permission [pm_y]. The trade
   restores exactly the original (ambient-independent) resources. *)
inline_for_extraction
fn mixed_list_singleton_gen
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (a: perm)
  (pm_y: perm)
  (y_elem: t) (y: Ghost.erased u)
  (ry: R.ref t)
  (vmatch_gather: gather_t vmatch)
requires
  vmatch pm_y y_elem (Ghost.reveal y) **
  (exists* vy. R.pts_to ry vy)
returns ml_res: mixed_list t
ensures
  mixed_list_match vmatch p a ml_res [Ghost.reveal y] **
  Trade.trade
    (mixed_list_match vmatch p a ml_res [Ghost.reveal y])
    (vmatch pm_y y_elem (Ghost.reveal y) ** (exists* vy. R.pts_to ry vy)) **
  pure (mixed_list_length ml_res == 1sz)
{
  with vy0. assert (R.pts_to ry vy0);
  R.write ry y_elem;
  R.share ry;
  let sp_val : Ghost.erased perm = (1.0R /. 2.0R) /. a;
  let sv_val : Ghost.erased perm = pm_y /. a;
  let ml_res : mixed_list t = Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry);
  perm_mul_div_cancel' a (1.0R /. 2.0R);
  perm_mul_div_cancel' a pm_y;
  rewrite (R.pts_to ry #(1.0R /. 2.0R) y_elem)
    as (pts_to ry #(a *. Ghost.reveal sp_val) y_elem);
  rewrite (vmatch pm_y y_elem (Ghost.reveal y))
    as (vmatch (a *. Ghost.reveal sv_val) y_elem (Ghost.reveal y));
  fold (base_mixed_list_match_n vmatch p 0 1 a (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
  fold (mixed_list_match_n vmatch p 0 1 a (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
  rewrite (mixed_list_match_n vmatch p 0 1 a (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y])
    as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) a ml_res [Ghost.reveal y]);
  fold (mixed_list_match vmatch p a ml_res [Ghost.reveal y]);
  perm_mul_div_cancel' a (1.0R /. 2.0R);
  perm_mul_div_cancel' a pm_y;
  Trade.intro_trade
    (mixed_list_match vmatch p a ml_res [Ghost.reveal y])
    (vmatch pm_y y_elem (Ghost.reveal y) ** (exists* vy. R.pts_to ry vy))
    (R.pts_to ry #(1.0R /. 2.0R) y_elem **
     pure (a *. Ghost.reveal sp_val == 1.0R /. 2.0R /\ a *. Ghost.reveal sv_val == pm_y))
    fn _ {
      unfold (mixed_list_match vmatch p a ml_res [Ghost.reveal y]);
      rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) a ml_res [Ghost.reveal y])
        as (mixed_list_match_n vmatch p 0 1 a (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
      unfold (mixed_list_match_n vmatch p 0 1 a (Base (Singleton (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry)) [Ghost.reveal y]);
      unfold (base_mixed_list_match_n vmatch p 0 1 a (Singleton #t (Ghost.reveal sp_val) (Ghost.reveal sv_val) ry) [Ghost.reveal y]);
      with x_sing y_sing. assert (
        pts_to ry #(a *. Ghost.reveal sp_val) x_sing **
        vmatch (a *. Ghost.reveal sv_val) x_sing y_sing
      );
      rewrite (pts_to ry #(a *. Ghost.reveal sp_val) x_sing)
        as (R.pts_to ry #(1.0R /. 2.0R) x_sing);
      R.gather ry;
      rewrite (vmatch (a *. Ghost.reveal sv_val) x_sing y_sing)
        as (vmatch pm_y y_elem (Ghost.reveal y));
      drop_ (pure (Ghost.reveal y_elem == Ghost.reveal x_sing));
      rewrite (R.pts_to ry #(1.0R /. 2.0R +. 1.0R /. 2.0R) y_elem)
        as (R.pts_to ry y_elem);
      fold (exists* vy. R.pts_to ry vy);
    };
  ml_res
}

(* ================================================================ *)
(* Append of two mixed_lists                                         *)
(* ================================================================ *)

(* Append two mixed_lists held at the SAME ambient permission [pm]. The result
   is the structural Append node, produced at ambient [pm], matching the
   concatenation of the two lists, with a trade returning both inputs and the
   two caller-provided references. O(1): no element copy and no re-encoding. *)
inline_for_extraction
fn mixed_list_append
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm)
  (ml_a: mixed_list t) (l_a: Ghost.erased (list u))
  (ml_b: mixed_list t) (l_b: Ghost.erased (list u))
  (r_before: R.ref (mixed_list t)) (r_after: R.ref (mixed_list t))
requires
  mixed_list_match vmatch p pm ml_a (Ghost.reveal l_a) **
  mixed_list_match vmatch p pm ml_b (Ghost.reveal l_b) **
  (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va) **
  pure (SZ.fits (SZ.v (mixed_list_length ml_a) + SZ.v (mixed_list_length ml_b)))
returns ml_res: mixed_list t
ensures
  mixed_list_match vmatch p pm ml_res (List.Tot.append (Ghost.reveal l_a) (Ghost.reveal l_b)) **
  Trade.trade
    (mixed_list_match vmatch p pm ml_res (List.Tot.append (Ghost.reveal l_a) (Ghost.reveal l_b)))
    (mixed_list_match vmatch p pm ml_a (Ghost.reveal l_a) **
     mixed_list_match vmatch p pm ml_b (Ghost.reveal l_b) **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va)) **
  pure (SZ.v (mixed_list_length ml_res) == SZ.v (mixed_list_length ml_a) + SZ.v (mixed_list_length ml_b))
{
  mixed_list_match_length vmatch p pm ml_a (Ghost.reveal l_a);
  mixed_list_match_length vmatch p pm ml_b (Ghost.reveal l_b);
  let len_a = mixed_list_length ml_a;
  let len_b = mixed_list_length ml_b;
  let depth : Ghost.erased nat =
    (if mixed_list_depth ml_a > mixed_list_depth ml_b
     then mixed_list_depth ml_a else mixed_list_depth ml_b) + 1;
  let bp : Ghost.erased perm = (1.0R /. 2.0R) /. pm;
  R.write r_before ml_a;
  R.share r_before;
  R.write r_after ml_b;
  R.share r_after;
  let ml_res : mixed_list t = Append (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after;
  let lres : Ghost.erased (list u) = List.Tot.append (Ghost.reveal l_a) (Ghost.reveal l_b);
  perm_mul_div_cancel' pm (1.0R /. 2.0R);
  rewrite (R.pts_to r_before #(1.0R /. 2.0R) ml_a)
    as (pts_to r_before #(pm *. Ghost.reveal bp) ml_a);
  rewrite (R.pts_to r_after #(1.0R /. 2.0R) ml_b)
    as (pts_to r_after #(pm *. Ghost.reveal bp) ml_b);
  rewrite (mixed_list_match vmatch p pm ml_a (Ghost.reveal l_a))
    as (mixed_list_match_n vmatch p (append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_before 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ml_a (Ghost.reveal l_a));
  rewrite (mixed_list_match vmatch p pm ml_b (Ghost.reveal l_b))
    as (mixed_list_match_n vmatch p (append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_after 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ml_b (Ghost.reveal l_b));
  List.Tot.Properties.append_length (Ghost.reveal l_a) (Ghost.reveal l_b);
  intro_pure (
    0 + SZ.v (mixed_list_length ml_res) <= SZ.v len_a + SZ.v len_b /\
    SZ.v 0sz + SZ.v len_a <= SZ.v (mixed_list_length ml_a) /\
    SZ.v 0sz + SZ.v len_b <= SZ.v (mixed_list_length ml_b) /\
    List.Tot.length (Ghost.reveal l_a) == append_n_before 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a) /\
    List.Tot.length (Ghost.reveal l_b) == append_n_after 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a) /\
    Ghost.reveal lres == List.Tot.append (Ghost.reveal l_a) (Ghost.reveal l_b) /\
    mixed_list_depth ml_a < Ghost.reveal depth /\
    mixed_list_depth ml_b < Ghost.reveal depth
  ) ();
  fold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) pm
    (Append #t (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
    (Ghost.reveal lres));
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) pm
    (Append #t (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
    (Ghost.reveal lres))
    as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) pm ml_res (Ghost.reveal lres));
  fold (mixed_list_match vmatch p pm ml_res (Ghost.reveal lres));
  perm_mul_div_cancel' pm (1.0R /. 2.0R);
  Trade.intro_trade
    (mixed_list_match vmatch p pm ml_res (Ghost.reveal lres))
    (mixed_list_match vmatch p pm ml_a (Ghost.reveal l_a) **
     mixed_list_match vmatch p pm ml_b (Ghost.reveal l_b) **
     (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va))
    (R.pts_to r_before #(1.0R /. 2.0R) ml_a **
     R.pts_to r_after #(1.0R /. 2.0R) ml_b **
     pure (pm *. Ghost.reveal bp == 1.0R /. 2.0R))
    fn _ {
      unfold (mixed_list_match vmatch p pm ml_res (Ghost.reveal lres));
      rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) pm ml_res (Ghost.reveal lres))
        as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) pm
              (Append #t (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
              (Ghost.reveal lres));
      unfold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_res)) pm
              (Append #t (Ghost.reveal depth) len_a len_b 0sz (Ghost.reveal bp) r_before 0sz (Ghost.reveal bp) r_after)
              (Ghost.reveal lres));
      with ib_u ia_u l1_u l2_u. assert (
        pts_to r_before #(pm *. Ghost.reveal bp) ib_u **
        mixed_list_match_n vmatch p (append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_before 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ib_u l1_u **
        pts_to r_after #(pm *. Ghost.reveal bp) ia_u **
        mixed_list_match_n vmatch p (append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_after 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ia_u l2_u
      );
      rewrite (pts_to r_before #(pm *. Ghost.reveal bp) ib_u)
        as (R.pts_to r_before #(1.0R /. 2.0R) ib_u);
      R.gather r_before;
      drop_ (pure (Ghost.reveal ml_a == Ghost.reveal ib_u));
      rewrite (R.pts_to r_before #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_a)
        as (R.pts_to r_before ml_a);
      rewrite (pts_to r_after #(pm *. Ghost.reveal bp) ia_u)
        as (R.pts_to r_after #(1.0R /. 2.0R) ia_u);
      R.gather r_after;
      drop_ (pure (Ghost.reveal ml_b == Ghost.reveal ia_u));
      rewrite (R.pts_to r_after #(1.0R /. 2.0R +. 1.0R /. 2.0R) ml_b)
        as (R.pts_to r_after ml_b);
      mixed_list_match_n_length vmatch p (append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_before 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ib_u l1_u;
      mixed_list_match_n_length vmatch p (append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_after 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ia_u l2_u;
      List.Tot.Properties.append_injective l1_u (Ghost.reveal l_a) l2_u (Ghost.reveal l_b);
      rewrite (mixed_list_match_n vmatch p (append_off_before 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_before 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ib_u l1_u)
        as (mixed_list_match vmatch p pm ml_a (Ghost.reveal l_a));
      rewrite (mixed_list_match_n vmatch p (append_off_after 0 (SZ.v 0sz) (SZ.v len_a)) (append_n_after 0 (SZ.v (mixed_list_length ml_res)) (SZ.v len_a)) pm ia_u l2_u)
        as (mixed_list_match vmatch p pm ml_b (Ghost.reveal l_b));
      fold (exists* vb va. R.pts_to r_before vb ** R.pts_to r_after va);
    };
  rewrite each (Ghost.reveal lres) as (List.Tot.append (Ghost.reveal l_a) (Ghost.reveal l_b));
  ml_res
}
