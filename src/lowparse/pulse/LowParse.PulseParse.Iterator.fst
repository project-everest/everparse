module LowParse.PulseParse.Iterator
#lang-pulse
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
open LowParse.PulseParse.Iterator.Type
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module LPS = LowParse.Pulse.Base
module LPV = LowParse.Pulse.VCList
open Pulse.Lib.Trade

let share_t = LowParse.PulseParse.Base.share_t

let gather_t = LowParse.PulseParse.Base.gather_t

let mixed_list_depth (#t: Type) (i: mixed_list t) : GTot nat =
  match i with
  | Base _ -> 0
  | Append depth _ _ _ _ _ _ _ _ -> Ghost.reveal depth

module SM = Pulse.Lib.SeqMatch

// Helper functions for Append child offset/count arithmetic
let append_n_before (off n cb: nat) : nat =
  if off >= cb then 0 else min n (cb - off)

let append_n_after (off n cb: nat) : nat =
  n - append_n_before off n cb

let append_off_before (off ob cb: nat) : nat =
  ob + (if off >= cb then cb else off)

let append_off_after (off oa cb: nat) : nat =
  oa + (if off >= cb then off - cb else 0)

let base_mixed_list_match_n
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
: Tot slprop
= match i with
  | Empty -> pure (Nil? l /\ n == 0 /\ off == 0)
  | Singleton sp sv s -> if n = 0 then pure (Nil? l /\ off <= 1) else exists* x y .
    pts_to s #(pm *. sp) x **
    vmatch (pm *. sv) x y **
    pure (l == [y] /\ off == 0 /\ n == 1)
  | Slice sp sv s -> exists* l' l1 .
    pts_to s #(pm *. sp) l' **
    SM.seq_list_match l1 l (vmatch (pm *. sv)) **
    pure (
      off + n <= Seq.length l' /\
      l1 == Seq.slice l' off (off + n)
    )
  | Serialized sp count pl -> exists* l_all .
    pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all **
    pure (l == snd (List.Tot.splitAt off l_all) /\ off + n <= SZ.v count)

let base_mixed_list_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
: Tot slprop
= base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length i)) pm i l

let rec mixed_list_match_n
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
: Tot slprop
  (decreases (mixed_list_depth i))
= match i with
  | Base i -> base_mixed_list_match_n vmatch p off n pm i l
  | Append depth cb ca ob bp before oa ap after ->
    let n1 = append_n_before off n (SZ.v cb) in
    let n' = append_n_after off n (SZ.v cb) in
    let off_b = append_off_before off (SZ.v ob) (SZ.v cb) in
    let off_a = append_off_after off (SZ.v oa) (SZ.v cb) in
    exists* i_before i_after l1 l2 .
      pts_to before #(pm *. bp) i_before **
      mixed_list_match_n vmatch p off_b n1 pm i_before l1 **
      pts_to after #(pm *. ap) i_after **
      mixed_list_match_n vmatch p off_a n' pm i_after l2 **
      pure (
        off + n <= SZ.v cb + SZ.v ca /\
        SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
        SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
        List.Tot.length l1 == n1 /\
        List.Tot.length l2 == n' /\
        l == List.Tot.append l1 l2 /\
        mixed_list_depth i_before < Ghost.reveal depth /\
        mixed_list_depth i_after < Ghost.reveal depth
      )

let mixed_list_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
: Tot slprop
= mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length i)) pm i l

open FStar.Real

let slprop_rw : (p:slprop -> q:slprop -> slprop_equiv p q -> stt_ghost unit emp_inames p (fun _ -> q)) =
  _ by (FStar.Tactics.V2.exact (FStar.Tactics.V2.pack (FStar.Tactics.V2.Tv_FVar (FStar.Tactics.V2.pack_fv ["Pulse"; "Lib"; "Core"; "rewrite"]))))

// Singleton lemmas adapted for offset parameter

let base_mixed_list_match_n_singleton_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
: Lemma (base_mixed_list_match_n vmatch p off 0 pm (Singleton sp sv s) l == pure (Nil? l /\ off <= 1))
= ()

let base_mixed_list_match_n_singleton_unfold_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n == 0))
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (fun _ -> pure (Nil? l /\ off <= 1))
= slprop_rw
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (pure (Nil? l /\ off <= 1))
    (Pulse.Lib.Core.slprop_equiv_ext'
       (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
       (pure (Nil? l /\ off <= 1))
       ())

let base_mixed_list_match_n_singleton_fold_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n == 0))
: stt_ghost unit emp_inames
    (pure (Nil? l /\ off <= 1))
    (fun _ -> base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
= slprop_rw
    (pure (Nil? l /\ off <= 1))
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (Pulse.Lib.Core.slprop_equiv_sym
       (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
       (pure (Nil? l /\ off <= 1))
       (Pulse.Lib.Core.slprop_equiv_ext'
          (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
          (pure (Nil? l /\ off <= 1))
          ()))

let base_mixed_list_match_n_singleton_pos
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n <> 0))
: Lemma
    (ensures base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l ==
             (exists* x y .
                pts_to s #(pm *. sp) x **
                vmatch (pm *. sv) x y **
                pure (l == [y] /\ off == 0 /\ n == 1)))
= norm_spec [delta_only [`%base_mixed_list_match_n]; iota; zeta] (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)

let base_mixed_list_match_n_singleton_unfold_pos
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n <> 0))
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (fun _ -> exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
= base_mixed_list_match_n_singleton_pos vmatch p off n pm sp sv s l ();
  slprop_rw
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
    (Pulse.Lib.Core.slprop_equiv_ext'
       (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
       (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
       ())

let base_mixed_list_match_n_singleton_fold_pos
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n <> 0))
: stt_ghost unit emp_inames
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
    (fun _ -> base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
= base_mixed_list_match_n_singleton_pos vmatch p off n pm sp sv s l ();
  slprop_rw
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (Pulse.Lib.Core.slprop_equiv_sym
       (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
       (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
       (Pulse.Lib.Core.slprop_equiv_ext'
          (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
          (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
          ()))

let dup_pure (p: prop)
: stt_ghost unit emp_inames (pure p) (fun _ -> pure p ** pure p)
= Pulse.Lib.Core.bind_ghost
    (Pulse.Lib.Core.elim_pure_explicit p)
    (fun (s: squash p) ->
      Pulse.Lib.Core.bind_ghost
        (Pulse.Lib.Core.intro_pure p s)
        (fun _ ->
          Pulse.Lib.Core.sub_ghost
            (pure p)
            (fun _ -> pure p ** pure p)
            (Pulse.Lib.Core.slprop_equiv_unit (pure p))
            (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_refl _))
            (Pulse.Lib.Core.frame_ghost
              (pure p)
              (Pulse.Lib.Core.intro_pure p s))))

// Helper: pure p ** pure q --> pure p ** pure r, given p /\ q ==> r
```pulse
ghost
fn replace_second_pure (p q r: prop) (f: squash (p ==> q ==> r))
requires pure p ** pure q
ensures pure p ** pure r
{
  drop_ (pure q)
}
```

```pulse
ghost
fn base_mixed_list_match_n_singleton_share_pos_inner
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (vmatch_share: (
    (x1: t) -> (pm0: perm) -> (x2: u) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2) (fun _ -> vmatch (pm0 /. 2.0R) x1 x2 ** vmatch (pm0 /. 2.0R) x1 x2)
  ))
  (_: squash (n <> 0))
requires base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l
ensures base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l **
        base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
  with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1));
  R.share s;
  rewrite (R.pts_to s #(pm *. sp /. 2.0R) x) as (R.pts_to s #(pm /. 2.0R *. sp) x);
  rewrite (R.pts_to s #(pm *. sp /. 2.0R) x) as (R.pts_to s #(pm /. 2.0R *. sp) x);
  vmatch_share x (pm *. sv) y;
  rewrite (vmatch (pm *. sv /. 2.0R) x y) as (vmatch (pm /. 2.0R *. sv) x y);
  rewrite (vmatch (pm *. sv /. 2.0R) x y) as (vmatch (pm /. 2.0R *. sv) x y);
  base_mixed_list_match_n_singleton_fold_pos vmatch p off n (pm /. 2.0R) sp sv s l ();
  base_mixed_list_match_n_singleton_fold_pos vmatch p off n (pm /. 2.0R) sp sv s l ()
}
```

let base_mixed_list_match_n_singleton_share
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (vmatch_share: share_t vmatch)
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
    (fun _ -> base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l **
              base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l)
= if n = 0
  then begin
    base_mixed_list_match_n_singleton_0 vmatch p off pm sp sv s l;
    base_mixed_list_match_n_singleton_0 vmatch p off (pm /. 2.0R) sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l)
      (fun _ -> base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l **
                base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l)
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (dup_pure (Nil? l /\ off <= 1))
  end
  else
    base_mixed_list_match_n_singleton_share_pos_inner #t #u vmatch #k p off n pm sp sv s l (fun x1 pm0 x2 -> vmatch_share x1 #pm0 #x2) ()

```pulse
ghost
fn base_mixed_list_match_n_singleton_gather_pos_inner
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l l': list u)
  (vmatch_gather: (
    (x1: t) -> (pm0: perm) -> (x2: u) -> (pm0': perm) -> (x2': u) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
  (_: squash (n <> 0))
requires base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l **
         base_mixed_list_match_n vmatch p off n pm' (Singleton sp sv s) l'
ensures base_mixed_list_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l ** pure (l == l')
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
  base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm' sp sv s l' ();
  with x1 y1. assert (pts_to s #(pm *. sp) x1 ** vmatch (pm *. sv) x1 y1 ** pure (l == [y1] /\ off == 0 /\ n == 1));
  with x2 y2. assert (pts_to s #(pm' *. sp) x2 ** vmatch (pm' *. sv) x2 y2 ** pure (l' == [y2] /\ off == 0 /\ n == 1));
  R.gather s;
  rewrite (R.pts_to s #(pm *. sp +. pm' *. sp) x1) as (R.pts_to s #((pm +. pm') *. sp) x1);
  rewrite each x2 as x1;
  vmatch_gather x1 (pm *. sv) y1 (pm' *. sv) y2;
  rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
  base_mixed_list_match_n_singleton_fold_pos vmatch p off n (pm +. pm') sp sv s l ()
}
```

let base_mixed_list_match_n_singleton_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l **
     base_mixed_list_match_n vmatch p off n pm' (Singleton sp sv s) l')
    (fun _ -> base_mixed_list_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
              pure (l == l'))
= if n = 0
  then begin
    base_mixed_list_match_n_singleton_0 vmatch p off pm sp sv s l;
    base_mixed_list_match_n_singleton_0 vmatch p off pm' sp sv s l';
    base_mixed_list_match_n_singleton_0 vmatch p off (pm +. pm') sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l **
       base_mixed_list_match_n vmatch p off n pm' (Singleton sp sv s) l')
      (fun _ -> base_mixed_list_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
                pure (l == l'))
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (replace_second_pure (Nil? l /\ off <= 1) (Nil? l' /\ off <= 1) (l == l') ())
  end
  else
    base_mixed_list_match_n_singleton_gather_pos_inner #t #u vmatch #k p off n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2') ()

ghost
fn rec seq_list_match_share
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match1: (t -> (v': t' { v' << v }) -> slprop))
  (item_match2: (t -> (v': t' { v' << v }) -> slprop))
  (prf: (
    (c': t) ->
    (v': t' { v' << v }) ->
    stt_ghost unit emp_inames
      (item_match1 c' v')
      (fun _ -> item_match2 c' v' ** item_match2 c' v')
  ))
requires
    (SM.seq_list_match c v item_match1)
ensures
    (SM.seq_list_match c v item_match2 ** SM.seq_list_match c v item_match2)
  decreases v
{
  if Nil? v {
    SM.seq_list_match_nil_elim c v item_match1;
    SM.seq_list_match_nil_intro c v item_match2;
    SM.seq_list_match_nil_intro c v item_match2;
  } else {
    SM.list_cons_precedes (List.Tot.hd v) (List.Tot.tl v);
    let _ : squash (List.Tot.tl v << v) = ();
    SM.seq_list_match_cons_elim c v item_match1;
    prf (Seq.head c) (List.Tot.hd v);
    ghost fn prf'
      (c': t)
      (v': t' { v' << List.Tot.tl v })
    requires
      item_match1 c' v'
    ensures
      item_match2 c' v' ** item_match2 c' v'
    {
      prf c' v'
    };
    seq_list_match_share (Seq.tail c) (List.Tot.tl v) item_match1 item_match2 prf';
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match2;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd v :: List.Tot.tl v) item_match2)
         as (SM.seq_list_match c v item_match2);
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match2;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd v :: List.Tot.tl v) item_match2)
         as (SM.seq_list_match c v item_match2);
    ()
  }
}

#push-options "--fuel 4 --ifuel 4"

ghost
fn rec seq_list_match_gather_memP
  (#t #t': Type0)
  (c: Seq.seq t)
  (v1: list t')
  (v2: list t')
  (item_match1: (t -> (v': t' { v' << v1 }) -> slprop))
  (item_match2: (t -> (v': t' { v' << v2 }) -> slprop))
  (item_match3: (t -> (v': t' { v' << v1 }) -> slprop))
  (prf: (
    (c': t) ->
    (v1': t' { v1' << v1 }) ->
    (v2': t' { v2' << v2 /\ List.Tot.memP v2' v2 }) ->
    stt_ghost unit emp_inames
      (item_match1 c' v1' ** item_match2 c' v2')
      (fun _ -> item_match3 c' v1' ** pure ((v1' <: t') == (v2' <: t')))
  ))
requires
    (SM.seq_list_match c v1 item_match1 ** SM.seq_list_match c v2 item_match2)
ensures
    (SM.seq_list_match c v1 item_match3 ** pure (v1 == v2))
  decreases v1
{
  if Nil? v1 {
    SM.seq_list_match_nil_elim c v1 item_match1;
    SM.seq_list_match_nil_elim c v2 item_match2;
    SM.seq_list_match_nil_intro c v1 item_match3;
  } else {
    SM.list_cons_precedes (List.Tot.hd v1) (List.Tot.tl v1);
    let _ : squash (List.Tot.tl v1 << v1) = ();
    SM.seq_list_match_cons_elim c v1 item_match1;
    SM.seq_list_match_cons_elim c v2 item_match2;
    SM.list_cons_precedes (List.Tot.hd v2) (List.Tot.tl v2);
    let _ : squash (List.Tot.tl v2 << v2) = ();
    prf (Seq.head c) (List.Tot.hd v1) (List.Tot.hd v2);
    ghost fn prf'
      (c': t)
      (v1': t' { v1' << List.Tot.tl v1 })
      (v2': t' { v2' << List.Tot.tl v2 /\ List.Tot.memP v2' (List.Tot.tl v2) })
    requires
      item_match1 c' v1' ** item_match2 c' v2'
    ensures
      item_match3 c' v1' ** pure ((v1' <: t') == (v2' <: t'))
    {
      prf c' v1' v2'
    };
    seq_list_match_gather_memP (Seq.tail c) (List.Tot.tl v1) (List.Tot.tl v2) item_match1 item_match2 item_match3 prf';
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v1) (Seq.tail c) (List.Tot.tl v1) item_match3;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd v1 :: List.Tot.tl v1) item_match3)
         as (SM.seq_list_match c v1 item_match3);
    ()
  }
}

#pop-options

#push-options "--z3rlimit 20"

```pulse
ghost
fn base_mixed_list_match_n_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
  (vmatch_share: share_t vmatch)
requires
  base_mixed_list_match_n vmatch p off n pm i l
ensures
  base_mixed_list_match_n vmatch p off n (pm /. 2.0R) i l **
  base_mixed_list_match_n vmatch p off n (pm /. 2.0R) i l
{
  match i {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Empty #t) l);
      fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
      fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_mixed_list_match_n_singleton_share vmatch p off n pm sp sv s l vmatch_share;
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      with l' l1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      S.share s;
      rewrite (pts_to s #((pm *. sp) /. 2.0R) l') as (pts_to s #((pm /. 2.0R) *. sp) l');
      rewrite (pts_to s #((pm *. sp) /. 2.0R) l') as (pts_to s #((pm /. 2.0R) *. sp) l');
      ghost fn share_prf
        (c': t)
        (v': u { v' << l })
      requires vmatch (pm *. sv) c' v'
      ensures vmatch ((pm /. 2.0R) *. sv) c' v' ** vmatch ((pm /. 2.0R) *. sv) c' v'
      {
        vmatch_share c' #(pm *. sv) #v';
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
      };
      seq_list_match_share l1 l (vmatch (pm *. sv)) (vmatch ((pm /. 2.0R) *. sv)) share_prf;
      fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Slice #t sp sv s) l);
      fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      with l' . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l');
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l');
      with v' . assert (S.pts_to pl #(pm *. sp) v');
      S.share pl;
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) l');
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) l');
      fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Serialized #t sp count pl) l);
      fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options

```pulse
ghost
fn base_mixed_list_match_n_singleton_gather_bound_pos_inner
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (pm0: perm) -> (x2: u) -> (pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
  (_: squash (n <> 0))
requires base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l **
         base_mixed_list_match_n vmatch p off n pm' (Singleton sp sv s) l'
ensures base_mixed_list_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l ** pure (l == l')
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
  base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm' sp sv s l' ();
  with x1 y1. assert (pts_to s #(pm *. sp) x1 ** vmatch (pm *. sv) x1 y1 ** pure (l == [y1] /\ off == 0 /\ n == 1));
  with x2 y2. assert (pts_to s #(pm' *. sp) x2 ** vmatch (pm' *. sv) x2 y2 ** pure (l' == [y2] /\ off == 0 /\ n == 1));
  R.gather s;
  rewrite (R.pts_to s #(pm *. sp +. pm' *. sp) x1) as (R.pts_to s #((pm +. pm') *. sp) x1);
  rewrite each x2 as x1;
  vmatch_gather x1 (pm *. sv) y1 (pm' *. sv) y2;
  rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
  base_mixed_list_match_n_singleton_fold_pos vmatch p off n (pm +. pm') sp sv s l ()
}
```

let base_mixed_list_match_n_singleton_gather_bound
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l **
     base_mixed_list_match_n vmatch p off n pm' (Singleton sp sv s) l')
    (fun _ -> base_mixed_list_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
              pure (l == l'))
= if n = 0
  then begin
    base_mixed_list_match_n_singleton_0 vmatch p off pm sp sv s l;
    base_mixed_list_match_n_singleton_0 vmatch p off pm' sp sv s l';
    base_mixed_list_match_n_singleton_0 vmatch p off (pm +. pm') sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_mixed_list_match_n vmatch p off n pm (Singleton sp sv s) l **
       base_mixed_list_match_n vmatch p off n pm' (Singleton sp sv s) l')
      (fun _ -> base_mixed_list_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
                pure (l == l'))
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (replace_second_pure (Nil? l /\ off <= 1) (Nil? l' /\ off <= 1) (l == l') ())
  end
  else
    base_mixed_list_match_n_singleton_gather_bound_pos_inner #t #u vmatch #k p off n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' x2') ()

#push-options "--z3rlimit 20"

```pulse
ghost
fn base_mixed_list_match_n_gather_bound
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: base_mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
requires
  base_mixed_list_match_n vmatch p off n pm i l **
  base_mixed_list_match_n vmatch p off n pm' i l'
ensures
  base_mixed_list_match_n vmatch p off n (pm +. pm') i l **
  pure (l == l')
{
  match i {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Empty #t) l);
      unfold (base_mixed_list_match_n vmatch p off n pm' (Empty #t) l');
      fold (base_mixed_list_match_n vmatch p off n (pm +. pm') (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_mixed_list_match_n_singleton_gather_bound #t #u vmatch p off n pm pm' sp sv s l l' vmatch_gather;
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      unfold (base_mixed_list_match_n vmatch p off n pm' (Slice #t sp sv s) l');
      with la l1 . assert (pts_to s #(pm *. sp) la ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      with la' l1' . assert (pts_to s #(pm' *. sp) la' ** SM.seq_list_match l1' l' (vmatch (pm' *. sv)));
      S.gather s;
      rewrite (pts_to s #(pm *. sp +. pm' *. sp) la) as (pts_to s #((pm +. pm') *. sp) la);
      rewrite each la' as la;
      rewrite each l1' as l1;
      ghost fn gather_prf
        (c': t)
        (v1': u { v1' << l })
        (v2': u { v2' << l' /\ List.Tot.memP v2' l' })
      requires vmatch (pm *. sv) c' v1' ** vmatch (pm' *. sv) c' v2'
      ensures vmatch ((pm +. pm') *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
      {
        vmatch_gather c' #(pm *. sv) #v1' #(pm' *. sv) v2';
        rewrite (vmatch (pm *. sv +. pm' *. sv) c' v1') as (vmatch ((pm +. pm') *. sv) c' v1');
      };
      seq_list_match_gather_memP l1 l l' (vmatch (pm *. sv)) (vmatch (pm' *. sv)) (vmatch ((pm +. pm') *. sv)) gather_prf;
      fold (base_mixed_list_match_n vmatch p off n (pm +. pm') (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      unfold (base_mixed_list_match_n vmatch p off n pm' (Serialized #t sp count pl) l');
      with lv . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) lv);
      with lv' . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm' *. sp) lv');
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) lv);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm' *. sp) lv');
      with v1 . assert (S.pts_to pl #(pm *. sp) v1);
      with v2 . assert (S.pts_to pl #(pm' *. sp) v2);
      S.gather pl;
      rewrite (S.pts_to pl #(pm *. sp +. pm' *. sp) v1) as (S.pts_to pl #((pm +. pm') *. sp) v1);
      rewrite each v2 as v1;
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm +. pm') *. sp) lv);
      fold (base_mixed_list_match_n vmatch p off n (pm +. pm') (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options

let base_mixed_list_match_n_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: base_mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch p off n pm i l **
     base_mixed_list_match_n vmatch p off n pm' i l')
    (fun _ ->
      base_mixed_list_match_n vmatch p off n (pm +. pm') i l **
      pure (l == l'))
= base_mixed_list_match_n_gather_bound #t #u vmatch #k p off n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')

#push-options "--z3rlimit 20"

```pulse
ghost
fn rec mixed_list_match_n_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
  (vmatch_share: share_t vmatch)
requires
  mixed_list_match_n vmatch p off n pm i l
ensures
  mixed_list_match_n vmatch p off n (pm /. 2.0R) i l **
  mixed_list_match_n vmatch p off n (pm /. 2.0R) i l
decreases (mixed_list_depth i)
{
  match i {
    Base bi -> {
      unfold (mixed_list_match_n vmatch p off n pm (Base bi) l);
      base_mixed_list_match_n_share vmatch p off n pm bi l vmatch_share;
      fold (mixed_list_match_n vmatch p off n (pm /. 2.0R) (Base bi) l);
      fold (mixed_list_match_n vmatch p off n (pm /. 2.0R) (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
          SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
          List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
          l == List.Tot.append l1 l2 /\
          mixed_list_depth i_before < Ghost.reveal depth /\
          mixed_list_depth i_after < Ghost.reveal depth
        )
      );
      R.share before;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      mixed_list_match_n_share vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 vmatch_share;
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      mixed_list_match_n_share vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 vmatch_share;
      dup_pure (
        off + n <= SZ.v cb + SZ.v ca /\
        SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
        SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
        List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
        List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
        l == List.Tot.append l1 l2 /\
        mixed_list_depth i_before < Ghost.reveal depth /\
        mixed_list_depth i_after < Ghost.reveal depth
      );
      fold (mixed_list_match_n vmatch p off n (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) l);
      fold (mixed_list_match_n vmatch p off n (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

```pulse
ghost
fn rec mixed_list_match_n_gather_bound
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
requires
  mixed_list_match_n vmatch p off n pm i l **
  mixed_list_match_n vmatch p off n pm' i l'
ensures
  mixed_list_match_n vmatch p off n (pm +. pm') i l **
  pure (l == l')
decreases (mixed_list_depth i)
{
  match i {
    Base bi -> {
      unfold (mixed_list_match_n vmatch p off n pm (Base bi) l);
      unfold (mixed_list_match_n vmatch p off n pm' (Base bi) l');
      base_mixed_list_match_n_gather_bound vmatch p off n pm pm' bi l l' vmatch_gather;
      fold (mixed_list_match_n vmatch p off n (pm +. pm') (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      unfold (mixed_list_match_n vmatch p off n pm' (Append #t depth cb ca ob bp before oa ap after) l');
      with i_before1 i_after1 l1 l2 . assert (
        pts_to before #(pm *. bp) i_before1 **
        mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before1 l1 **
        pts_to after #(pm *. ap) i_after1 **
        mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after1 l2 **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before1) /\
          SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after1) /\
          List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
          l == List.Tot.append l1 l2 /\
          mixed_list_depth i_before1 < Ghost.reveal depth /\
          mixed_list_depth i_after1 < Ghost.reveal depth
        )
      );
      with i_before2 i_after2 l1' l2' . assert (
        pts_to before #(pm' *. bp) i_before2 **
        mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm' i_before2 l1' **
        pts_to after #(pm' *. ap) i_after2 **
        mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm' i_after2 l2' **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before2) /\
          SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after2) /\
          List.Tot.length l1' == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2' == append_n_after off n (SZ.v cb) /\
          l' == List.Tot.append l1' l2' /\
          mixed_list_depth i_before2 < Ghost.reveal depth /\
          mixed_list_depth i_after2 < Ghost.reveal depth
        )
      );
      // Gather the ref 'before'
      R.gather before;
      rewrite (R.pts_to before #(pm *. bp +. pm' *. bp) i_before1) as (R.pts_to before #((pm +. pm') *. bp) i_before1);
      rewrite each i_before2 as i_before1;
      // Align the pm' mixed_list_match_n for before
      with ib_x l1x . assert (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm' ib_x l1x);
      slprop_rw
        (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before1 l1)
        (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm ib_x l1)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before1 l1)
          (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm ib_x l1)
          ());
      // Gather the recursive mixed_list_match_n for i_before
      ghost fn before_gather_fn
        (x1: t) (#pm0: perm) (#x2: u) (#pm0': perm) (x2': u { List.Tot.memP x2' l1x })
      requires vmatch pm0 x1 x2 ** vmatch pm0' x1 x2'
      ensures vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
      {
        FStar.List.Tot.Properties.append_memP l1x l2' x2';
        vmatch_gather x1 #pm0 #x2 #pm0' x2'
      };
      mixed_list_match_n_gather_bound vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm pm' ib_x l1 l1x before_gather_fn;
      // Gather the ref 'after'
      R.gather after;
      rewrite (R.pts_to after #(pm *. ap +. pm' *. ap) i_after1) as (R.pts_to after #((pm +. pm') *. ap) i_after1);
      rewrite each i_after2 as i_after1;
      // Align the pm' mixed_list_match_n for after
      with ia_x l2x . assert (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm' ia_x l2x);
      slprop_rw
        (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after1 l2)
        (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm ia_x l2)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after1 l2)
          (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm ia_x l2)
          ());
      // Gather the recursive mixed_list_match_n for i_after
      ghost fn after_gather_fn
        (x1: t) (#pm0: perm) (#x2: u) (#pm0': perm) (x2': u { List.Tot.memP x2' l2x })
      requires vmatch pm0 x1 x2 ** vmatch pm0' x1 x2'
      ensures vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
      {
        FStar.List.Tot.Properties.append_memP l1 l2x x2';
        vmatch_gather x1 #pm0 #x2 #pm0' x2'
      };
      mixed_list_match_n_gather_bound vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm pm' ia_x l2 l2x after_gather_fn;
      // Now we have mixed_list_match_n ... (pm +. pm') ib_x l1 and ... (pm +. pm') ia_x l2
      // Rewrite back for fold
      slprop_rw
        (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') ib_x l1)
        (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') i_before1 l1)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') ib_x l1)
          (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') i_before1 l1)
          ());
      slprop_rw
        (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') ia_x l2)
        (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') i_after1 l2)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') ia_x l2)
          (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') i_after1 l2)
          ());
      fold (mixed_list_match_n vmatch p off n (pm +. pm') (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

#pop-options

let mixed_list_match_n_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (mixed_list_match_n vmatch p off n pm i l **
     mixed_list_match_n vmatch p off n pm' i l')
    (fun _ ->
      mixed_list_match_n vmatch p off n (pm +. pm') i l **
      pure (l == l'))
= mixed_list_match_n_gather_bound #t #u vmatch #k p off n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')

// Version with i, l, l' implicit — for calling inside closures where values are lambda-wrapped
let mixed_list_match_n_gather_implicit
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (#i: mixed_list t)
  (#l: list u)
  (#l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (mixed_list_match_n vmatch p off n pm i l **
     mixed_list_match_n vmatch p off n pm' i l')
    (fun _ ->
      mixed_list_match_n vmatch p off n (pm +. pm') i l **
      pure (l == l'))
= mixed_list_match_n_gather_bound #t #u vmatch #k p off n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')

let mixed_list_match_share
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
  (vmatch_share: share_t vmatch)
: stt_ghost unit emp_inames
    (mixed_list_match vmatch p pm i l)
    (fun _ ->
      mixed_list_match vmatch p (pm /. 2.0R) i l **
      mixed_list_match vmatch p (pm /. 2.0R) i l)
= mixed_list_match_n_share #t #u vmatch #k p 0 (SZ.v (mixed_list_length i)) pm i l vmatch_share

let mixed_list_match_gather_bound
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
: stt_ghost unit emp_inames
    (mixed_list_match vmatch p pm i l **
     mixed_list_match vmatch p pm' i l')
    (fun _ ->
      mixed_list_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= mixed_list_match_n_gather_bound #t #u vmatch #k p 0 (SZ.v (mixed_list_length i)) pm pm' i l l' vmatch_gather

let mixed_list_match_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (mixed_list_match vmatch p pm i l **
     mixed_list_match vmatch p pm' i l')
    (fun _ ->
      mixed_list_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= mixed_list_match_n_gather #t #u vmatch #k p 0 (SZ.v (mixed_list_length i)) pm pm' i l l' vmatch_gather

// Monotonicity (weaken) for match predicates:
// Given a ghost fn turning vmatch1 into vmatch2 for all y in l,
// transform the match predicate from vmatch1 to vmatch2.

```pulse
ghost
fn rec seq_list_match_weaken_memP
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match1: (t -> (v': t' { v' << v }) -> slprop))
  (item_match2: (t -> (v': t' { v' << v }) -> slprop))
  (prf: (
    (c': t) ->
    (v': t' { v' << v /\ List.Tot.memP v' v }) ->
    stt_ghost unit emp_inames
      (item_match1 c' v')
      (fun _ -> item_match2 c' v')
  ))
requires
    (SM.seq_list_match c v item_match1)
ensures
    (SM.seq_list_match c v item_match2)
  decreases v
{
  if Nil? v {
    SM.seq_list_match_nil_elim c v item_match1;
    SM.seq_list_match_nil_intro c v item_match2;
  } else {
    SM.list_cons_precedes (List.Tot.hd v) (List.Tot.tl v);
    let _ : squash (List.Tot.tl v << v) = ();
    SM.seq_list_match_cons_elim c v item_match1;
    prf (Seq.head c) (List.Tot.hd v);
    ghost fn prf'
      (c': t)
      (v': t' { v' << List.Tot.tl v /\ List.Tot.memP v' (List.Tot.tl v) })
    requires
      item_match1 c' v'
    ensures
      item_match2 c' v'
    {
      prf c' v'
    };
    seq_list_match_weaken_memP (Seq.tail c) (List.Tot.tl v) item_match1 item_match2 prf';
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match2;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd v :: List.Tot.tl v) item_match2)
         as (SM.seq_list_match c v item_match2);
  }
}
```

```pulse
ghost
fn base_mixed_list_match_n_weaken_singleton_pos
  (#t: Type0)
  (#u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 pm0 x y)
  ))
  (_: squash (n <> 0))
requires
    (base_mixed_list_match_n vmatch1 p off n pm (Singleton sp sv s) l)
ensures
    (base_mixed_list_match_n vmatch2 p off n pm (Singleton sp sv s) l)
{
  base_mixed_list_match_n_singleton_unfold_pos vmatch1 p off n pm sp sv s l ();
  with x y . assert (pts_to s #(pm *. sp) x ** vmatch1 (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1));
  drop_ (pure (l == [y] /\ off == 0 /\ n == 1));
  prf x (pm *. sv) y;
  Pulse.Lib.Core.intro_pure (l == [y] /\ off == 0 /\ n == 1) ();
  base_mixed_list_match_n_singleton_fold_pos vmatch2 p off n pm sp sv s l ()
}
```

let base_mixed_list_match_n_weaken_singleton
  (#t: Type0)
  (#u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 pm0 x y)
  ))
: stt_ghost unit emp_inames
    (base_mixed_list_match_n vmatch1 p off n pm (Singleton sp sv s) l)
    (fun _ -> base_mixed_list_match_n vmatch2 p off n pm (Singleton sp sv s) l)
= if n = 0
  then begin
    base_mixed_list_match_n_singleton_0 vmatch1 p off pm sp sv s l;
    base_mixed_list_match_n_singleton_0 vmatch2 p off pm sp sv s l;
    slprop_rw
      (base_mixed_list_match_n vmatch1 p off n pm (Singleton sp sv s) l)
      (base_mixed_list_match_n vmatch2 p off n pm (Singleton sp sv s) l)
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
  end
  else
    base_mixed_list_match_n_weaken_singleton_pos vmatch1 vmatch2 p off n pm sp sv s l prf ()

```pulse
ghost
fn base_mixed_list_match_n_weaken
  (#t: Type0)
  (#u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 pm0 x y)
  ))
requires
    (base_mixed_list_match_n vmatch1 p off n pm i l)
ensures
    (base_mixed_list_match_n vmatch2 p off n pm i l)
{
  match i {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch1 p off n pm (Empty #t) l);
      fold (base_mixed_list_match_n vmatch2 p off n pm (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_mixed_list_match_n_weaken_singleton vmatch1 vmatch2 p off n pm sp sv s l prf;
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_mixed_list_match_n vmatch1 p off n pm (Slice #t sp sv s) l);
      with l' l1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match l1 l (vmatch1 (pm *. sv)));
      ghost fn prf'
        (c': t)
        (v': u { v' << l /\ List.Tot.memP v' l })
      requires vmatch1 (pm *. sv) c' v'
      ensures vmatch2 (pm *. sv) c' v'
      {
        prf c' (pm *. sv) v'
      };
      seq_list_match_weaken_memP l1 l (vmatch1 (pm *. sv)) (vmatch2 (pm *. sv)) prf';
      fold (base_mixed_list_match_n vmatch2 p off n pm (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch1 p off n pm (Serialized #t sp count pl) l);
      fold (base_mixed_list_match_n vmatch2 p off n pm (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

let base_mixed_list_match_weaken
  (#t: Type0) (#u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 pm0 x y)
  ))
: stt_ghost unit emp_inames
    (base_mixed_list_match vmatch1 p pm i l)
    (fun _ -> base_mixed_list_match vmatch2 p pm i l)
= base_mixed_list_match_n_weaken vmatch1 vmatch2 p 0 (SZ.v (base_mixed_list_length i)) pm i l prf

#push-options "--z3rlimit 40"

```pulse
ghost
fn rec mixed_list_match_n_weaken
  (#t: Type0)
  (#u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 pm0 x y)
  ))
requires
    (mixed_list_match_n vmatch1 p off n pm i l)
ensures
    (mixed_list_match_n vmatch2 p off n pm i l)
decreases (mixed_list_depth i)
{
  match i {
    Base bi -> {
      unfold (mixed_list_match_n vmatch1 p off n pm (Base #t bi) l);
      base_mixed_list_match_n_weaken vmatch1 vmatch2 p off n pm bi l prf;
      fold (mixed_list_match_n vmatch2 p off n pm (Base #t bi) l);
      rewrite each (Base #t bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (mixed_list_match_n vmatch1 p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        mixed_list_match_n vmatch1 p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        mixed_list_match_n vmatch1 p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2
      );
      List.Tot.Properties.append_memP_forall l1 l2;
      ghost fn prf1
        (x: t) (pm0: perm) (y: u { List.Tot.memP y l1 })
      requires vmatch1 pm0 x y
      ensures vmatch2 pm0 x y
      {
        prf x pm0 y
      };
      ghost fn prf2
        (x: t) (pm0: perm) (y: u { List.Tot.memP y l2 })
      requires vmatch1 pm0 x y
      ensures vmatch2 pm0 x y
      {
        prf x pm0 y
      };
      mixed_list_match_n_weaken vmatch1 vmatch2 p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 prf1;
      mixed_list_match_n_weaken vmatch1 vmatch2 p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 prf2;
      fold (mixed_list_match_n vmatch2 p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

#pop-options

let mixed_list_match_weaken
  (#t: Type0) (#u: Type0)
  (vmatch1 vmatch2: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
  (prf: (
    (x: t) -> (pm0: perm) -> (y: u { List.Tot.memP y l }) ->
    stt_ghost unit emp_inames
      (vmatch1 pm0 x y)
      (fun _ -> vmatch2 pm0 x y)
  ))
: stt_ghost unit emp_inames
    (mixed_list_match vmatch1 p pm i l)
    (fun _ -> mixed_list_match vmatch2 p pm i l)
= mixed_list_match_n_weaken vmatch1 vmatch2 p 0 (SZ.v (mixed_list_length i)) pm i l prf

```pulse
ghost
fn base_mixed_list_match_n_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
requires
  base_mixed_list_match_n vmatch p off n pm i l
ensures
  base_mixed_list_match_n vmatch p off n pm i l **
  pure (List.Tot.length l == n)
{
  match i {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Empty #t) l);
      fold (base_mixed_list_match_n vmatch p off n pm (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      if (n = 0) {
        base_mixed_list_match_n_singleton_unfold_0 vmatch p off n pm sp sv s l ();
        base_mixed_list_match_n_singleton_fold_0 vmatch p off n pm sp sv s l ();
        rewrite each (Singleton #t sp sv s) as i;
      } else {
        base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
        base_mixed_list_match_n_singleton_fold_pos vmatch p off n pm sp sv s l ();
        rewrite each (Singleton #t sp sv s) as i;
      }
    }
    Slice sp sv s -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      with l' l1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      SM.seq_list_match_length (vmatch (pm *. sv)) l1 l;
      fold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      with l_all . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      // l == snd (splitAt off l_all) and List.Tot.length l_all == off + n
      // so List.Tot.length l == n
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      with v' . assert (S.pts_to pl #(pm *. sp) v');
      List.Tot.Base.lemma_splitAt_snd_length off l_all;
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      fold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

```pulse
ghost
fn rec mixed_list_match_n_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
requires
  mixed_list_match_n vmatch p off n pm i l
ensures
  mixed_list_match_n vmatch p off n pm i l **
  pure (List.Tot.length l == n)
decreases (mixed_list_depth i)
{
  match i {
    Base bi -> {
      unfold (mixed_list_match_n vmatch p off n pm (Base bi) l);
      base_mixed_list_match_n_length vmatch p off n pm bi l;
      fold (mixed_list_match_n vmatch p off n pm (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
          SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
          List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
          l == List.Tot.append l1 l2 /\
          mixed_list_depth i_before < Ghost.reveal depth /\
          mixed_list_depth i_after < Ghost.reveal depth
        )
      );
      List.Tot.Properties.append_length l1 l2;
      fold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

let base_mixed_list_match_length
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
: stt_ghost unit emp_inames
    (base_mixed_list_match vmatch p pm i l)
    (fun _ ->
      base_mixed_list_match vmatch p pm i l **
      pure (List.Tot.length l == SZ.v (base_mixed_list_length i)))
= base_mixed_list_match_n_length vmatch p 0 (SZ.v (base_mixed_list_length i)) pm i l

let mixed_list_match_length
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
: stt_ghost unit emp_inames
    (mixed_list_match vmatch p pm i l)
    (fun _ ->
      mixed_list_match vmatch p pm i l **
      pure (List.Tot.length l == SZ.v (mixed_list_length i)))
= mixed_list_match_n_length vmatch p 0 (SZ.v (mixed_list_length i)) pm i l

let base_mixed_list_match_share
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
  (vmatch_share: share_t vmatch)
: stt_ghost unit emp_inames
    (base_mixed_list_match vmatch p pm i l)
    (fun _ ->
      base_mixed_list_match vmatch p (pm /. 2.0R) i l **
      base_mixed_list_match vmatch p (pm /. 2.0R) i l)
= base_mixed_list_match_n_share #t #u vmatch #k p 0 (SZ.v (base_mixed_list_length i)) pm i l vmatch_share

let base_mixed_list_match_gather_bound
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: base_mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
: stt_ghost unit emp_inames
    (base_mixed_list_match vmatch p pm i l **
     base_mixed_list_match vmatch p pm' i l')
    (fun _ ->
      base_mixed_list_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= base_mixed_list_match_n_gather_bound #t #u vmatch #k p 0 (SZ.v (base_mixed_list_length i)) pm pm' i l l' vmatch_gather

let base_mixed_list_match_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: base_mixed_list t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_mixed_list_match vmatch p pm i l **
     base_mixed_list_match vmatch p pm' i l')
    (fun _ ->
      base_mixed_list_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= base_mixed_list_match_n_gather #t #u vmatch #k p 0 (SZ.v (base_mixed_list_length i)) pm pm' i l l' vmatch_gather

```pulse
ghost
fn pts_to_parsed_strong_prefix_share
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: S.slice byte)
  (#pm: perm)
  (#v: t)
requires
  pts_to_parsed_strong_prefix p input #pm v
ensures
  pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v **
  pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v
{
  unfold (pts_to_parsed_strong_prefix p input #pm v);
  with v' . assert (S.pts_to input #pm v');
  S.share input;
  rewrite (S.pts_to input #(pm /. 2.0R) v') as (S.pts_to input #(pm /. 2.0R) v');
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
}
```

```pulse
ghost
fn pts_to_parsed_strong_prefix_gather
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: S.slice byte)
  (#pm: perm) (#v: t)
  (#pm': perm) (#v': t)
requires
  pts_to_parsed_strong_prefix p input #pm v **
  pts_to_parsed_strong_prefix p input #pm' v'
ensures
  pts_to_parsed_strong_prefix p input #(pm +. pm') v **
  pure (v == v')
{
  unfold (pts_to_parsed_strong_prefix p input #pm v);
  unfold (pts_to_parsed_strong_prefix p input #pm' v');
  with w1 . assert (S.pts_to input #pm w1);
  with w2 . assert (S.pts_to input #pm' w2);
  S.gather input;
  rewrite each w2 as w1;
  fold (pts_to_parsed_strong_prefix p input #(pm +. pm') v);
}
```

module SMU = Pulse.Lib.SeqMatch.Util

let pts_to_parsed_strong_prefix_nlist_truncate
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (n: nat) (len: nat)
  (v': Seq.seq byte)
  (l: list t)
: Lemma
  (requires (
    len <= n /\
    List.Tot.length l == n /\
    pts_to_parsed_strong_prefix_prop (parse_nlist n p) v' l
  ))
  (ensures (
    List.Tot.length (fst (List.Tot.splitAt len l)) == len /\
    pts_to_parsed_strong_prefix_prop (parse_nlist len p) v' (fst (List.Tot.splitAt len l))
  ))
= let _ : squash (len <= List.Tot.length l) = () in
  FStar.List.Pure.Properties.splitAt_length len l;
  FStar.List.Pure.Properties.lemma_splitAt_append len l;
  let l1 = fst (List.Tot.splitAt len l) in
  let l2 = snd (List.Tot.splitAt len l) in
  assert (List.Tot.append l1 l2 == l);
  assert (List.Tot.length l1 == len);
  parse_nlist_sum p len (n - len) v';
  assert (len + (n - len) == n);
  match parse (parse_nlist len p) v' with
  | Some (l1', consumed1) ->
    begin match parse (parse_nlist (n - len) p) (Seq.slice v' consumed1 (Seq.length v')) with
    | Some (l2', consumed2) ->
      List.Tot.Properties.append_length l1' l2';
      FStar.List.Pure.Properties.lemma_append_splitAt l1' l2';
      assert (List.Tot.splitAt len l == (l1', l2'));
      assert (l1 == l1');
      ()
    | None -> ()
    end
  | None -> ()

// Helper: splitAt of the composed splitAt
let list_narrow_spec
  (#a: Type) (l: list a) (left: nat) (right: nat)
: Lemma
  (requires left <= right /\ right <= List.Tot.length l)
  (ensures (
    List.Tot.length (fst (List.Tot.splitAt right l)) == right /\
    List.Tot.length (snd (List.Tot.splitAt left (fst (List.Tot.splitAt right l)))) == right - left
  ))
= FStar.List.Pure.Properties.splitAt_length right l;
  FStar.List.Pure.Properties.splitAt_length left (fst (List.Tot.splitAt right l))

let rec splitAt_narrow (#a: Type) (l_all: list a) (off off' n': nat)
: Lemma
  (requires off <= off' /\ off' + n' <= List.Tot.length l_all)
  (ensures
    snd (List.Tot.splitAt off' (fst (List.Tot.splitAt (off' + n') l_all)))
    == fst (List.Tot.splitAt n' (snd (List.Tot.splitAt (off' - off) (snd (List.Tot.splitAt off l_all))))))
  (decreases l_all)
= if off' = 0 then ()
  else match l_all with
    | [] -> ()
    | _ :: tl ->
      if off = 0 then splitAt_narrow tl 0 (off' - 1) n'
      else splitAt_narrow tl (off - 1) (off' - 1) n'

let list_narrow (#a: Type) (l: list a) (skip: int) (n': int) : list a =
  if skip < 0 || n' < 0 then []
  else fst (List.Tot.splitAt n' (snd (List.Tot.splitAt skip l)))

let list_narrow_length (#a: Type) (l: list a) (skip take: int)
  : Lemma
    (requires skip >= 0 /\ take >= 0 /\ skip + take <= List.Tot.length l)
    (ensures List.Tot.length (list_narrow l skip take) == take)
= FStar.List.Tot.Base.lemma_splitAt_snd_length skip l;
  FStar.List.Pure.Properties.splitAt_length take (snd (FStar.List.Tot.Base.splitAt skip l))

// If the first m elements of l1 and l2 agree, then the first k elements (k <= m) also agree.
let rec list_narrow_prefix (#a: Type) (l1 l2: list a) (m k: nat)
: Lemma
  (requires k <= m /\ m <= List.Tot.length l1 /\ m <= List.Tot.length l2 /\
            list_narrow l1 0 m == list_narrow l2 0 m)
  (ensures list_narrow l1 0 k == list_narrow l2 0 k)
  (decreases k)
= if k = 0 then ()
  else match l1, l2 with
    | _ :: t1, _ :: t2 -> list_narrow_prefix t1 t2 (m - 1) (k - 1)
    | _, _ -> ()

#push-options "--z3rlimit 80"

```pulse
ghost
fn base_mixed_list_match_n_narrow
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n off' n': nat)
  (pm: perm)
  (i: base_mixed_list t)
  (l: list u)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
requires
  base_mixed_list_match_n vmatch p off n pm i l **
  pure (off <= off' /\ off' + n' <= off + n)
ensures
  base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n') **
  trade (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n'))
        (base_mixed_list_match_n vmatch p off n pm i l)
{
  base_mixed_list_match_n_share vmatch p off n pm i l vmatch_share;
  match i {
    Empty -> {
      // n = 0, off = 0, so off' = 0, n' = 0
      unfold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
      fold (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Empty #t) (list_narrow l (off' - off) n'));
      intro (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Empty #t) (list_narrow l (off' - off) n') @==>
             base_mixed_list_match_n vmatch p off n pm (Empty #t) l)
        #(base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l)
        fn _ {
          unfold (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Empty #t) (list_narrow l (off' - off) n'));
          drop_ (pure (Nil? (list_narrow l (off' - off) n') /\ n' == 0 /\ off' == 0));
          fold (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
          base_mixed_list_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Empty #t) l l vmatch_gather;
          drop_ (pure (l == l));
          rewrite (base_mixed_list_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Empty #t) l)
            as (base_mixed_list_match_n vmatch p off n pm (Empty #t) l);
        };
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      if (off' = off && n' = n) {
        // No change in window — just return one copy
        base_mixed_list_match_n_length vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l;
        FStar.List.Pure.Properties.splitAt_length_total l;
        assert (pure (list_narrow l (off' - off) n' == l));
        rewrite (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l)
          as (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n'));
        intro (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n') @==>
               base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) l)
          #(base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l **
            pure (List.Tot.length l == n))
          fn _ {
            FStar.List.Pure.Properties.splitAt_length_total l;
            rewrite (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n'))
              as (base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l);
            drop_ (pure (List.Tot.length l == n));
            base_mixed_list_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Singleton #t sp sv s) l l vmatch_gather;
            drop_ (pure (l == l));
            rewrite (base_mixed_list_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Singleton #t sp sv s) l)
              as (base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) l);
          };
        rewrite each (Singleton #t sp sv s) as i;
      } else {
        // Shrinking a Singleton. Since off + n <= 1, either n=0 or (off=0,n=1).
        // If n=0: n'=0, off'=off=0 — handled by first branch (off'=off, n'=n).
        // So n=1, off=0. And (off',n') != (0,1), with off'<=0+1=1 and off'+n'<=1.
        // So n' = 0 (and off' = 0 or 1).
        base_mixed_list_match_n_singleton_unfold_pos vmatch p off n (pm /. 2.0R) sp sv s l ();
        with x y. assert (pts_to s #((pm /. 2.0R) *. sp) x ** vmatch ((pm /. 2.0R) *. sv) x y **
                          pure (l == [y] /\ off == 0 /\ n == 1));
        dup_pure (l == [y] /\ off == 0 /\ n == 1);
        base_mixed_list_match_n_singleton_fold_pos vmatch p off n (pm /. 2.0R) sp sv s l ();
        // n' must be 0
        replace_second_pure (off <= off' /\ off' + n' <= off + n) (l == [y] /\ off == 0 /\ n == 1) (Nil? (list_narrow l (off' - off) n') /\ n' == 0 /\ off' <= 1) ();
        drop_ (pure (off <= off' /\ off' + n' <= off + n));
        base_mixed_list_match_n_singleton_fold_0 vmatch p off' n' (pm /. 2.0R) sp sv s (list_narrow l (off' - off) n') ();
        intro (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n') @==>
               base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) l)
          #(base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l **
            base_mixed_list_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l)
          fn _ {
            drop_ (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n'));
            base_mixed_list_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Singleton #t sp sv s) l l vmatch_gather;
            drop_ (pure (l == l));
            rewrite (base_mixed_list_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Singleton #t sp sv s) l)
              as (base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) l);
          };
        rewrite each (Singleton #t sp sv s) as i;
      }
    }
    Slice sp sv s -> {
      // Gather two shared copies back to full perm
      base_mixed_list_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Slice #t sp sv s) l l vmatch_gather;
      drop_ (pure (l == l));
      rewrite (base_mixed_list_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Slice #t sp sv s) l)
        as (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      // Unfold at full perm
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      with sl sl1 . assert (pts_to s #(pm *. sp) sl ** SM.seq_list_match sl1 l (vmatch (pm *. sv)));
      // Share pts_to
      S.share s;
      rewrite (pts_to s #((pm *. sp) /. 2.0R) sl) as (pts_to s #((pm /. 2.0R) *. sp) sl);
      rewrite (pts_to s #((pm *. sp) /. 2.0R) sl) as (pts_to s #((pm /. 2.0R) *. sp) sl);
      // Share seq_list_match
      ghost fn share_prf
        (c': t) (v': u { v' << l })
      requires vmatch (pm *. sv) c' v'
      ensures vmatch ((pm /. 2.0R) *. sv) c' v' ** vmatch ((pm /. 2.0R) *. sv) c' v'
      {
        vmatch_share c' #(pm *. sv) #v';
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
      };
      seq_list_match_share sl1 l (vmatch (pm *. sv)) (vmatch ((pm /. 2.0R) *. sv)) share_prf;
      // Split one copy into prefix + rest
      let skip : Ghost.erased nat = off' - off;
      SM.seq_list_match_length (vmatch ((pm /. 2.0R) *. sv)) sl1 l;
      drop_ (pure (Seq.length (reveal sl1) == List.Tot.length l));
      let prefix_seq : Ghost.erased (Seq.seq t) = Seq.slice (reveal sl1) 0 (reveal skip);
      let rest_seq : Ghost.erased (Seq.seq t) = Seq.slice (reveal sl1) (reveal skip) n;
      let prefix_l : Ghost.erased (list u) = fst (List.Tot.splitAt (reveal skip) l);
      let rest_l : Ghost.erased (list u) = snd (List.Tot.splitAt (reveal skip) l);
      FStar.List.Pure.Properties.splitAt_length (reveal skip) l;
      FStar.List.Pure.Properties.lemma_splitAt_append (reveal skip) l;
      Seq.lemma_eq_intro (reveal sl1) (Seq.append (reveal prefix_seq) (reveal rest_seq));
      rewrite (SM.seq_list_match sl1 l (vmatch ((pm /. 2.0R) *. sv)))
        as (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal rest_seq)) (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch ((pm /. 2.0R) *. sv)));
      assert (pure (Seq.length (reveal prefix_seq) == List.Tot.length (reveal prefix_l)));
      SMU.seq_list_match_append_elim_trade (vmatch ((pm /. 2.0R) *. sv)) (reveal prefix_seq) (reveal prefix_l) (reveal rest_seq) (reveal rest_l);
      drop_ (pure (Seq.length (reveal prefix_seq) == List.Tot.length (reveal prefix_l) /\
                   Seq.length (reveal rest_seq) == List.Tot.length (reveal rest_l)));
      // Split rest into middle + suffix
      let middle_seq : Ghost.erased (Seq.seq t) = Seq.slice (reveal rest_seq) 0 n';
      let suffix_seq : Ghost.erased (Seq.seq t) = Seq.slice (reveal rest_seq) n' (n - reveal skip);
      let middle_l : Ghost.erased (list u) = fst (List.Tot.splitAt n' (reveal rest_l));
      let suffix_l : Ghost.erased (list u) = snd (List.Tot.splitAt n' (reveal rest_l));
      FStar.List.Pure.Properties.splitAt_length n' (reveal rest_l);
      FStar.List.Pure.Properties.lemma_splitAt_append n' (reveal rest_l);
      Seq.lemma_eq_intro (reveal rest_seq) (Seq.append (reveal middle_seq) (reveal suffix_seq));
      rewrite (SM.seq_list_match (reveal rest_seq) (reveal rest_l) (vmatch ((pm /. 2.0R) *. sv)))
        as (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq)) (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv)));
      assert (pure (Seq.length (reveal middle_seq) == List.Tot.length (reveal middle_l)));
      SMU.seq_list_match_append_elim_trade (vmatch ((pm /. 2.0R) *. sv)) (reveal middle_seq) (reveal middle_l) (reveal suffix_seq) (reveal suffix_l);
      drop_ (pure (Seq.length (reveal middle_seq) == List.Tot.length (reveal middle_l) /\
                   Seq.length (reveal suffix_seq) == List.Tot.length (reveal suffix_l)));
      // middle_l is our narrow list
      // Rewrite middle_seq for the fold
      Seq.lemma_eq_intro (reveal middle_seq) (Seq.slice (reveal sl) off' (off' + n'));
      rewrite (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch ((pm /. 2.0R) *. sv)))
        as (SM.seq_list_match (Seq.slice (reveal sl) off' (off' + n')) (list_narrow l (off' - off) n') (vmatch ((pm /. 2.0R) *. sv)));
      // Fold narrow view
      assert (pure (off' + n' <= Seq.length (reveal sl)));
      fold (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Slice #t sp sv s) (list_narrow l (off' - off) n'));
      // Build trade
      intro (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Slice #t sp sv s) (list_narrow l (off' - off) n') @==>
             base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l)
        #(pts_to s #((pm /. 2.0R) *. sp) sl **
          SM.seq_list_match sl1 l (vmatch ((pm /. 2.0R) *. sv)) **
          SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)) **
          SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch ((pm /. 2.0R) *. sv)) **
          trade (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch ((pm /. 2.0R) *. sv)) **
                 SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch ((pm /. 2.0R) *. sv)))
                (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq)) (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv))) **
          trade (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)) **
                 SM.seq_list_match (reveal rest_seq) (reveal rest_l) (vmatch ((pm /. 2.0R) *. sv)))
                (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal rest_seq)) (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch ((pm /. 2.0R) *. sv))) **
          pure (off + n <= Seq.length (reveal sl) /\ reveal sl1 == Seq.slice (reveal sl) off (off + n)))
        fn _ {
          // Unfold trigger
          unfold (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Slice #t sp sv s) (list_narrow l (off' - off) n'));
          with sl1_2 . assert (SM.seq_list_match sl1_2 (list_narrow l (off' - off) n') (vmatch ((pm /. 2.0R) *. sv)));
          // Gather pts_to
          S.gather s;
          with sl2 . assert (pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) sl2);
          rewrite (pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) sl2)
            as (pts_to s #(pm *. sp) sl2);
          // Rewrite middle to match the stored trade
          rewrite (SM.seq_list_match sl1_2 (list_narrow l (off' - off) n') (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch ((pm /. 2.0R) *. sv)));
          // Reassemble middle + suffix
          elim_trade
            (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch ((pm /. 2.0R) *. sv)) **
             SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch ((pm /. 2.0R) *. sv)))
            (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq)) (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv)));
          // Reassemble prefix + (middle++suffix) using outer trade
          // The trade stores (prefix ** (append middle suffix)) -> (append prefix rest)
          // But the trade was captured with rest_seq in the RHS, so we need rest = append middle suffix
          Seq.lemma_eq_intro (Seq.append (reveal middle_seq) (reveal suffix_seq)) (reveal rest_seq);
          FStar.List.Pure.Properties.lemma_splitAt_append n' (reveal rest_l);
          // Rewrite the second part to match the outer trade's LHS (which uses Seq.append middle suffix)
          // Actually, the outer trade's LHS uses rest_seq directly, so let's rewrite first
          rewrite (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq)) (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (reveal rest_seq) (reveal rest_l) (vmatch ((pm /. 2.0R) *. sv)));
          elim_trade
            (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)) **
             SM.seq_list_match (reveal rest_seq) (reveal rest_l) (vmatch ((pm /. 2.0R) *. sv)))
            (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal rest_seq)) (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch ((pm /. 2.0R) *. sv)));
          // Rewrite back to sl1, l
          Seq.lemma_eq_intro (Seq.append (reveal prefix_seq) (reveal rest_seq)) (reveal sl1);
          FStar.List.Pure.Properties.lemma_splitAt_append (reveal skip) l;
          rewrite (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal rest_seq)) (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match sl1 l (vmatch ((pm /. 2.0R) *. sv)));
          // Gather seq_list_match copies
          ghost fn gather_prf
            (c': t) (v1': u { v1' << l }) (v2': u { v2' << l /\ List.Tot.memP v2' l })
          requires vmatch ((pm /. 2.0R) *. sv) c' v1' ** vmatch ((pm /. 2.0R) *. sv) c' v2'
          ensures vmatch (pm *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
          {
            vmatch_gather c' #((pm /. 2.0R) *. sv) #v1' #((pm /. 2.0R) *. sv) #v2';
            rewrite (vmatch ((pm /. 2.0R) *. sv +. (pm /. 2.0R) *. sv) c' v1') as (vmatch (pm *. sv) c' v1');
          };
          seq_list_match_gather_memP sl1 l l (vmatch ((pm /. 2.0R) *. sv)) (vmatch ((pm /. 2.0R) *. sv)) (vmatch (pm *. sv)) gather_prf;
          drop_ (pure (l == l));
          drop_ (pure (off + n <= Seq.length (reveal sl) /\ reveal sl1 == Seq.slice (reveal sl) off (off + n)));
          // Fold at full perm
          rewrite (pts_to s #(pm *. sp) sl2) as (pts_to s #(pm *. sp) sl);
          fold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
        };
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      // Gather two shared copies back to full perm
      base_mixed_list_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Serialized #t sp count pl) l l vmatch_gather;
      drop_ (pure (l == l));
      rewrite (base_mixed_list_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Serialized #t sp count pl) l)
        as (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      // Unfold at full perm
      unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      with l_all. assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      with v'. assert (S.pts_to pl #(pm *. sp) v');
      // Truncate nlist to off' + n'
      pts_to_parsed_strong_prefix_nlist_truncate p (off + n) (off' + n') (reveal v') l_all;
      // Share S.pts_to
      S.share pl;
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      // Fold the narrow view
      let l_all' : Ghost.erased (list u) = fst (List.Tot.splitAt (off' + n') l_all);
      // Prove the narrow list relationship
      splitAt_narrow l_all off off' n';
      // narrow list: snd(splitAt off' l_all') = fst(splitAt n' (snd(splitAt (off'-off) l)))
      fold (pts_to_parsed_strong_prefix (parse_nlist (off' + n') p) pl #((pm /. 2.0R) *. sp) (reveal l_all'));
      assert (pure (snd (List.Tot.splitAt off' (reveal l_all')) == list_narrow l (off' - off) n'));
      fold (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (snd (List.Tot.splitAt off' (reveal l_all'))));
      rewrite (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (snd (List.Tot.splitAt off' (reveal l_all'))))
        as (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (list_narrow l (off' - off) n'));
      // Build trade
      intro (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (list_narrow l (off' - off) n') @==>
             base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l)
        #(S.pts_to pl #((pm /. 2.0R) *. sp) v' **
          pure (pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) (reveal v') l_all /\
                l == snd (List.Tot.splitAt off l_all) /\ off + n <= SZ.v count))
        fn _ {
          unfold (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (list_narrow l (off' - off) n'));
          with lv2. assert (pts_to_parsed_strong_prefix (parse_nlist (off' + n') p) pl #((pm /. 2.0R) *. sp) lv2);
          unfold (pts_to_parsed_strong_prefix (parse_nlist (off' + n') p) pl #((pm /. 2.0R) *. sp) lv2);
          S.gather pl;
          with v'2. assert (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2);
          rewrite (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2)
            as (S.pts_to pl #(pm *. sp) v'2);
          rewrite (S.pts_to pl #(pm *. sp) v'2) as (S.pts_to pl #(pm *. sp) v');
          fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
          fold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
        };
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options

let rec splitAt_append_left (#a: Type) (n: nat) (l1 l2: list a)
  : Lemma
    (requires n <= List.Tot.length l1)
    (ensures (
      fst (List.Tot.splitAt n (List.Tot.append l1 l2)) == fst (List.Tot.splitAt n l1) /\
      snd (List.Tot.splitAt n (List.Tot.append l1 l2)) == List.Tot.append (snd (List.Tot.splitAt n l1)) l2
    ))
    (decreases n)
= if n = 0 then ()
  else match l1 with
    | _ :: tl -> splitAt_append_left (n - 1) tl l2

let rec list_narrow_append (#a: Type) (l1 l2: list a) (skip n': int)
: Lemma
  (requires skip >= 0 /\ n' >= 0 /\ List.Tot.length l1 + List.Tot.length l2 >= skip + n')
  (ensures (
    let len1 = List.Tot.length l1 in
    let n1' = if skip >= len1 then 0 else if n' <= len1 - skip then n' else len1 - skip in
    let na' = n' - n1' in
    let skip1 = if skip >= len1 then len1 else skip in
    let skip2 = if skip >= len1 then skip - len1 else 0 in
    list_narrow (l1 @ l2) skip n' == list_narrow l1 skip1 n1' @ list_narrow l2 skip2 na'
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl ->
    if skip > 0 then list_narrow_append tl l2 (skip - 1) n'
    else if n' = 0 then ()
    else list_narrow_append tl l2 0 (n' - 1)

// Narrow preserves well-definedness of child offsets
let append_narrow_before_ineq (off n off' n': nat) (cb: nat)
: Lemma
  (requires off <= off' /\ off' + n' <= off + n)
  (ensures (
    let off_b = append_off_before off 0 cb in
    let n1 = append_n_before off n cb in
    let off_b' = append_off_before off' 0 cb in
    let n1' = append_n_before off' n' cb in
    off_b <= off_b' /\ off_b' + n1' <= off_b + n1
  ))
= ()

let append_narrow_after_ineq (off n off' n': nat) (cb: nat)
: Lemma
  (requires off <= off' /\ off' + n' <= off + n)
  (ensures (
    let off_a = append_off_after off 0 cb in
    let na = append_n_after off n cb in
    let off_a' = append_off_after off' 0 cb in
    let na' = append_n_after off' n' cb in
    off_a <= off_a' /\ off_a' + na' <= off_a + na
  ))
= ()

// Connect list_narrow of appended list to narrows of children
let list_narrow_append_connect
  (off n off' n': nat)
  (cb ob oa: nat)
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires
    off <= off' /\ off' + n' <= off + n /\
    List.Tot.length l1 == append_n_before off n cb /\
    List.Tot.length l2 == append_n_after off n cb
  )
  (ensures (
    let skip = off' - off in
    let n1 = append_n_before off n cb in
    let na = append_n_after off n cb in
    let n1' = append_n_before off' n' cb in
    let na' = append_n_after off' n' cb in
    let skip_b = append_off_before off' ob cb - append_off_before off ob cb in
    let skip_a = append_off_after off' oa cb - append_off_after off oa cb in
    list_narrow (l1 @ l2) skip n' ==
      list_narrow l1 skip_b n1' @ list_narrow l2 skip_a na'
  ))
= list_narrow_append l1 l2 (off' - off) n'

#push-options "--z3rlimit 80"

```pulse
ghost
fn rec mixed_list_match_n_narrow
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n off' n': nat)
  (pm: perm)
  (i: mixed_list t)
  (l: list u)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
requires
  mixed_list_match_n vmatch p off n pm i l **
  pure (off <= off' /\ off' + n' <= off + n)
ensures
  mixed_list_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n') **
  trade (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n'))
        (mixed_list_match_n vmatch p off n pm i l)
decreases (mixed_list_depth i)
{
  match i {
    Base bi -> {
      unfold (mixed_list_match_n vmatch p off n pm (Base bi) l);
      base_mixed_list_match_n_narrow vmatch p off n off' n' pm bi l vmatch_share vmatch_gather;
      fold (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Base bi) (list_narrow l (off' - off) n'));
      intro (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Base bi) (list_narrow l (off' - off) n') @==>
             mixed_list_match_n vmatch p off n pm (Base bi) l)
        #(trade (base_mixed_list_match_n vmatch p off' n' (pm /. 2.0R) bi (list_narrow l (off' - off) n'))
                (base_mixed_list_match_n vmatch p off n pm bi l))
        fn _ {
          unfold (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Base bi) (list_narrow l (off' - off) n'));
          elim_trade _ _;
          fold (mixed_list_match_n vmatch p off n pm (Base bi) l);
        };
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2
      );
      // Compute child narrow parameters
      let off_b = append_off_before off (SZ.v ob) (SZ.v cb);
      let n1 = append_n_before off n (SZ.v cb);
      let off_a = append_off_after off (SZ.v oa) (SZ.v cb);
      let na = append_n_after off n (SZ.v cb);
      let off_b' = append_off_before off' (SZ.v ob) (SZ.v cb);
      let n1' = append_n_before off' n' (SZ.v cb);
      let off_a' = append_off_after off' (SZ.v oa) (SZ.v cb);
      let na' = append_n_after off' n' (SZ.v cb);
      // Rewrite context to use let-bound names
      rewrite (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1)
        as (mixed_list_match_n vmatch p off_b n1 pm i_before l1);
      rewrite (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2)
        as (mixed_list_match_n vmatch p off_a na pm i_after l2);
      // Prove narrow preconditions for children
      append_narrow_before_ineq off n off' n' (SZ.v cb);
      append_narrow_after_ineq off n off' n' (SZ.v cb);
      // Recursively narrow before child
      mixed_list_match_n_narrow vmatch p off_b n1 off_b' n1' pm i_before l1 vmatch_share vmatch_gather;
      // Share R.pts_to before
      R.share before;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      // Recursively narrow after child
      mixed_list_match_n_narrow vmatch p off_a na off_a' na' pm i_after l2 vmatch_share vmatch_gather;
      // Share R.pts_to after
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      // Rewrite narrow results from let-bound names back to append_* forms for fold
      rewrite (mixed_list_match_n vmatch p off_b' n1' (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
        as (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'));
      rewrite (mixed_list_match_n vmatch p off_a' na' (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
        as (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'));
      // Also rewrite the trades
      rewrite (trade (mixed_list_match_n vmatch p off_b' n1' (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                     (mixed_list_match_n vmatch p off_b n1 pm i_before l1))
        as (trade (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                  (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1));
      rewrite (trade (mixed_list_match_n vmatch p off_a' na' (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                     (mixed_list_match_n vmatch p off_a na pm i_after l2))
        as (trade (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                  (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2));
      // Establish list narrow relationship (pure facts from unfold are in SMT context)
      list_narrow_append_connect off n off' n' (SZ.v cb) (SZ.v ob) (SZ.v oa) l1 l2;
      list_narrow_length l1 (off_b' - off_b) n1';
      list_narrow_length l2 (off_a' - off_a) na';
      // Fold narrow view
      fold (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) (list_narrow l (off' - off) n'));
      // Build trade
      intro (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) (list_narrow l (off' - off) n') @==>
             mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l)
        #(trade (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1) **
          R.pts_to before #((pm /. 2.0R) *. bp) i_before **
          trade (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2) **
          R.pts_to after #((pm /. 2.0R) *. ap) i_after **
          pure (
            off + n <= SZ.v cb + SZ.v ca /\
            SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
            SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
            List.Tot.length l1 == n1 /\
            List.Tot.length l2 == na /\
            l == List.Tot.append l1 l2 /\
            mixed_list_depth i_before < Ghost.reveal depth /\
            mixed_list_depth i_after < Ghost.reveal depth
          ))
        fn _ {
          unfold (mixed_list_match_n vmatch p off' n' (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) (list_narrow l (off' - off) n'));
          with ib_u ia_u l1_u l2_u . assert (
            pts_to before #((pm /. 2.0R) *. bp) ib_u **
            mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_u l1_u **
            pts_to after #((pm /. 2.0R) *. ap) ia_u **
            mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_u l2_u
          );
          // Gather R.pts_to before
          R.gather before;
          drop_ (pure (reveal i_before == reveal ib_u));
          rewrite (R.pts_to before #((pm /. 2.0R) *. bp +. (pm /. 2.0R) *. bp) i_before)
            as (R.pts_to before #(pm *. bp) i_before);
          // Gather R.pts_to after
          R.gather after;
          drop_ (pure (reveal i_after == reveal ia_u));
          rewrite (R.pts_to after #((pm /. 2.0R) *. ap +. (pm /. 2.0R) *. ap) i_after)
            as (R.pts_to after #(pm *. ap) i_after);
          // Rewrite before child lists/mixed_lists to match trades
          mixed_list_match_n_length vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_u l1_u;
          list_narrow_length l1 (off_b' - off_b) n1';
          mixed_list_match_n_length vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_u l2_u;
          list_narrow_length l2 (off_a' - off_a) na';
          List.Tot.Properties.append_injective l1_u (list_narrow l1 (off_b' - off_b) n1')
            l2_u (list_narrow l2 (off_a' - off_a) na');
          with ib_x . assert (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_x l1_u);
          slprop_rw
            (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_x l1_u)
            (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
            (Pulse.Lib.Core.slprop_equiv_ext'
              (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_x l1_u)
              (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
              ());
          // Elim before trade
          elim_trade
            (mixed_list_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
            (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1);
          // Rewrite after child
          with ia_x . assert (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_x l2_u);
          slprop_rw
            (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_x l2_u)
            (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
            (Pulse.Lib.Core.slprop_equiv_ext'
              (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_x l2_u)
              (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
              ());
          // Elim after trade
          elim_trade
            (mixed_list_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
            (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2);
          // Fold original
          fold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
        };
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

#pop-options

// Helper: length of an nlist is its count
let nlist_list_length
  (#t: Type) (n: nat) (l: nlist n t)
: Lemma (List.Tot.length l == n)
= ()

// Helper: derive List.Tot.length from pts_to_parsed_strong_prefix_prop on parse_nlist.
// Note: l must already have nlist type (from pts_to_parsed_strong_prefix context).
// This is just a convenience wrapper.
let pts_to_parsed_strong_prefix_prop_nlist_length
  (#k: parser_kind) (#t: Type0)
  (p: parser k t) (n: nat) (v: Seq.seq byte) (l: nlist n t)
: Lemma
  (ensures List.Tot.length l == n)
= ()

// Lemma: narrowing a nlist parse via truncation.
// Takes nlist directly to avoid subtyping issues in Pulse.
let pts_to_parsed_strong_prefix_nlist_narrow
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (off n off' n': nat)
  (v': Seq.seq byte)
  (l_all: nlist (off + n) t)
: Lemma
  (requires (
    off <= off' /\ off' + n' <= off + n /\
    pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) v' l_all
  ))
  (ensures (
    List.Tot.length (fst (List.Tot.splitAt (off' + n') l_all)) == off' + n' /\
    pts_to_parsed_strong_prefix_prop (parse_nlist (off' + n') p) v' (fst (List.Tot.splitAt (off' + n') l_all))
  ))
= pts_to_parsed_strong_prefix_nlist_truncate p (off + n) (off' + n') v' l_all

// Lemma: connecting the narrow list from Serialized to list_narrow.
// Takes nlist directly to avoid subtyping issues in Pulse.
let serialized_narrow_list_eq
  (#t: Type)
  (off_n: nat)
  (l_all: nlist off_n t)
  (off n off' n': nat)
: Lemma
  (requires (
    off + n == off_n /\
    off <= off' /\ off' + n' <= off + n
  ))
  (ensures (
    let l = snd (List.Tot.splitAt off l_all) in
    let l_all' = fst (List.Tot.splitAt (off' + n') l_all) in
    list_narrow l (off' - off) n' == snd (List.Tot.splitAt off' l_all')
  ))
= FStar.List.Tot.Base.lemma_splitAt_snd_length off l_all;
  splitAt_narrow l_all off off' n'

// Ghost helper: unfolds pts_to_parsed_strong_prefix and returns raw components.
```pulse
ghost fn pts_to_parsed_strong_prefix_unfold
  (#k: parser_kind) (#t: Type0)
  (p: parser k t)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
requires
  pts_to_parsed_strong_prefix p input #pm v
ensures exists* (w: Seq.seq byte) .
  S.pts_to input #pm w **
  pure (pts_to_parsed_strong_prefix_prop p w (reveal v))
{
  unfold (pts_to_parsed_strong_prefix p input #pm v);
}
```

// Ghost helper: from raw S.pts_to + pure, folds into base_mixed_list_match for Serialized narrow.
// Works in ghost context where nlist subtyping can be resolved.
```pulse
ghost fn serialized_fold_narrow
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off_n: nat) (off'_n': nat)
  (sp: perm) (new_count: SZ.t)
  (input: S.slice byte)
  (pm: perm)
  (#w: Ghost.erased (Seq.seq byte))
  (l_all: Ghost.erased (list u))
  (l: Ghost.erased (list u))
  (off: nat) (n: nat)
requires
  S.pts_to input #(pm *. sp) w **
  pure (off + n == off_n /\
        off_n <= SZ.v new_count /\
        List.Tot.length (reveal l_all) == off_n /\
        reveal l == snd (List.Tot.splitAt off (reveal l_all)) /\
        off'_n' <= off_n /\
        SZ.v new_count >= off'_n' /\
        pts_to_parsed_strong_prefix_prop (parse_nlist off_n p) (reveal w) (reveal l_all))
ensures
  base_mixed_list_match_n vmatch p 0 off'_n' pm (Serialized #t sp new_count input)
    (fst (List.Tot.splitAt off'_n' (reveal l_all)))
{
  pts_to_parsed_strong_prefix_nlist_truncate p off_n off'_n' (reveal w) (reveal l_all);
  fold (pts_to_parsed_strong_prefix (parse_nlist off'_n' p) input #(pm *. sp) (fst (List.Tot.splitAt off'_n' (reveal l_all))));
  fold (base_mixed_list_match_n vmatch p 0 off'_n' pm (Serialized #t sp new_count input) (fst (List.Tot.splitAt off'_n' (reveal l_all))));
}
```

// Ghost helper: folds pts_to_parsed_strong_prefix from S.pts_to + pure, resolving nlist subtyping.
```pulse
ghost fn pts_to_parsed_strong_prefix_fold
  (#k: parser_kind) (#t: Type0)
  (p: parser k t)
  (input: S.slice byte)
  (#pm: perm)
  (#w: Ghost.erased (Seq.seq byte))
  (v: Ghost.erased t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_strong_prefix_prop p (reveal w) (reveal v))
ensures
  pts_to_parsed_strong_prefix p input #pm v
{
  fold (pts_to_parsed_strong_prefix p input #pm v);
}
```

// Lemma: given a full parse of off+n elements, a validator_success at position off' giving byte
// position pos, the suffix after pos parses as n' elements equal to list_narrow l (off'-off) n'.
#push-options "--z3rlimit 200"
let serialized_narrow_suffix_parses
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (off n off' n': nat)
  (v': Seq.seq byte)
  (l_all: nlist (off + n) t)
  (l: list t)
  (l_narrow: list t)
  (pos: nat)
: Lemma
  (requires (
    off <= off' /\ off' + n' <= off + n /\
    l == snd (List.Tot.splitAt off l_all) /\
    l_narrow == list_narrow l (off' - off) n' /\
    pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) v' l_all /\
    pos <= Seq.length v' /\
    (match parse (parse_nlist off' p) (Seq.slice v' 0 (Seq.length v')) with
     | Some (_, consumed) -> consumed == pos
     | None -> False)
  ))
  (ensures (
    List.Tot.length l_narrow == n' /\
    pts_to_parsed_strong_prefix_prop (parse_nlist n' p) (Seq.slice v' pos (Seq.length v')) l_narrow
  ))
= // Establish lengths
  FStar.List.Tot.Base.lemma_splitAt_snd_length off l_all;
  list_narrow_length l (off' - off) n';
  // Normalize Seq.slice v' 0 len == v'
  Seq.lemma_eq_intro (Seq.slice v' 0 (Seq.length v')) v';
  // Truncate parse to first off'+n' elements
  pts_to_parsed_strong_prefix_nlist_truncate p (off + n) (off' + n') v' l_all;
  let l_all' = fst (List.Tot.splitAt (off' + n') (l_all <: list t)) in
  assert (pts_to_parsed_strong_prefix_prop (parse_nlist (off' + n') p) v' l_all');
  // Decompose into off' + n' via parse_nlist_sum
  parse_nlist_sum p off' n' v';
  match parse (parse_nlist off' p) v' with
  | Some (l1, consumed1) ->
    assert (consumed1 == pos);
    let v_suff = Seq.slice v' pos (Seq.length v') in
    begin match parse (parse_nlist n' p) v_suff with
    | Some (l2, consumed2) ->
      // l1 @ l2 == l_all'
      List.Tot.Properties.append_length l1 l2;
      FStar.List.Pure.Properties.lemma_append_splitAt l1 l2;
      assert (snd (List.Tot.splitAt off' (l1 `List.Tot.append` l2)) == l2);
      // Connect list_narrow to l2
      serialized_narrow_list_eq (off + n) l_all off n off' n';
      assert (list_narrow l (off' - off) n' == snd (List.Tot.splitAt off' l_all'));
      assert (l2 == l_narrow);
      ()
    | None ->
      // Contradiction: parse_nlist (off'+n') succeeds so both sub-parses succeed
      assert False
    end
  | None ->
    // Contradiction: validator_success implies parse (parse_nlist off') succeeds
    assert False
#pop-options

#push-options "--z3rlimit 200"

// Ghost helper: fold the narrow result for Serialized case from suffix bytes.
// Takes the suffix S.pts_to + all facts from context, does all nlist reasoning internally.
```pulse
ghost fn serialized_narrow_fold_suffix
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n off' n': nat)
  (sp: perm) (new_count: SZ.t)
  (pl_suffix: S.slice byte)
  (pm: perm)
  (#v_suff: Ghost.erased (Seq.seq byte))
  (v': Ghost.erased (Seq.seq byte))
  (l_all: Ghost.erased (nlist (off + n) u))
  (l: Ghost.erased (list u))
  (l_narrow: Ghost.erased (list u))
  (pos: SZ.t)
  (sq_ctx: squash (reveal l == snd (List.Tot.splitAt off (reveal l_all))))
  (sq_bounds: squash (off <= off' /\ off' + n' <= off + n /\ SZ.v new_count == n'))
  (sq_pos: squash (SZ.v pos <= Seq.length (reveal v') /\
                   reveal v_suff == Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))))
  (sq_narrow: squash (reveal l_narrow == list_narrow (reveal l) (off' - off) n'))
  (sq_prop: squash (pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) (reveal v') (reveal l_all)))
  (sq_validator: squash (LPS.validator_success (parse_nlist off' p) 0sz (reveal v') pos == true))
requires
  S.pts_to pl_suffix #(pm *. sp) v_suff
ensures
  base_mixed_list_match_n vmatch p 0 n' pm (Serialized #t sp new_count pl_suffix) (reveal l_narrow)
{
  nlist_list_length (off + n) (reveal l_all);
  Seq.lemma_eq_intro (Seq.slice (reveal v') 0 (Seq.length (reveal v'))) (reveal v');
  serialized_narrow_suffix_parses p off n off' n' (reveal v') (reveal l_all) (reveal l) (reveal l_narrow) (SZ.v pos);
  S.pts_to_len pl_suffix;
  rewrite (S.pts_to pl_suffix #(pm *. sp) v_suff)
    as (S.pts_to pl_suffix #(pm *. sp) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))));
  fold (pts_to_parsed_strong_prefix (parse_nlist n' p) pl_suffix #(pm *. sp) (reveal l_narrow));
  fold (base_mixed_list_match_n vmatch p 0 n' pm (Serialized #t sp new_count pl_suffix) (reveal l_narrow));
}
```

#pop-options

// Trade body ghost fn for the Serialized case of base_mixed_list_narrow_n.
// Uses S.gather to recover byte identity after fold/unfold (S.share/S.gather pattern).
// The narrow match uses sp/.2, keeping one half in the frame for gather.
#push-options "--z3rlimit 400"

```pulse
ghost fn serialized_narrow_trade_body
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n: Ghost.erased nat) (n': SZ.t)
  (sp: perm) (count: SZ.t)
  (pm: perm)
  (pl pl_prefix pl_suffix: S.slice byte)
  (v': Ghost.erased (Seq.seq byte))
  (l_all: Ghost.erased (nlist (off + n) u))
  (l l_narrow: Ghost.erased (list u))
  (pos: SZ.t)
  (sq_ctx: squash (reveal l == snd (List.Tot.splitAt off (reveal l_all))))
  (sq_count: squash (off + n <= SZ.v count))
  (sq_prop: squash (pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) (reveal v') (reveal l_all)))
  (sq_pos_bound: squash (SZ.v pos <= Seq.length (reveal v')))
requires
  base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) **
  S.is_split pl pl_prefix pl_suffix **
  S.pts_to pl_prefix #(pm *. sp) (Seq.slice (reveal v') 0 (SZ.v pos))
ensures
  base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l)
{
  // Unfold the narrow match to reach S.pts_to pl_suffix at half perm
  unfold (base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Serialized #t (sp /. 2.0R) n' pl_suffix))) pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
    as (base_mixed_list_match_n vmatch p 0 (SZ.v n') pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  unfold (base_mixed_list_match_n vmatch p 0 (SZ.v n') pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  with l_na. assert (pts_to_parsed_strong_prefix (parse_nlist (0 + SZ.v n') p) pl_suffix #(pm *. (sp /. 2.0R)) l_na);
  unfold (pts_to_parsed_strong_prefix (parse_nlist (0 + SZ.v n') p) pl_suffix #(pm *. (sp /. 2.0R)) l_na);
  // Rewrite frame's half perm to match: (pm*.sp)/.2 = pm*(sp/.2)
  rewrite (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))))
    as (S.pts_to pl_suffix #(pm *. (sp /. 2.0R)) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))));
  // Gather two halves — proves byte identity via pure(s0 == s1)
  S.gather pl_suffix;
  with v_g. assert (S.pts_to pl_suffix #(pm *. (sp /. 2.0R) +. pm *. (sp /. 2.0R)) v_g);
  rewrite (S.pts_to pl_suffix #(pm *. (sp /. 2.0R) +. pm *. (sp /. 2.0R)) v_g)
    as (S.pts_to pl_suffix #(pm *. sp) v_g);
  // Join prefix and suffix back to full slice
  S.join pl_prefix pl_suffix pl;
  // v_g == Seq.slice v' pos len (from gather); v_pref == Seq.slice v' 0 pos (from split)
  // Seq.lemma_split: v' == Seq.append (Seq.slice v' 0 pos) (Seq.slice v' pos len)
  nlist_list_length (off + n) (reveal l_all);
  Seq.lemma_split (reveal v') (SZ.v pos);
  rewrite (S.pts_to pl #(pm *. sp) (Seq.append (Seq.slice (reveal v') 0 (SZ.v pos)) (reveal v_g)))
    as (S.pts_to pl #(pm *. sp) (reveal v'));
  // Fold back the original
  fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) (reveal l_all));
  fold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l));
}
```

#pop-options

// Ghost fn that builds the trade for the Serialized case of base_mixed_list_narrow_n.
// Wraps `intro ... fn _ { serialized_narrow_trade_body ... }` in a ghost context
// to avoid the deep_compress error that occurs when `intro`'s closure is inside
// a concrete function with many captured variables.
#push-options "--z3rlimit 400"

```pulse
ghost fn serialized_narrow_build_trade
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n: Ghost.erased nat) (n': SZ.t)
  (sp: perm) (count: SZ.t) (pm: perm)
  (pl pl_prefix pl_suffix: S.slice byte)
  (v': Ghost.erased (Seq.seq byte))
  (l_all: Ghost.erased (nlist (off + n) u))
  (l l_narrow: Ghost.erased (list u))
  (pos: SZ.t)
  (sq_ctx: squash (reveal l == snd (List.Tot.splitAt off (reveal l_all))))
  (sq_count: squash (off + n <= SZ.v count))
  (sq_prop: squash (pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) (reveal v') (reveal l_all)))
  (sq_pos_bound: squash (SZ.v pos <= Seq.length (reveal v')))
requires
  base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) **
  S.is_split pl pl_prefix pl_suffix **
  S.pts_to pl_prefix #(pm *. sp) (Seq.slice (reveal v') 0 (SZ.v pos))
ensures
  base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  trade (base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
       (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l))
{
  intro (base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) @==>
         base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l))
    #(S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) **
      S.is_split pl pl_prefix pl_suffix **
      S.pts_to pl_prefix #(pm *. sp) (Seq.slice (reveal v') 0 (SZ.v pos)))
    fn _ {
      serialized_narrow_trade_body vmatch p off n n' sp count pm pl pl_prefix pl_suffix v' l_all l l_narrow pos
        () () () ();
    };
}
```

#pop-options

let validator_success_pos_bound
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (v: bytes) (pos: SZ.t)
: Lemma
  (requires LPS.validator_success p 0sz v pos)
  (ensures SZ.v pos <= Seq.length v)
= Seq.lemma_eq_intro (Seq.slice v 0 (Seq.length v)) v

// Named predicate bundling the pure facts from Serialized unfold.
// Uses concrete types so `fold` with explicit `reveal` matches unfold's auto-coercion.
let serialized_unfold_pure_ctx
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (off_val n_val: nat)
  (count: SZ.t)
  (v': Seq.seq byte)
  (l_all: nlist (off_val + n_val) t)
  (l: list t)
: Tot slprop
= pure (l == snd (List.Tot.splitAt off_val l_all) /\ off_val + n_val <= SZ.v count) **
  pure (pts_to_parsed_strong_prefix_prop (parse_nlist (off_val + n_val) p) v' l_all)

// Ghost fn: given post-jump/split state + pures bundled in serialized_unfold_pure_ctx,
// share suffix, fold narrow match, build trade.
// The named predicate is frame-matched from calling context (not proved by SMT).
#push-options "--z3rlimit 400 --ext no:context_pruning"

```pulse
ghost fn serialized_narrow_after_jump
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n: Ghost.erased nat) (off'_elem n'_elem: nat) (n': SZ.t)
  (sp: perm) (count: SZ.t) (pm: perm)
  (pl pl_prefix pl_suffix: S.slice byte)
  (v': Ghost.erased (Seq.seq byte))
  (l_all: Ghost.erased (nlist (off + n) u))
  (l l_narrow: Ghost.erased (list u))
  (pos: SZ.t)
  (sq_bounds: squash (off <= off'_elem /\ off'_elem + n'_elem <= off + n /\ SZ.v n' == n'_elem))
  (sq_narrow: squash (reveal l_narrow == list_narrow (reveal l) (off'_elem - off) n'_elem))
  (sq_pos_bound: squash (SZ.v pos <= Seq.length (reveal v')))
  (sq_vs: squash (LPS.validator_success (parse_nlist off'_elem p) 0sz (reveal v') pos))
requires
  S.pts_to pl_prefix #(pm *. sp) (Seq.slice (reveal v') 0 (SZ.v pos)) **
  S.pts_to pl_suffix #(pm *. sp) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) **
  S.is_split pl pl_prefix pl_suffix **
  serialized_unfold_pure_ctx p off n count v' l_all l
ensures
  base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  trade (base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
       (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l))
{
  // Unfold named predicate to recover pures
  unfold (serialized_unfold_pure_ctx p off n count v' l_all l);
  // Drop pures — facts are in VC
  drop_ (pure (reveal l == snd (List.Tot.splitAt (Ghost.reveal off) (reveal l_all)) /\ Ghost.reveal off + Ghost.reveal n <= SZ.v count));
  drop_ (pure (pts_to_parsed_strong_prefix_prop (parse_nlist (Ghost.reveal off + Ghost.reveal n) p) (reveal v') (reveal l_all)));
  // Prepare facts via pure lemmas
  nlist_list_length (Ghost.reveal off + Ghost.reveal n) (reveal l_all);
  Seq.lemma_eq_intro (Seq.slice (reveal v') 0 (Seq.length (reveal v'))) (reveal v');
  serialized_narrow_suffix_parses p (Ghost.reveal off) (Ghost.reveal n) off'_elem n'_elem (reveal v') (reveal l_all) (reveal l) (reveal l_narrow) (SZ.v pos);
  // Share pl_suffix
  S.share pl_suffix;
  rewrite (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))))
    as (S.pts_to pl_suffix #(pm *. (sp /. 2.0R)) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))));
  // Fold narrow match
  intro_pure (pts_to_parsed_strong_prefix_prop (parse_nlist n'_elem p) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) (reveal l_narrow)) ();
  fold (pts_to_parsed_strong_prefix (parse_nlist n'_elem p) pl_suffix #(pm *. (sp /. 2.0R)) (reveal l_narrow));
  intro_pure (reveal l_narrow == snd (List.Tot.splitAt 0 (reveal l_narrow)) /\ 0 + n'_elem <= SZ.v n') ();
  fold (base_mixed_list_match_n vmatch p 0 n'_elem pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  rewrite (base_mixed_list_match_n vmatch p 0 n'_elem pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
    as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Serialized #t (sp /. 2.0R) n' pl_suffix))) pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  fold (base_mixed_list_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  // Build trade
  serialized_narrow_build_trade vmatch p
    off n n'
    sp count pm pl pl_prefix pl_suffix v' l_all l l_narrow pos
    () () () ();
}
```

#pop-options

#push-options "--z3rlimit 2000 --ext no:context_pruning"

// Concrete fn for the Serialized case of base_mixed_list_narrow_n.
// Inlines all ghost fn logic — pures from unfold are SMT hypotheses for fold.
inline_for_extraction
```pulse
fn base_mixed_list_narrow_n_serialized
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (off: Ghost.erased nat) (n: Ghost.erased nat)
  (pm: perm)
  (sp: perm) (count: SZ.t) (pl: S.slice byte)
  (l: Ghost.erased (list u))
  (off': SZ.t) (n': SZ.t)
  (l_narrow: Ghost.erased (list u))
  (sq_bounds: squash (Ghost.reveal off <= SZ.v off' /\ SZ.v off' + SZ.v n' <= Ghost.reveal off + Ghost.reveal n))
  (sq_narrow: squash (reveal l_narrow == list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')))
requires
  base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l
returns i': base_mixed_list t
ensures
  base_mixed_list_match vmatch p pm i' (reveal l_narrow) **
  trade (base_mixed_list_match vmatch p pm i' (reveal l_narrow))
       (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l)) **
  pure (base_mixed_list_length i' == n')
{
  // Step 1: Unfold base_mixed_list_match_n and pts_to_parsed_strong_prefix
  unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) l);
  with l_all. assert (pts_to_parsed_strong_prefix (parse_nlist (Ghost.reveal off + Ghost.reveal n) p) pl #(pm *. sp) l_all);
  unfold (pts_to_parsed_strong_prefix (parse_nlist (Ghost.reveal off + Ghost.reveal n) p) pl #(pm *. sp) l_all);
  with v'. assert (S.pts_to pl #(pm *. sp) v');

  // Step 2: Fold named predicate IMMEDIATELY (VC is simple here, fold proves pures easily)
  fold (serialized_unfold_pure_ctx p off n count v' l_all l);

  // Step 3: Jump
  S.pts_to_len pl;
  parse_nlist_sum p (SZ.v off') (Ghost.reveal off + Ghost.reveal n - SZ.v off') (reveal v');
  intro_pure (LPS.jumper_pre' (parse_nlist (SZ.v off') p) 0sz v') ();
  let pos = LPV.jump_nlist j off' pl 0sz;

  // Step 4: Split
  let pl_p = S.split pl pos;
  match pl_p {
    pl_prefix, pl_suffix -> {

  // Step 5: Call ghost fn — named predicate is frame-matched
  drop_ (pure (Seq.length v' == SZ.v (S.len pl)));
  validator_success_pos_bound (parse_nlist (SZ.v off') p) (reveal v') pos;

  serialized_narrow_after_jump vmatch p
    off n (SZ.v off') (SZ.v n') n'
    sp count pm pl pl_prefix pl_suffix v' l_all l l_narrow pos
    () () () ();

  intro_pure (base_mixed_list_length (Serialized #t (sp /. 2.0R) n' pl_suffix) == n') ();
  let i' = Serialized #t (sp /. 2.0R) n' pl_suffix;
  rewrite each (Serialized #t (sp /. 2.0R) n' pl_suffix) as i';
  i'
  }}
}
```

inline_for_extraction
```pulse
fn base_mixed_list_narrow_n
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (off: Ghost.erased nat) (n: Ghost.erased nat)
  (pm: perm) (i: base_mixed_list t) (l: Ghost.erased (list u))
  (off': SZ.t) (n': SZ.t)
requires
  base_mixed_list_match_n vmatch p off n pm i l **
  pure (Ghost.reveal off <= SZ.v off' /\ SZ.v off' + SZ.v n' <= Ghost.reveal off + Ghost.reveal n)
returns i': base_mixed_list t
ensures
  base_mixed_list_match vmatch p pm i' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')) **
  trade (base_mixed_list_match vmatch p pm i' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')))
       (base_mixed_list_match_n vmatch p off n pm i l) **
  pure (base_mixed_list_length i' == n')
{
  let l_narrow : Ghost.erased (list u) = list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n');
  match i {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Empty #t) l);
      fold (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Empty #t))) pm (Empty #t) (reveal l_narrow));
      fold (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow));
      Trade.refl (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow));
      rewrite
        (trade (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow))
               (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow)))
        as (trade (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow))
                  (base_mixed_list_match_n vmatch p off n pm i l));
      let i' = Empty #t;
      rewrite each (Empty #t) as i';
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
    }
    Singleton sp sv s -> {
      if (n' = 0sz) {
        fold (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Empty #t))) pm (Empty #t) (reveal l_narrow));
        fold (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow));
        intro (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow) @==>
               base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) (reveal l))
          #(base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) (reveal l))
          fn _ {
            unfold (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow));
            unfold (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Empty #t))) pm (Empty #t) (reveal l_narrow));
            drop_ (pure (Nil? (reveal l_narrow) /\ SZ.v (base_mixed_list_length (Empty #t)) == 0 /\ 0 == 0));
          };
        rewrite
          (trade (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow))
                 (base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) (reveal l)))
          as (trade (base_mixed_list_match vmatch p pm (Empty #t) (reveal l_narrow))
                    (base_mixed_list_match_n vmatch p off n pm i l));
        let i' = Empty #t;
        rewrite each (Empty #t) as i';
        rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
        i'
      } else {
        base_mixed_list_match_n_singleton_unfold_pos vmatch p (Ghost.reveal off) (Ghost.reveal n) pm sp sv s l ();
        with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ Ghost.reveal off == 0 /\ Ghost.reveal n == 1));
        base_mixed_list_match_n_singleton_fold_pos vmatch p (Ghost.reveal off) (Ghost.reveal n) pm sp sv s l ();
        rewrite (base_mixed_list_match_n vmatch p off n pm (Singleton #t sp sv s) l)
          as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Singleton #t sp sv s))) pm (Singleton #t sp sv s) l);
        fold (base_mixed_list_match vmatch p pm (Singleton #t sp sv s) l);
        assert (pure (reveal l == [y]));
        FStar.List.Pure.Properties.splitAt_length_total (reveal l);
        assert (pure (reveal l_narrow == reveal l));
        Trade.rewrite_with_trade
          (base_mixed_list_match vmatch p pm (Singleton #t sp sv s) (reveal l))
          (base_mixed_list_match vmatch p pm (Singleton #t sp sv s) (reveal l_narrow));
        rewrite
          (trade (base_mixed_list_match vmatch p pm (Singleton #t sp sv s) (reveal l_narrow))
                 (base_mixed_list_match vmatch p pm (Singleton #t sp sv s) (reveal l)))
          as (trade (base_mixed_list_match vmatch p pm (Singleton #t sp sv s) (reveal l_narrow))
                    (base_mixed_list_match_n vmatch p off n pm i l));
        let i' = Singleton sp sv s;
        rewrite each (Singleton #t sp sv s) as i';
        rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
        i'
      }
    }
    Slice sp sv s -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) l);
      with l' sl1. assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match sl1 l (vmatch (pm *. sv)));
      S.pts_to_len s;
      SM.seq_list_match_length (vmatch (pm *. sv)) sl1 (reveal l);
      // Split at off' to get prefix [0..off') and rest [off'..)
      let s_pr = S.split s off';
      match s_pr {
        s_prefix, s_rest -> {
      with v_prefix. assert (pts_to s_prefix #(pm *. sp) v_prefix);
      with v_rest. assert (pts_to s_rest #(pm *. sp) v_rest);
      S.pts_to_len s_prefix;
      S.pts_to_len s_rest;
      // Split rest at n' to get middle [off'..off'+n') and suffix [off'+n'..)
      let s_ms = S.split s_rest n';
      match s_ms {
        s_middle, s_suffix -> {
      with v_middle. assert (pts_to s_middle #(pm *. sp) v_middle);
      with v_suffix. assert (pts_to s_suffix #(pm *. sp) v_suffix);
      S.pts_to_len s_middle;
      S.pts_to_len s_suffix;
      // Split the seq_list_match
      let skip : Ghost.erased nat = SZ.v off' - Ghost.reveal off;
      let prefix_seq : Ghost.erased (Seq.seq t) = Seq.slice sl1 0 (reveal skip);
      let middle_seq : Ghost.erased (Seq.seq t) = Seq.slice sl1 (reveal skip) (reveal skip + SZ.v n');
      let suffix_seq : Ghost.erased (Seq.seq t) = Seq.slice sl1 (reveal skip + SZ.v n') (Seq.length sl1);
      let prefix_l : Ghost.erased (list u) = fst (List.Tot.splitAt (reveal skip) (reveal l));
      let rest_l : Ghost.erased (list u) = snd (List.Tot.splitAt (reveal skip) (reveal l));
      let middle_l : Ghost.erased (list u) = fst (List.Tot.splitAt (SZ.v n') (reveal rest_l));
      let suffix_l : Ghost.erased (list u) = snd (List.Tot.splitAt (SZ.v n') (reveal rest_l));
      assert (pure (reveal middle_l == reveal l_narrow));
      // Split seq_list_match into prefix ++ rest
      FStar.List.Pure.Properties.lemma_splitAt_append (reveal skip) (reveal l);
      Seq.lemma_split sl1 (reveal skip);
      assert (pure (Seq.equal sl1 (Seq.append (reveal prefix_seq) (Seq.append (reveal middle_seq) (reveal suffix_seq)))));
      rewrite (SM.seq_list_match sl1 l (vmatch (pm *. sv)))
        as (SM.seq_list_match (Seq.append (reveal prefix_seq) (Seq.append (reveal middle_seq) (reveal suffix_seq)))
                              (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch (pm *. sv)));
      assert (pure (Seq.length (reveal prefix_seq) == List.Tot.length (reveal prefix_l)));
      SMU.seq_list_match_append_elim_trade (vmatch (pm *. sv)) (reveal prefix_seq) (reveal prefix_l) (Seq.append (reveal middle_seq) (reveal suffix_seq)) (reveal rest_l);
      drop_ (trade (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch (pm *. sv)) **
                     SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq)) (reveal rest_l) (vmatch (pm *. sv)))
                   (SM.seq_list_match (Seq.append (reveal prefix_seq) (Seq.append (reveal middle_seq) (reveal suffix_seq)))
                              (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch (pm *. sv))));
      // Split rest into middle ++ suffix
      FStar.List.Pure.Properties.lemma_splitAt_append (SZ.v n') (reveal rest_l);
      FStar.List.Pure.Properties.splitAt_length (SZ.v n') (reveal rest_l);
      assert (pure (Seq.length (reveal middle_seq) == List.Tot.length (reveal middle_l)));
      rewrite (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq)) (reveal rest_l) (vmatch (pm *. sv)))
        as (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq))
                              (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch (pm *. sv)));
      SMU.seq_list_match_append_elim_trade (vmatch (pm *. sv)) (reveal middle_seq) (reveal middle_l) (reveal suffix_seq) (reveal suffix_l);
      drop_ (trade (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch (pm *. sv)) **
                     SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch (pm *. sv)))
                   (SM.seq_list_match (Seq.append (reveal middle_seq) (reveal suffix_seq))
                              (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch (pm *. sv))));
      // Fold base_mixed_list_match for s_middle
      Seq.lemma_eq_intro (reveal middle_seq) (reveal v_middle);
      Seq.lemma_eq_intro (reveal middle_seq) (Seq.slice (reveal v_middle) 0 (SZ.v n'));
      rewrite (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch (pm *. sv)))
        as (SM.seq_list_match (Seq.slice (reveal v_middle) 0 (SZ.v (S.len s_middle))) (reveal l_narrow) (vmatch (pm *. sv)));
      fold (base_mixed_list_match_n vmatch p 0 (SZ.v (S.len s_middle)) pm (Slice #t sp sv s_middle) (reveal l_narrow));
      fold (base_mixed_list_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow));

      // Build the trade
      intro (base_mixed_list_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow) @==>
             base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) (reveal l))
        #(S.is_split s s_prefix s_rest **
          S.is_split s_rest s_middle s_suffix **
          pts_to s_prefix #(pm *. sp) v_prefix **
          pts_to s_suffix #(pm *. sp) v_suffix **
          SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch (pm *. sv)) **
          SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch (pm *. sv)) **
          pure (Seq.equal sl1 (Seq.append (reveal prefix_seq) (Seq.append (reveal middle_seq) (reveal suffix_seq))) /\
                reveal l == List.Tot.append (reveal prefix_l) (reveal rest_l) /\
                reveal rest_l == List.Tot.append (reveal middle_l) (reveal suffix_l) /\
                List.Tot.length (reveal prefix_l) == reveal skip /\
                List.Tot.length (reveal middle_l) == SZ.v n' /\
                Seq.length (reveal prefix_seq) == reveal skip /\
                Seq.length (reveal middle_seq) == SZ.v n' /\
                Ghost.reveal off + Ghost.reveal n <= Seq.length (reveal l') /\
                reveal sl1 == Seq.slice (reveal l') (Ghost.reveal off) (Ghost.reveal off + Ghost.reveal n) /\
                SZ.v (S.len s_prefix) == SZ.v off' /\
                Seq.length (reveal v_prefix) == SZ.v off' /\
                Seq.length (reveal v_suffix) == Seq.length (reveal l') - SZ.v off' - SZ.v n'))
        fn _ {
          unfold (base_mixed_list_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow));
          unfold (base_mixed_list_match_n vmatch p 0 (SZ.v (S.len s_middle)) pm (Slice #t sp sv s_middle) (reveal l_narrow));
          with l'2 sl1_2. assert (pts_to s_middle #(pm *. sp) l'2 ** SM.seq_list_match sl1_2 (reveal l_narrow) (vmatch (pm *. sv)));
          S.pts_to_len s_middle;
          SM.seq_list_match_length (vmatch (pm *. sv)) sl1_2 (reveal l_narrow);
          Seq.lemma_eq_intro sl1_2 (reveal l'2);
          // Recombine: middle ++ suffix
          SMU.seq_list_match_append_intro_trade (vmatch (pm *. sv)) sl1_2 (reveal middle_l) (reveal suffix_seq) (reveal suffix_l);
          drop_ (trade (SM.seq_list_match (Seq.append sl1_2 (reveal suffix_seq)) (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch (pm *. sv)))
                       (SM.seq_list_match sl1_2 (reveal middle_l) (vmatch (pm *. sv)) ** SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch (pm *. sv))));
          rewrite (SM.seq_list_match (Seq.append sl1_2 (reveal suffix_seq)) (List.Tot.append (reveal middle_l) (reveal suffix_l)) (vmatch (pm *. sv)))
            as (SM.seq_list_match (Seq.append sl1_2 (reveal suffix_seq)) (reveal rest_l) (vmatch (pm *. sv)));
          // prefix ++ rest
          SMU.seq_list_match_append_intro_trade (vmatch (pm *. sv)) (reveal prefix_seq) (reveal prefix_l) (Seq.append sl1_2 (reveal suffix_seq)) (reveal rest_l);
          drop_ (trade (SM.seq_list_match (Seq.append (reveal prefix_seq) (Seq.append sl1_2 (reveal suffix_seq))) (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch (pm *. sv)))
                       (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch (pm *. sv)) ** SM.seq_list_match (Seq.append sl1_2 (reveal suffix_seq)) (reveal rest_l) (vmatch (pm *. sv))));
          // Join s_middle + s_suffix -> s_rest
          S.join s_middle s_suffix s_rest;
          // Join s_prefix + s_rest -> s
          S.join s_prefix s_rest s;
          Seq.lemma_eq_intro (Seq.append (reveal prefix_seq) (Seq.append sl1_2 (reveal suffix_seq)))
                             (Seq.slice (Seq.append (reveal v_prefix) (Seq.append (reveal l'2) (reveal v_suffix))) (Ghost.reveal off) (Ghost.reveal off + Ghost.reveal n));
          rewrite (SM.seq_list_match (Seq.append (reveal prefix_seq) (Seq.append sl1_2 (reveal suffix_seq))) (List.Tot.append (reveal prefix_l) (reveal rest_l)) (vmatch (pm *. sv)))
            as (SM.seq_list_match (Seq.slice (Seq.append (reveal v_prefix) (Seq.append (reveal l'2) (reveal v_suffix))) (Ghost.reveal off) (Ghost.reveal off + Ghost.reveal n))
                                  (reveal l) (vmatch (pm *. sv)));
          drop_ (pure (0 + SZ.v (S.len s_middle) <= Seq.length (reveal l'2) /\ sl1_2 == Seq.slice (reveal l'2) 0 (SZ.v (S.len s_middle))));
          drop_ (pure (Seq.length (reveal l'2) == SZ.v (S.len s_middle)));
          fold (base_mixed_list_match_n vmatch p (Ghost.reveal off) (Ghost.reveal n) pm (Slice #t sp sv s) (reveal l));
        };

      rewrite
        (trade (base_mixed_list_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow))
               (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) (reveal l)))
        as (trade (base_mixed_list_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow))
                  (base_mixed_list_match_n vmatch p off n pm i l));
      let i' = Slice #t sp sv s_middle;
      rewrite each (Slice #t sp sv s_middle) as i';
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
      }}
      }}
    }
    Serialized sp count pl -> {
      let i' = base_mixed_list_narrow_n_serialized vmatch p j off n pm sp count pl l off' n' l_narrow () ();
      rewrite
        (trade (base_mixed_list_match vmatch p pm i' (reveal l_narrow))
               (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l)))
        as (trade (base_mixed_list_match vmatch p pm i' (reveal l_narrow))
                  (base_mixed_list_match_n vmatch p off n pm i l));
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
    }
  }
}
```

#pop-options

// mixed_list_narrow_n: concrete narrowing for mixed_lists.
// Returns at pm /. 2.0R because Append children are narrowed via mixed_list_match_n_narrow (which halves pm).
// Base case calls base_mixed_list_narrow_n (full pm) then shares.

// Helper: append_n_before + append_n_after = n
let append_n_sum (off n cb: nat)
: Lemma (append_n_before off n cb + append_n_after off n cb == n)
= ()

// Helper: SZ.fits for new Append offset computations
let append_off_before_fits (off ob cb: nat)
: Lemma
  (requires SZ.fits (ob + cb))
  (ensures SZ.fits (append_off_before off ob cb))
= ()

let append_off_after_fits (off oa ca cb: nat)
: Lemma
  (requires SZ.fits (oa + ca) /\ off <= cb + ca)
  (ensures SZ.fits (append_off_after off oa cb))
= ()

// SZ.t-returning helpers for Append child params (pure, no stateful conditionals)
let append_n_before_sz (off n cb: SZ.t)
: Pure SZ.t
  (requires True)
  (ensures fun r -> SZ.v r == append_n_before (SZ.v off) (SZ.v n) (SZ.v cb) /\ SZ.v r <= SZ.v n)
= if SZ.gte off cb then 0sz
  else let diff = SZ.sub cb off in
       if SZ.lte n diff then n else diff

let append_n_after_sz (off n cb: SZ.t)
: Pure SZ.t
  (requires True)
  (ensures fun r -> SZ.v r == append_n_after (SZ.v off) (SZ.v n) (SZ.v cb))
= SZ.sub n (append_n_before_sz off n cb)

let append_off_before_sz (off ob cb: SZ.t)
: Pure SZ.t
  (requires SZ.fits (SZ.v ob + SZ.v cb))
  (ensures fun r -> SZ.v r == append_off_before (SZ.v off) (SZ.v ob) (SZ.v cb))
= SZ.add ob (if SZ.gte off cb then cb else off)

let append_off_after_sz (off oa ca cb: SZ.t)
: Pure SZ.t
  (requires SZ.fits (SZ.v oa + SZ.v ca) /\ SZ.v off <= SZ.v cb + SZ.v ca)
  (ensures fun r -> SZ.v r == append_off_after (SZ.v off) (SZ.v oa) (SZ.v cb))
= SZ.add oa (if SZ.gte off cb then SZ.sub off cb else 0sz)

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"

inline_for_extraction
```pulse
fn mixed_list_narrow_n
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (off: Ghost.erased nat) (n: Ghost.erased nat)
  (pm: perm) (i: mixed_list t) (l: Ghost.erased (list u))
  (off': SZ.t) (n': SZ.t)
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
requires
  mixed_list_match_n vmatch p off n pm i l **
  pure (Ghost.reveal off <= SZ.v off' /\ SZ.v off' + SZ.v n' <= Ghost.reveal off + Ghost.reveal n)
returns i': mixed_list t
ensures
  mixed_list_match vmatch p (pm /. 2.0R) i' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')) **
  trade (mixed_list_match vmatch p (pm /. 2.0R) i' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')))
       (mixed_list_match_n vmatch p off n pm i l) **
  pure (mixed_list_length i' == n')
{
  let l_narrow : Ghost.erased (list u) = list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n');
  match i {
    Base bi -> {
      // Unfold mixed_list_match_n to get base_mixed_list_match_n
      unfold (mixed_list_match_n vmatch p off n pm (Base bi) l);
      // Call base_mixed_list_narrow_n to get a new base_mixed_list at full pm
      let bi' = base_mixed_list_narrow_n vmatch p j off n pm bi l off' n';
      // bi' has: base_mixed_list_match pm bi' (list_narrow ...) + trade + pure(base_mixed_list_length bi' == n')
      // Rewrite to use l_narrow
      rewrite (base_mixed_list_match vmatch p pm bi' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')))
        as (base_mixed_list_match vmatch p pm bi' (reveal l_narrow));
      rewrite (trade (base_mixed_list_match vmatch p pm bi' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')))
                     (base_mixed_list_match_n vmatch p off n pm bi l))
        as (trade (base_mixed_list_match vmatch p pm bi' (reveal l_narrow))
                  (base_mixed_list_match_n vmatch p off n pm bi l));
      // Share base_mixed_list_match to get two copies at pm/2
      rewrite (base_mixed_list_match vmatch p pm bi' (reveal l_narrow))
        as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) pm bi' (reveal l_narrow));
      base_mixed_list_match_n_share vmatch p 0 (SZ.v (base_mixed_list_length bi')) pm bi' (reveal l_narrow) vmatch_share;
      // Now have two copies of base_mixed_list_match_n 0 len (pm/2) bi' l_narrow
      // Fold one into mixed_list_match
      fold (mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) (Base bi') (reveal l_narrow));
      rewrite (mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) (Base bi') (reveal l_narrow))
        as (mixed_list_match vmatch p (pm /. 2.0R) (Base bi') (reveal l_narrow));
      // Build trade: mixed_list_match (pm/2) (Base bi') l_narrow @==> mixed_list_match_n off n pm i l
      intro (mixed_list_match vmatch p (pm /. 2.0R) (Base bi') (reveal l_narrow) @==>
             mixed_list_match_n vmatch p off n pm (Base bi) l)
        #(base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) bi' (reveal l_narrow) **
          trade (base_mixed_list_match vmatch p pm bi' (reveal l_narrow))
               (base_mixed_list_match_n vmatch p off n pm bi l))
        fn _ {
          // Unfold mixed_list_match
          rewrite (mixed_list_match vmatch p (pm /. 2.0R) (Base bi') (reveal l_narrow))
            as (mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) (Base bi') (reveal l_narrow));
          unfold (mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) (Base bi') (reveal l_narrow));
          // Gather to get full pm
          base_mixed_list_match_n_gather vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) (pm /. 2.0R) bi' (reveal l_narrow) (reveal l_narrow) vmatch_gather;
          drop_ (pure (reveal l_narrow == reveal l_narrow));
          rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R +. pm /. 2.0R) bi' (reveal l_narrow))
            as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) pm bi' (reveal l_narrow));
          // Fold back to base_mixed_list_match
          rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) pm bi' (reveal l_narrow))
            as (base_mixed_list_match vmatch p pm bi' (reveal l_narrow));
          // Elim trade to get original
          elim_trade
            (base_mixed_list_match vmatch p pm bi' (reveal l_narrow))
            (base_mixed_list_match_n vmatch p off n pm bi l);
          fold (mixed_list_match_n vmatch p off n pm (Base bi) l);
        };
      rewrite each (Base bi) as i;
      let i' = Base bi';
      rewrite each (Base bi') as i';
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
    }
    Append depth cb ca ob bp before oa ap after -> {
      // Unfold mixed_list_match_n
      unfold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2
      );
      // Bind child narrow parameters (ghost since off/n are ghost)
      let off_b : Ghost.erased nat = append_off_before (Ghost.reveal off) (SZ.v ob) (SZ.v cb);
      let n1 : Ghost.erased nat = append_n_before (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb);
      let off_a : Ghost.erased nat = append_off_after (Ghost.reveal off) (SZ.v oa) (SZ.v cb);
      let na : Ghost.erased nat = append_n_after (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb);
      let off_b' : Ghost.erased nat = append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb);
      let n1' : Ghost.erased nat = append_n_before (SZ.v off') (SZ.v n') (SZ.v cb);
      let off_a' : Ghost.erased nat = append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb);
      let na' : Ghost.erased nat = append_n_after (SZ.v off') (SZ.v n') (SZ.v cb);
      // Rewrite to let-bound names
      rewrite (mixed_list_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1)
        as (mixed_list_match_n vmatch p off_b n1 pm i_before l1);
      rewrite (mixed_list_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2)
        as (mixed_list_match_n vmatch p off_a na pm i_after l2);
      // Prove narrow preconditions
      append_narrow_before_ineq (Ghost.reveal off) (Ghost.reveal n) (SZ.v off') (SZ.v n') (SZ.v cb);
      append_narrow_after_ineq (Ghost.reveal off) (Ghost.reveal n) (SZ.v off') (SZ.v n') (SZ.v cb);
      // Narrow before child (halves pm)
      mixed_list_match_n_narrow vmatch p off_b n1 off_b' n1' pm i_before l1 vmatch_share vmatch_gather;
      // Share R.pts_to before
      R.share before;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      // Narrow after child (halves pm)
      mixed_list_match_n_narrow vmatch p off_a na off_a' na' pm i_after l2 vmatch_share vmatch_gather;
      // Share R.pts_to after
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      // Compute new SZ.t values for the narrowed Append using pure functions
      append_n_sum (SZ.v off') (SZ.v n') (SZ.v cb);
      let cb'_sz : SZ.t = append_n_before_sz off' n' cb;
      let ca'_sz : SZ.t = append_n_after_sz off' n' cb;
      let ob'_sz : SZ.t = append_off_before_sz off' ob cb;
      let oa'_sz : SZ.t = append_off_after_sz off' oa ca cb;
      // Rewrite narrow results to use new offsets/counts
      rewrite (mixed_list_match_n vmatch p off_b' n1' (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
        as (mixed_list_match_n vmatch p (append_off_before 0 (SZ.v ob'_sz) (SZ.v cb'_sz)) (append_n_before 0 (SZ.v n') (SZ.v cb'_sz)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'));
      rewrite (mixed_list_match_n vmatch p off_a' na' (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
        as (mixed_list_match_n vmatch p (append_off_after 0 (SZ.v oa'_sz) (SZ.v cb'_sz)) (append_n_after 0 (SZ.v n') (SZ.v cb'_sz)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'));
      // Establish list relationship
      list_narrow_append_connect (Ghost.reveal off) (Ghost.reveal n) (SZ.v off') (SZ.v n') (SZ.v cb) (SZ.v ob) (SZ.v oa) l1 l2;
      list_narrow_length l1 (off_b' - off_b) n1';
      list_narrow_length l2 (off_a' - off_a) na';
      // Fold mixed_list_match_n for the new Append at pm/2
      fold (mixed_list_match_n vmatch p 0 (SZ.v n') (pm /. 2.0R)
        (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after)
        (list_narrow l1 (off_b' - off_b) n1' @ list_narrow l2 (off_a' - off_a) na'));
      // Rewrite list_narrow of append to match l_narrow
      rewrite (mixed_list_match_n vmatch p 0 (SZ.v n') (pm /. 2.0R)
        (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after)
        (list_narrow l1 (off_b' - off_b) n1' @ list_narrow l2 (off_a' - off_a) na'))
        as (mixed_list_match vmatch p (pm /. 2.0R)
          (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after)
          (reveal l_narrow));
      // Also rewrite trades back to append_* forms
      rewrite (trade (mixed_list_match_n vmatch p off_b' n1' (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                     (mixed_list_match_n vmatch p off_b n1 pm i_before l1))
        as (trade (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                  (mixed_list_match_n vmatch p (append_off_before (Ghost.reveal off) (SZ.v ob) (SZ.v cb)) (append_n_before (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb)) pm i_before l1));
      rewrite (trade (mixed_list_match_n vmatch p off_a' na' (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                     (mixed_list_match_n vmatch p off_a na pm i_after l2))
        as (trade (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                  (mixed_list_match_n vmatch p (append_off_after (Ghost.reveal off) (SZ.v oa) (SZ.v cb)) (append_n_after (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb)) pm i_after l2));
      // Build trade
      intro (mixed_list_match vmatch p (pm /. 2.0R) (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after) (reveal l_narrow) @==>
             mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l)
        #(trade (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                (mixed_list_match_n vmatch p (append_off_before (Ghost.reveal off) (SZ.v ob) (SZ.v cb)) (append_n_before (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb)) pm i_before l1) **
          R.pts_to before #((pm /. 2.0R) *. bp) i_before **
          trade (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                (mixed_list_match_n vmatch p (append_off_after (Ghost.reveal off) (SZ.v oa) (SZ.v cb)) (append_n_after (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb)) pm i_after l2) **
          R.pts_to after #((pm /. 2.0R) *. ap) i_after **
          pure (
            Ghost.reveal off + Ghost.reveal n <= SZ.v cb + SZ.v ca /\
            SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
            SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
            List.Tot.length l1 == n1 /\
            List.Tot.length l2 == na /\
            l == List.Tot.append l1 l2 /\
            mixed_list_depth i_before < Ghost.reveal depth /\
            mixed_list_depth i_after < Ghost.reveal depth
          ))
        fn _ {
          // Unfold mixed_list_match for the new Append
          rewrite (mixed_list_match vmatch p (pm /. 2.0R) (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after) (reveal l_narrow))
            as (mixed_list_match_n vmatch p 0 (SZ.v n') (pm /. 2.0R) (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after) (reveal l_narrow));
          unfold (mixed_list_match_n vmatch p 0 (SZ.v n') (pm /. 2.0R) (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after) (reveal l_narrow));
          with ib_u ia_u l1_u l2_u . assert (
            pts_to before #((pm /. 2.0R) *. bp) ib_u **
            mixed_list_match_n vmatch p (append_off_before 0 (SZ.v ob'_sz) (SZ.v cb'_sz)) (append_n_before 0 (SZ.v n') (SZ.v cb'_sz)) (pm /. 2.0R) ib_u l1_u **
            pts_to after #((pm /. 2.0R) *. ap) ia_u **
            mixed_list_match_n vmatch p (append_off_after 0 (SZ.v oa'_sz) (SZ.v cb'_sz)) (append_n_after 0 (SZ.v n') (SZ.v cb'_sz)) (pm /. 2.0R) ia_u l2_u
          );
          // Gather R.pts_to before
          R.gather before;
          drop_ (pure (reveal i_before == reveal ib_u));
          rewrite (R.pts_to before #((pm /. 2.0R) *. bp +. (pm /. 2.0R) *. bp) i_before)
            as (R.pts_to before #(pm *. bp) i_before);
          // Gather R.pts_to after
          R.gather after;
          drop_ (pure (reveal i_after == reveal ia_u));
          rewrite (R.pts_to after #((pm /. 2.0R) *. ap +. (pm /. 2.0R) *. ap) i_after)
            as (R.pts_to after #(pm *. ap) i_after);
          // Rewrite child mixed_list_match_n to use original offset names
          rewrite (mixed_list_match_n vmatch p (append_off_before 0 (SZ.v ob'_sz) (SZ.v cb'_sz)) (append_n_before 0 (SZ.v n') (SZ.v cb'_sz)) (pm /. 2.0R) ib_u l1_u)
            as (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ib_u l1_u);
          // Use length + append_injective to identify ib_u = i_before, l1_u = list_narrow l1 ...
          mixed_list_match_n_length vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ib_u l1_u;
          rewrite (mixed_list_match_n vmatch p (append_off_after 0 (SZ.v oa'_sz) (SZ.v cb'_sz)) (append_n_after 0 (SZ.v n') (SZ.v cb'_sz)) (pm /. 2.0R) ia_u l2_u)
            as (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ia_u l2_u);
          mixed_list_match_n_length vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ia_u l2_u;
          list_narrow_length l1 (off_b' - off_b) n1';
          list_narrow_length l2 (off_a' - off_a) na';
          List.Tot.Properties.append_injective l1_u (list_narrow l1 (off_b' - off_b) n1')
            l2_u (list_narrow l2 (off_a' - off_a) na');
          // Rewrite to match trade domains
          with ib_x . assert (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ib_x l1_u);
          slprop_rw
            (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ib_x l1_u)
            (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
            (Pulse.Lib.Core.slprop_equiv_ext'
              (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ib_x l1_u)
              (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
              ());
          // Elim before trade
          elim_trade
            (mixed_list_match_n vmatch p (append_off_before (SZ.v off') (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
            (mixed_list_match_n vmatch p (append_off_before (Ghost.reveal off) (SZ.v ob) (SZ.v cb)) (append_n_before (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb)) pm i_before l1);
          // Rewrite after child
          with ia_x . assert (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ia_x l2_u);
          slprop_rw
            (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ia_x l2_u)
            (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
            (Pulse.Lib.Core.slprop_equiv_ext'
              (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) ia_x l2_u)
              (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
              ());
          // Elim after trade
          elim_trade
            (mixed_list_match_n vmatch p (append_off_after (SZ.v off') (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v off') (SZ.v n') (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
            (mixed_list_match_n vmatch p (append_off_after (Ghost.reveal off) (SZ.v oa) (SZ.v cb)) (append_n_after (Ghost.reveal off) (Ghost.reveal n) (SZ.v cb)) pm i_after l2);
          // Fold original
          fold (mixed_list_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
        };
      let i' = Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after;
      rewrite each (Append #t depth cb'_sz ca'_sz ob'_sz bp before oa'_sz ap after) as i';
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
    }
  }
}
```

#pop-options

// Helper lemma: hd/tl distribute over append when first list is nonempty
let hd_append_l (#a: Type) (l1 l2: list a)
: Lemma (requires Cons? l1)
  (ensures Cons? (l1 @ l2) /\ List.Tot.hd (l1 @ l2) == List.Tot.hd l1 /\
           List.Tot.tl (l1 @ l2) == List.Tot.tl l1 @ l2)
= ()

// Helper: length > 0 implies Cons
let length_pos_cons (#a: Type) (l: list a)
: Lemma (requires List.Tot.length l > 0)
  (ensures Cons? l)
= ()

// Safe predecessor for nat
let nat_pred (n: nat) : nat = if n > 0 then n - 1 else 0

// Helper: from parse_nlist n, extract single element parse for head
let pts_to_parsed_strong_prefix_nlist_hd
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (n: nat) (v': Seq.seq byte) (l: nlist n t)
: Lemma
  (requires n > 0 /\ pts_to_parsed_strong_prefix_prop (parse_nlist n p) v' l)
  (ensures pts_to_parsed_strong_prefix_prop p v' (List.Tot.hd l))
= parse_nlist_eq n p v'

// Helper: extract fst equality from pts_to_parsed_strong_prefix_prop
let pts_to_parsed_fst_eq
  (#k: parser_kind) (#t: Type) (p: parser k t) (bytes: Seq.seq byte) (v: t)
: Lemma
  (requires pts_to_parsed_strong_prefix_prop p bytes v)
  (ensures Some? (parse p bytes) /\ fst (Some?.v (parse p bytes)) == v)
= ()


// Helper: if we have a full parse of (off+n) elements from (v_prefix ++ v_suffix),
// and v_prefix tightly parses off elements (consumed == length), and v_suffix parses as hd_val with p,
// then snd (splitAt off l_all) == hd_val :: tl_val
#push-options "--z3rlimit 120 --fuel 2 --ifuel 1"
let parse_nlist_splitAt_hd_lemma
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (off n m: nat)
  (bytes: Seq.seq byte)
  (v_prefix v_suffix: Seq.seq byte)
  (hd_val: t)
: Lemma
  (requires
    m == off + n /\
    n > 0 /\
    k.parser_kind_subkind == Some ParserStrong /\
    bytes == Seq.append v_prefix v_suffix /\
    Some? (parse (parse_nlist m p) bytes) /\
    (match parse (parse_nlist off p) v_prefix with Some (_, c) -> c == Seq.length v_prefix | _ -> False) /\
    pts_to_parsed_strong_prefix_prop p v_suffix hd_val
  )
  (ensures (
    Cons? (snd (List.Tot.splitAt off (fst (Some?.v (parse (parse_nlist m p) bytes))))) /\
    List.Tot.hd (snd (List.Tot.splitAt off (fst (Some?.v (parse (parse_nlist m p) bytes))))) == hd_val /\
    List.Tot.tl (snd (List.Tot.splitAt off (fst (Some?.v (parse (parse_nlist m p) bytes))))) == snd (List.Tot.splitAt (off + 1) (fst (Some?.v (parse (parse_nlist m p) bytes))))
  ))
= let l_all = fst (Some?.v (parse (parse_nlist m p) bytes)) in
  parse_nlist_sum p off n bytes;
  parser_kind_prop_equiv (LowParse.Spec.VCList.parse_nlist_kind off k) (parse_nlist off p);
  assert (Seq.length v_prefix <= Seq.length bytes);
  assert (Seq.slice bytes 0 (Seq.length v_prefix) `Seq.equal` v_prefix);
  assert (Seq.slice v_prefix 0 (Seq.length v_prefix) `Seq.equal` v_prefix);
  assert (no_lookahead_on_precond (parse_nlist off p) v_prefix bytes);
  assert (no_lookahead_on_postcond (parse_nlist off p) v_prefix bytes);
  assert (Seq.slice bytes (Seq.length v_prefix) (Seq.length bytes) `Seq.equal` v_suffix);
  parse_nlist_eq n p v_suffix;
  let prefix_parse = parse (parse_nlist off p) v_prefix in
  assert (Some? prefix_parse);
  let Some (prefix_list, prefix_consumed) = prefix_parse in
  assert (prefix_consumed == Seq.length v_prefix);
  let bytes_parse = parse (parse_nlist off p) bytes in
  assert (Some? bytes_parse);
  let Some (l1, consumed1) = bytes_parse in
  assert (consumed1 == Seq.length v_prefix);
  assert (l1 == prefix_list);
  assert (List.Tot.length l1 == off);
  let suffix_slice = Seq.slice bytes consumed1 (Seq.length bytes) in
  assert (suffix_slice `Seq.equal` v_suffix);
  let suffix_parse = parse (parse_nlist n p) v_suffix in
  assert (Some? suffix_parse);
  let Some (l2, _consumed2) = suffix_parse in
  assert (l_all == List.Tot.append l1 l2);
  FStar.List.Pure.Properties.lemma_append_splitAt l1 l2;
  assert (List.Tot.length l2 == n);
  assert (Cons? l2);
  let hd_l2 :: tl_l2 = l2 in
  assert (hd_l2 == hd_val);
  List.Tot.append_assoc l1 [hd_val] tl_l2;
  List.Tot.append_length l1 [hd_val];
  assert (List.Tot.length (List.Tot.append l1 [hd_val]) == off + 1);
  assert (l_all == List.Tot.append (List.Tot.append l1 [hd_val]) tl_l2);
  FStar.List.Pure.Properties.lemma_append_splitAt (List.Tot.append l1 [hd_val]) tl_l2
#pop-options

// Combined lemma for Serialized trade body:
// Uses pts_to_parsed_strong_prefix_prop as precondition to match SL pures directly.
// This avoids needing SMT to extract Some? and fst==l_all from the prop.
#push-options "--z3rlimit 120 --fuel 2 --ifuel 1"
let parse_nlist_splitAt_hd_full_lemma
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (off n m: nat)
  (bytes: Seq.seq byte)
  (l_all: nlist m t)
  (l: list t)
  (v_prefix v_suffix: Seq.seq byte)
  (hd_val: t)
: Lemma
  (requires
    m == off + n /\
    n > 0 /\
    Cons? l /\
    hd_val == List.Tot.hd l /\
    List.Tot.tl l == snd (List.Tot.splitAt (off + 1) l_all) /\
    k.parser_kind_subkind == Some ParserStrong /\
    bytes == Seq.append v_prefix v_suffix /\
    pts_to_parsed_strong_prefix_prop (parse_nlist m p) bytes l_all /\
    (match parse (parse_nlist off p) v_prefix with Some (_, c) -> c == Seq.length v_prefix | _ -> False) /\
    pts_to_parsed_strong_prefix_prop p v_suffix hd_val
  )
  (ensures l == snd (List.Tot.splitAt off l_all))
= parse_nlist_splitAt_hd_lemma p off n m bytes v_prefix v_suffix hd_val
#pop-options

// Helper: tl(snd(splitAt i l)) == snd(splitAt (i+1) l)
let rec lemma_splitAt_tl_snd (#t: Type) (i: nat) (l: list t)
: Lemma
  (requires i < List.Tot.length l)
  (ensures (
    List.Tot.Base.lemma_splitAt_snd_length i l;
    Cons? (snd (List.Tot.splitAt i l)) /\
    List.Tot.tl (snd (List.Tot.splitAt i l)) == snd (List.Tot.splitAt (i + 1) l)
  ))
= List.Tot.Base.lemma_splitAt_snd_length i l;
  match i with
  | 0 -> ()
  | _ -> lemma_splitAt_tl_snd (i - 1) (List.Tot.tl l)

// Helper: pts_to_parsed_strong_prefix_prop for suffix after jump/split
let pts_to_parsed_strong_prefix_prop_nlist_suffix
  (#k: parser_kind) (#t: Type)
  (p: parser k t) (off n: nat)
  (v': Seq.seq byte) (l_all: nlist (off + n) t) (l: nlist n t)
  (pos: SZ.t)
: Lemma
  (requires
    pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) v' l_all /\
    l == snd (List.Tot.splitAt off l_all) /\
    LPS.validator_success (parse_nlist off p) 0sz v' pos
  )
  (ensures
    pts_to_parsed_strong_prefix_prop (parse_nlist n p) (Seq.slice v' (SZ.v pos) (Seq.length v')) l
  )
= parse_nlist_sum p off n v';
  let Some (_, consumed1) = parse (parse_nlist off p) v' in
  assert (consumed1 == SZ.v pos);
  let v_suffix = Seq.slice v' (SZ.v pos) (Seq.length v') in
  let Some (l2, consumed2) = parse (parse_nlist n p) v_suffix in
  let Some (l1, _) = parse (parse_nlist off p) v' in
  List.Tot.append_length l1 l2;
  FStar.List.Pure.Properties.lemma_append_splitAt l1 l2

// Pure function wrapper returning squash — workaround for lemma postconditions
// not propagating in Pulse trade body lambdas.
let parse_nlist_splitAt_hd_full_squash
  (#k: parser_kind) (#t: Type)
  (p: parser k t)
  (off n m: nat)
  (bytes: Seq.seq byte)
  (l_all: nlist m t)
  (l: list t)
  (v_prefix v_suffix: Seq.seq byte)
  (hd_val: t)
: Pure (squash (l == snd (List.Tot.splitAt off l_all)))
  (requires
    m == off + n /\
    n > 0 /\
    Cons? l /\
    hd_val == List.Tot.hd l /\
    List.Tot.tl l == snd (List.Tot.splitAt (off + 1) l_all) /\
    k.parser_kind_subkind == Some ParserStrong /\
    bytes == Seq.append v_prefix v_suffix /\
    pts_to_parsed_strong_prefix_prop (parse_nlist m p) bytes l_all /\
    (match parse (parse_nlist off p) v_prefix with Some (_, c) -> c == Seq.length v_prefix | _ -> False) /\
    pts_to_parsed_strong_prefix_prop p v_suffix hd_val
  )
  (ensures fun _ -> True)
= parse_nlist_splitAt_hd_full_lemma p off n m bytes l_all l v_prefix v_suffix hd_val

// Lemma: fst(splitAt n (l1 ++ l2)) == fst(splitAt n l1) when n <= length l1
let rec lemma_splitAt_fst_append (#a: Type) (n: nat) (l1 l2: list a)
  : Lemma (requires n <= List.Tot.length l1)
          (ensures fst (List.Tot.splitAt n (l1 @ l2)) == fst (List.Tot.splitAt n l1))
          (decreases n)
= match n with
  | 0 -> ()
  | _ -> match l1 with
    | _ :: l1' -> lemma_splitAt_fst_append (n - 1) l1' l2

// Lemma: list_narrow l 0 n ++ list_narrow l n (len - n) == l when n <= len = length l
let list_narrow_split (#a: Type) (l: list a) (n: nat)
  : Lemma (requires n <= List.Tot.length l)
          (ensures List.Tot.append (list_narrow l 0 n) (list_narrow l n (List.Tot.length l - n)) == l)
= // list_narrow l 0 n = fst (splitAt n (snd (splitAt 0 l))) = fst (splitAt n l) = l1
  // list_narrow l n (len-n) = fst (splitAt (len-n) (snd (splitAt n l))) = fst (splitAt (len-n) l2) = l2
  let (l1, l2) = List.Tot.splitAt n l in
  FStar.List.Pure.Properties.splitAt_length n l;
  // length l1 == n, length l2 == length l - n
  FStar.List.Tot.Base.lemma_splitAt_snd_length n l;
  // splitAt (length l2) l2 == (l2, [])
  FStar.List.Pure.Properties.splitAt_length_total l2;
  // l == l1 @ l2
  FStar.List.Pure.Properties.lemma_splitAt l l1 l2 n

// Extract the first non-empty base_mixed_list from an mixed_list,
// returning it with base_mixed_list_match and a trade back.
// Descends the Append tree following a single path until a Base node is found.
#push-options "--z3rlimit 4000 --fuel 2 --ifuel 1"

inline_for_extraction
```pulse
fn mixed_list_extract_first_base_loop
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (off: Ghost.erased nat) (n: Ghost.erased nat { Ghost.reveal n > 0 })
  (off_sz: SZ.t { SZ.v off_sz == Ghost.reveal off })
  (n_sz: SZ.t { SZ.v n_sz == Ghost.reveal n })
  (pm: perm) (i: mixed_list t) (l: Ghost.erased (list u))
requires
  mixed_list_match_n vmatch p off n pm i l
returns res: (base_mixed_list t & SZ.t)
ensures (
  let (bi', len) = res in
  base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v len)) **
  trade (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v len)))
       (mixed_list_match_n vmatch p off n pm i l) **
  pure (SZ.v len == SZ.v (base_mixed_list_length bi') /\ SZ.v len > 0 /\ SZ.v len <= Ghost.reveal n)
)
{
  let mut r_node = i;
  let mut r_off = off_sz;
  let mut r_n = n_sz;
  let mut pcontinue = not (Base? i);
  // Rewrite to use concrete sizes
  rewrite (mixed_list_match_n vmatch p off n pm i l)
    as (mixed_list_match_n vmatch p (SZ.v off_sz) (SZ.v n_sz) pm i (Ghost.reveal l));
  // Initial trade: reflexive
  Trade.refl (mixed_list_match_n vmatch p (SZ.v off_sz) (SZ.v n_sz) pm i (Ghost.reveal l));
  rewrite (trade (mixed_list_match_n vmatch p (SZ.v off_sz) (SZ.v n_sz) pm i (Ghost.reveal l))
                 (mixed_list_match_n vmatch p (SZ.v off_sz) (SZ.v n_sz) pm i (Ghost.reveal l)))
    as (trade (mixed_list_match_n vmatch p (SZ.v off_sz) (SZ.v n_sz) pm i (Ghost.reveal l))
              (mixed_list_match_n vmatch p off n pm i l));
  mixed_list_match_n_length vmatch p (SZ.v off_sz) (SZ.v n_sz) pm i (Ghost.reveal l);
  while (
    let c = !pcontinue;
    c
  ) invariant exists* c (cur: mixed_list t) (cur_off: SZ.t) (cur_n: SZ.t) (l_cur: list u).
    R.pts_to pcontinue c **
    R.pts_to r_node cur **
    R.pts_to r_off cur_off **
    R.pts_to r_n cur_n **
    mixed_list_match_n vmatch p (SZ.v cur_off) (SZ.v cur_n) pm cur l_cur **
    trade (mixed_list_match_n vmatch p (SZ.v cur_off) (SZ.v cur_n) pm cur l_cur)
         (mixed_list_match_n vmatch p off n pm i l) **
    pure (
      SZ.v cur_n > 0 /\
      SZ.v cur_n <= Ghost.reveal n /\
      List.Tot.length l_cur >= SZ.v cur_n /\
      list_narrow l_cur 0 (SZ.v cur_n) == list_narrow (Ghost.reveal l) 0 (SZ.v cur_n) /\
      (c == true ==> Append? cur) /\
      (c == false ==> Base? cur)
    )
  {
    let node = !r_node;
    let cur_off_v = !r_off;
    let cur_n_v = !r_n;
    with _l_cur . assert (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_cur);
    match node {
      Append depth cb ca ob bp before oa ap after -> {
        rewrite (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_cur)
          as (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur);
        unfold (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur);
        with i_before i_after l1 l2 . assert (
          pts_to before #(pm *. bp) i_before **
          mixed_list_match_n vmatch p (append_off_before (SZ.v cur_off_v) (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_before l1 **
          pts_to after #(pm *. ap) i_after **
          mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_after l2 **
          pure (
            SZ.v cur_off_v + SZ.v cur_n_v <= SZ.v cb + SZ.v ca /\
            SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_before) /\
            SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_after) /\
            List.Tot.length l1 == append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb) /\
            List.Tot.length l2 == append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb) /\
            _l_cur == List.Tot.append l1 l2 /\
            mixed_list_depth i_before < Ghost.reveal depth /\
            mixed_list_depth i_after < Ghost.reveal depth
          )
        );
        let child_n_before = append_n_before_sz cur_off_v cur_n_v cb;
        if (SZ.gt child_n_before 0sz) {
          // Descend into "before" child
          let child_off_sz = append_off_before_sz cur_off_v ob cb;
          let ib = R.read before;
          with i_x l_x . rewrite
            (mixed_list_match_n vmatch p (append_off_before (SZ.v cur_off_v) (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_x l_x)
            as (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_before) pm ib l_x);
          with l_before . assert (
            mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_before) pm ib l_before
          );
          // Build trade: before_match → Append_match
          with i_aft l_aft . assert (
            pts_to after #(pm *. ap) i_aft **
            mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_aft l_aft
          );
          intro (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_before) pm ib (Ghost.reveal l_before) @==>
                 mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur)
            #(pts_to before #(pm *. bp) ib **
              pts_to after #(pm *. ap) i_aft **
              mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_aft l_aft **
              pure (
                SZ.v cur_off_v + SZ.v cur_n_v <= SZ.v cb + SZ.v ca /\
                SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length ib) /\
                SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length i_aft) /\
                List.Tot.length (Ghost.reveal l_before) == append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb) /\
                List.Tot.length (Ghost.reveal l_aft) == append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb) /\
                _l_cur == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal l_aft) /\
                mixed_list_depth ib < Ghost.reveal depth /\
                mixed_list_depth i_aft < Ghost.reveal depth))
            fn _ {
              rewrite (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_before) pm ib (Ghost.reveal l_before))
                as (mixed_list_match_n vmatch p (append_off_before (SZ.v cur_off_v) (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm ib l_before);
              rewrite (mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_aft l_aft)
                as (mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_aft l_aft);
              fold (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur);
            };
          // Compose with accumulated trade
          rewrite (trade (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_cur)
                        (mixed_list_match_n vmatch p off n pm i l))
            as (trade (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur)
                      (mixed_list_match_n vmatch p off n pm i l));
          Trade.trans
            (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_before) pm ib (Ghost.reveal l_before))
            (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur)
            (mixed_list_match_n vmatch p off n pm i l);
          // Prove list_narrow invariant for new state
          lemma_splitAt_fst_append (SZ.v child_n_before) (Ghost.reveal l_before) (Ghost.reveal l_aft);
          list_narrow_prefix _l_cur (Ghost.reveal l) (SZ.v cur_n_v) (SZ.v child_n_before);
          // Update refs
          r_node := ib;
          r_off := child_off_sz;
          r_n := child_n_before;
          pcontinue := not (Base? ib);
        } else {
          // Descend into "after" child (n_before == 0)
          let child_off_sz = append_off_after_sz cur_off_v oa ca cb;
          let child_n_sz = append_n_after_sz cur_off_v cur_n_v cb;
          let ia = R.read after;
          with i_y l_y . rewrite
            (mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_y l_y)
            as (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_sz) pm ia l_y);
          with l_aft . assert (
            mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_sz) pm ia l_aft
          );
          // Build trade: after_match → Append_match
          with i_bef l_bef . assert (
            pts_to before #(pm *. bp) i_bef **
            mixed_list_match_n vmatch p (append_off_before (SZ.v cur_off_v) (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_bef l_bef
          );
          intro (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_sz) pm ia (Ghost.reveal l_aft) @==>
                 mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur)
            #(pts_to before #(pm *. bp) i_bef **
              mixed_list_match_n vmatch p (append_off_before (SZ.v cur_off_v) (SZ.v ob) (SZ.v cb)) (append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm i_bef l_bef **
              pts_to after #(pm *. ap) ia **
              pure (
                SZ.v cur_off_v + SZ.v cur_n_v <= SZ.v cb + SZ.v ca /\
                SZ.v ob + SZ.v cb <= SZ.v (mixed_list_length i_bef) /\
                SZ.v oa + SZ.v ca <= SZ.v (mixed_list_length ia) /\
                List.Tot.length (Ghost.reveal l_bef) == append_n_before (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb) /\
                List.Tot.length (Ghost.reveal l_aft) == append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb) /\
                _l_cur == List.Tot.append (Ghost.reveal l_bef) (Ghost.reveal l_aft) /\
                mixed_list_depth i_bef < Ghost.reveal depth /\
                mixed_list_depth ia < Ghost.reveal depth))
            fn _ {
              rewrite (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_sz) pm ia (Ghost.reveal l_aft))
                as (mixed_list_match_n vmatch p (append_off_after (SZ.v cur_off_v) (SZ.v oa) (SZ.v cb)) (append_n_after (SZ.v cur_off_v) (SZ.v cur_n_v) (SZ.v cb)) pm ia l_aft);
              fold (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur);
            };
          // Compose with accumulated trade
          rewrite (trade (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_cur)
                        (mixed_list_match_n vmatch p off n pm i l))
            as (trade (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur)
                      (mixed_list_match_n vmatch p off n pm i l));
          Trade.trans
            (mixed_list_match_n vmatch p (SZ.v child_off_sz) (SZ.v child_n_sz) pm ia (Ghost.reveal l_aft))
            (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Append #t depth cb ca ob bp before oa ap after) _l_cur)
            (mixed_list_match_n vmatch p off n pm i l);
          // Prove list_narrow invariant: n_before == 0, so l_bef == [] and _l_cur == l_aft
          List.Tot.Properties.append_l_nil (Ghost.reveal l_aft);
          // Update refs
          r_node := ia;
          r_off := child_off_sz;
          r_n := child_n_sz;
          pcontinue := not (Base? ia);
        }
      }
      Base _ -> {
        // Unreachable: condition was true (not Base?)
        // Re-establish invariant unchanged
        ()
      }
    }
  };
  // After loop: cur is Base
  let node = !r_node;
  let cur_off_v = !r_off;
  let cur_n_v = !r_n;
  with _l_fin . assert (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_fin);
  match node {
    Base bi -> {
      rewrite (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_fin)
        as (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin);
      unfold (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin);
      let bi' = base_mixed_list_narrow_n vmatch p j (SZ.v cur_off_v) (SZ.v cur_n_v) pm bi _l_fin cur_off_v cur_n_v;
      // bi' has: base_mixed_list_match pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)) + trade + pure
      // list_narrow _l_fin 0 cur_n_v == list_narrow l 0 cur_n_v (from invariant)
      rewrite (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin (SZ.v cur_off_v - SZ.v cur_off_v) (SZ.v cur_n_v)))
        as (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)));
      rewrite (trade (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin (SZ.v cur_off_v - SZ.v cur_off_v) (SZ.v cur_n_v)))
                    (base_mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm bi _l_fin))
        as (trade (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)))
                  (base_mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm bi _l_fin));
      // Build trade: base_match_n → mixed_list_match_n (Base)
      intro (base_mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm bi (Ghost.reveal _l_fin) @==>
             mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin)
        fn _ {
          fold (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin);
        };
      // Compose: base_mixed_list_match → base_match_n → mixed_list_match_n (Base) → original
      Trade.trans
        (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)))
        (base_mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm bi _l_fin)
        (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin);
      rewrite (trade (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm node _l_fin)
                    (mixed_list_match_n vmatch p off n pm i l))
        as (trade (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin)
                  (mixed_list_match_n vmatch p off n pm i l));
      Trade.trans
        (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)))
        (mixed_list_match_n vmatch p (SZ.v cur_off_v) (SZ.v cur_n_v) pm (Base bi) _l_fin)
        (mixed_list_match_n vmatch p off n pm i l);
      // Rewrite list_narrow _l_fin to list_narrow l (using invariant)
      rewrite (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)))
        as (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v cur_n_v)));
      rewrite (trade (base_mixed_list_match vmatch p pm bi' (list_narrow _l_fin 0 (SZ.v cur_n_v)))
                    (mixed_list_match_n vmatch p off n pm i l))
        as (trade (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v cur_n_v)))
                  (mixed_list_match_n vmatch p off n pm i l));
      let len = base_mixed_list_length bi';
      rewrite (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v cur_n_v)))
        as (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v len)));
      rewrite (trade (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v cur_n_v)))
                    (mixed_list_match_n vmatch p off n pm i l))
        as (trade (base_mixed_list_match vmatch p pm bi' (list_narrow l 0 (SZ.v len)))
                  (mixed_list_match_n vmatch p off n pm i l));
      (bi', len)
    }
    Append _ _ _ _ _ _ _ _ _ -> {
      // Unreachable: loop exited with Base? cur
      unreachable ()
    }
  }
}
```

#pop-options

// Always returns an element matching the head, shifted match on tail at pm/2, trade back
let mixed_list_next_n_post
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off: Ghost.erased nat) (n: Ghost.erased nat) (pm: perm) (i: mixed_list t) (l: list u)
  (res: t)
: Tot slprop
= exists* pm_v hd_val tl_val .
    vmatch pm_v res hd_val **
    mixed_list_match_n vmatch p (Ghost.reveal off + 1) (nat_pred (Ghost.reveal n)) (pm /. 2.0R) i tl_val **
    trade
      (vmatch pm_v res hd_val **
       mixed_list_match_n vmatch p (Ghost.reveal off + 1) (nat_pred (Ghost.reveal n)) (pm /. 2.0R) i tl_val)
      (mixed_list_match_n vmatch p (Ghost.reveal off) (Ghost.reveal n) pm i l) **
    pure (Ghost.reveal n > 0 /\ l == hd_val :: tl_val)


// Ghost fn: trade body for mixed_list_next Serialized case.
// Recovers the original mixed_list_match_n from the split head/tail.
#push-options "--z3rlimit 4000 --fuel 2 --ifuel 1 --ext no:context_pruning"

```pulse
ghost fn serialized_next_trade_body
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n: nat)
  (sp: perm) (count: SZ.t) (pm: perm)
  (pl pl_prefix pl_suffix: S.slice byte)
  (v': Ghost.erased (Seq.seq byte))
  (l: Ghost.erased (list u))
  (x_val: t)
  (pos: SZ.t)
  (sq_pos_bound: squash (SZ.v pos <= Seq.length (reveal v')))
  (sq_n: squash (n > 0 /\ Cons? (reveal l)))
  (sq_validator: squash (LPS.validator_success (parse_nlist off p) 0sz (reveal v') pos))
  (sq_strong: squash (k.parser_kind_subkind == Some ParserStrong))
requires
  vmatch 1.0R x_val (List.Tot.hd (reveal l)) **
  mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (reveal l)) **
  trade (vmatch 1.0R x_val (List.Tot.hd (reveal l)))
       (pts_to_parsed_strong_prefix p pl_suffix #((pm *. sp) /. 2.0R) (List.Tot.hd (reveal l))) **
  S.pts_to pl_prefix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') 0 (SZ.v pos)) **
  S.is_split pl pl_prefix pl_suffix
ensures
  mixed_list_match_n vmatch p off n pm (Base (Serialized #t sp count pl)) (reveal l)
{
  // Step 1: Unfold tail mixed_list to reach S.pts_to pl at half perm
  unfold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (reveal l)));
  unfold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Serialized #t sp count pl) (List.Tot.tl (reveal l)));
  with l_all'. assert (pts_to_parsed_strong_prefix (parse_nlist ((off + 1) + nat_pred n) p) pl #((pm /. 2.0R) *. sp) l_all');
  rewrite (pts_to_parsed_strong_prefix (parse_nlist ((off + 1) + nat_pred n) p) pl #((pm /. 2.0R) *. sp) l_all')
    as (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all');
  unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all');
  with v_tail. assert (S.pts_to pl #((pm *. sp) /. 2.0R) v_tail);

  // Step 2: Exercise vmatch→pts_to trade to recover suffix bytes
  elim_trade _ _;
  unfold (pts_to_parsed_strong_prefix p pl_suffix #((pm *. sp) /. 2.0R) (List.Tot.hd (reveal l)));
  with v_s. assert (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) v_s);

  // Step 3: Join prefix + suffix → full slice at half perm
  S.join pl_prefix pl_suffix pl;

  // Step 4: Gather two halves — proves byte equality via pure(s0 == s1)
  S.gather pl;
  // gather gives: pts_to pl #(half+half) v_tail ** pure(v_tail == Seq.append (slice v' 0 pos) v_s)
  // Now derive l == snd(splitAt off l_all') via parse_nlist_splitAt_hd_full_lemma
  parser_kind_prop_equiv (parse_nlist_kind off k) (parse_nlist off p);
  Seq.lemma_eq_intro (Seq.slice (reveal v') 0 (Seq.length (reveal v'))) (reveal v');
  parse_strong_prefix (parse_nlist off p) (reveal v') (Seq.slice (reveal v') 0 (SZ.v pos));
  parse_nlist_splitAt_hd_full_lemma p off n (off + n) (reveal v_tail) l_all' (reveal l) (Seq.slice (reveal v') 0 (SZ.v pos)) (reveal v_s) (List.Tot.hd (reveal l));

  // Step 5: Fold back with l_all' and v_tail
  with v_g. assert (S.pts_to pl #((pm *. sp) /. 2.0R +. (pm *. sp) /. 2.0R) v_g);
  rewrite (S.pts_to pl #((pm *. sp) /. 2.0R +. (pm *. sp) /. 2.0R) v_g)
    as (S.pts_to pl #(pm *. sp) v_g);
  // v_g == v_tail (gather picks first operand)
  rewrite (S.pts_to pl #(pm *. sp) v_g)
    as (S.pts_to pl #(pm *. sp) (reveal v_tail));
  fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all');
  fold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l));
  fold (mixed_list_match_n vmatch p off n pm (Base (Serialized #t sp count pl)) (reveal l));
}
```

#pop-options

#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction
```pulse
fn base_mixed_list_next_n
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off: Ghost.erased nat) (n: Ghost.erased nat { Ghost.reveal n > 0 })
  (off_sz: SZ.t { SZ.v off_sz == Ghost.reveal off }) (n_sz: SZ.t { SZ.v n_sz == Ghost.reveal n })
  (pm: perm) (bi: base_mixed_list t) (l: Ghost.erased (list u))
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (j: LPS.jumper p)
  (zcp: zero_copy_parse_strong_prefix (vmatch 1.0R) p)
requires
  base_mixed_list_match_n vmatch p off n pm bi (Ghost.reveal l)
returns res: t
ensures
  mixed_list_next_n_post vmatch p off n pm (Base bi) (Ghost.reveal l) res
{
  match bi {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Empty #t) (Ghost.reveal l));
      unreachable ()
    }
    Singleton sp sv s -> {
      base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm sp sv s (Ghost.reveal l) ();
      with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y **
        pure (Ghost.reveal l == [y] /\ off == 0 /\ n == 1));
      let x_val = R.read s;
      // Fold 0-case at pm/2 (needs only pure, not pts_to)
      fold (base_mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Singleton #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
      fold (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
      rewrite (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)))
        as (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
      rewrite each x as x_val;
      rewrite (vmatch (pm *. sv) x_val y)
        as (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)));
      intro (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)) **
             mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l))
             @==>
             mixed_list_match_n vmatch p off n pm (Base (Singleton #t sp sv s)) (Ghost.reveal l))
        #(pts_to s #(pm *. sp) x_val **
          pure (Ghost.reveal l == [y] /\ off == 0 /\ n == 1))
        fn _ {
          rewrite (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)))
            as (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
          unfold (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
          unfold (base_mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Singleton #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
          drop_ (pure (Nil? (List.Tot.tl (Ghost.reveal l)) /\ 1 <= 1));
          rewrite (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)))
            as (vmatch (pm *. sv) x_val y);
          base_mixed_list_match_n_singleton_fold_pos vmatch p off n pm sp sv s (Ghost.reveal l) ();
          fold (mixed_list_match_n vmatch p off n pm (Base (Singleton #t sp sv s)) (Ghost.reveal l));
        };
      fold (mixed_list_next_n_post vmatch p off n pm (Base (Singleton #t sp sv s)) (Ghost.reveal l) x_val);
      rewrite each (Singleton #t sp sv s) as bi;
      x_val
    }
    Slice sp sv s -> {
      // Read element from slice at position off
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) (Ghost.reveal l));
      with l' sl1. assert (S.pts_to s #(pm *. sp) l' ** SM.seq_list_match sl1 (Ghost.reveal l) (vmatch (pm *. sv)));
      S.pts_to_len s;
      SM.seq_list_match_length (vmatch (pm *. sv)) sl1 (Ghost.reveal l);
      // sl1 == Seq.slice l' off (off+n), read at position off
      let x_val = S.op_Array_Access s off_sz;
      // Split head from seq_list_match
      SMU.seq_list_match_cons_elim_trade sl1 (Ghost.reveal l) (vmatch (pm *. sv));
      // Share pts_to s
      S.share s;
      rewrite (S.pts_to s #((pm *. sp) /. 2.0R) l') as (S.pts_to s #((pm /. 2.0R) *. sp) l');
      rewrite (S.pts_to s #((pm *. sp) /. 2.0R) l') as (S.pts_to s #((pm /. 2.0R) *. sp) l');
      // Share tail seq_list_match
      ghost fn share_prf
        (c': t)
        (v': u { v' << List.Tot.tl (Ghost.reveal l) })
      requires vmatch (pm *. sv) c' v'
      ensures vmatch ((pm /. 2.0R) *. sv) c' v' ** vmatch ((pm /. 2.0R) *. sv) c' v'
      {
        vmatch_share c' #(pm *. sv) #v';
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
      };
      seq_list_match_share (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l))
        (vmatch (pm *. sv))
        (vmatch ((pm /. 2.0R) *. sv))
        share_prf;
      // Fold tail into base_mixed_list_match_n at pm/2
      Seq.lemma_index_slice l' off (off + n) 0;
      assert (pure (Seq.head sl1 == Seq.index l' off));
      fold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Slice #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
      fold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Slice #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
      // Rewrite head vmatch
      rewrite (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)))
        as (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)));
      // Build trade
      intro (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)) **
             mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Slice #t sp sv s)) (List.Tot.tl (Ghost.reveal l))
             @==>
             mixed_list_match_n vmatch p off n pm (Base (Slice #t sp sv s)) (Ghost.reveal l))
        #(trade
            (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)) **
             SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch (pm *. sv)))
            (SM.seq_list_match sl1 (Ghost.reveal l) (vmatch (pm *. sv))) **
          S.pts_to s #((pm /. 2.0R) *. sp) l' **
          SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)) **
          pure (off + n <= Seq.length l' /\ sl1 == Seq.slice l' off (off + n)) **
          pure (Seq.head sl1 == Seq.index l' off))
        fn _ {
          // Trade body: unfold tail, gather, elim inner trade, fold original
          // First, disambiguate the frame's pts_to by rewriting its perm
          rewrite (S.pts_to s #((pm /. 2.0R) *. sp) l') as (S.pts_to s #((pm *. sp) /. 2.0R) l');
          // Also disambiguate the frame's seq_list_match
          rewrite (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          // Now unfold the exchange condition's mixed_list_match_n
          unfold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Slice #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
          unfold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Slice #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
          // The unfold produces: S.pts_to s #((pm/.2)*.sp) l'2 ** seq_list_match sl1_2 (tl l) (vmatch ((pm/.2)*.sv)) ** pure(...)
          with l'2 sl1_2. assert (
            S.pts_to s #((pm /. 2.0R) *. sp) l'2 **
            SM.seq_list_match sl1_2 (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv))
          );
          // Gather pts_to
          rewrite (S.pts_to s #((pm /. 2.0R) *. sp) l'2) as (S.pts_to s #((pm *. sp) /. 2.0R) l'2);
          S.gather s;
          // Gather tail seq_list_match
          rewrite (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          rewrite (SM.seq_list_match sl1_2 (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match sl1_2 (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          rewrite (SM.seq_list_match sl1_2 (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          ghost fn gather_prf
            (c': t) (v1': u { v1' << List.Tot.tl (Ghost.reveal l) }) (v2': u { v2' << List.Tot.tl (Ghost.reveal l) /\ List.Tot.memP v2' (List.Tot.tl (Ghost.reveal l)) })
          requires vmatch ((pm *. sv) /. 2.0R) c' v1' ** vmatch ((pm *. sv) /. 2.0R) c' v2'
          ensures vmatch (pm *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
          {
            vmatch_gather c' #((pm *. sv) /. 2.0R) #v1' #((pm *. sv) /. 2.0R) #v2';
            rewrite (vmatch ((pm *. sv) /. 2.0R +. (pm *. sv) /. 2.0R) c' v1') as (vmatch (pm *. sv) c' v1');
          };
          seq_list_match_gather_memP (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (List.Tot.tl (Ghost.reveal l))
            (vmatch ((pm *. sv) /. 2.0R))
            (vmatch ((pm *. sv) /. 2.0R))
            (vmatch (pm *. sv))
            gather_prf;
          drop_ (pure (List.Tot.tl (Ghost.reveal l) == List.Tot.tl (Ghost.reveal l)));
          drop_ (pure (l' == l'2));
          drop_ (pure ((off + 1) + nat_pred n <= Seq.length l'2 /\ sl1_2 == Seq.slice l'2 (off + 1) (off + 1 + nat_pred n)));
          drop_ (pure (off + n <= Seq.length l' /\ sl1 == Seq.slice l' off (off + n)));
          drop_ (pure (Seq.head sl1 == Seq.index l' off));
          // Rewrite head vmatch back
          rewrite (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)))
            as (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)));
          // Elim inner trade
          elim_trade
            (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)) **
             SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch (pm *. sv)))
            (SM.seq_list_match sl1 (Ghost.reveal l) (vmatch (pm *. sv)));
          // Fold
          rewrite (S.pts_to s #((pm *. sp) /. 2.0R +. (pm *. sp) /. 2.0R) l') as (S.pts_to s #(pm *. sp) l');
          fold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) (Ghost.reveal l));
          fold (mixed_list_match_n vmatch p off n pm (Base (Slice #t sp sv s)) (Ghost.reveal l));
        };
      fold (mixed_list_next_n_post vmatch p off n pm (Base (Slice #t sp sv s)) (Ghost.reveal l) x_val);
      rewrite each (Slice #t sp sv s) as bi;
      x_val
    }
    Serialized sp count pl -> {
      // Parse element from serialized bytes at position off
      unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (Ghost.reveal l));
      with l_all. assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      // Unfold pts_to_parsed_strong_prefix
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      with v'. assert (S.pts_to pl #(pm *. sp) v');
      // Share S.pts_to
      S.share pl;
      // FIRST: use one half to jump to position off and parse head
      S.pts_to_len pl;
      parse_nlist_sum p off n (reveal v');
      intro_pure (LPS.jumper_pre' (parse_nlist off p) 0sz v') ();
      let pos = LPV.jump_nlist j off_sz pl 0sz;
      let pl_p = S.split pl pos;
      match pl_p {
        pl_prefix, pl_suffix -> {
      with v_prefix. assert (S.pts_to pl_prefix #((pm *. sp) /. 2.0R) v_prefix);
      with v_suffix. assert (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) v_suffix);
      S.pts_to_len pl_suffix;
      // Establish length l == n so Ghost.reveal l : nlist n u
      List.Tot.Base.lemma_splitAt_snd_length off l_all;
      // Establish strong prefix prop for suffix
      pts_to_parsed_strong_prefix_prop_nlist_suffix p off n (reveal v') l_all (Ghost.reveal l) pos;
      // Assert the strong prefix prop on the suffix
      assert (pure (pts_to_parsed_strong_prefix_prop (parse_nlist n p) (reveal v_suffix) (Ghost.reveal l)));
      pts_to_parsed_strong_prefix_nlist_hd p n (reveal v_suffix) (Ghost.reveal l);
      // Fold into pts_to_parsed_strong_prefix p and call zcp
      rewrite (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) v_suffix)
        as (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (reveal v_suffix));
      fold (pts_to_parsed_strong_prefix p pl_suffix #((pm *. sp) /. 2.0R) (List.Tot.hd (Ghost.reveal l)));
      let x_val = zcp pl_suffix #((pm *. sp) /. 2.0R) #(Ghost.hide (List.Tot.hd (Ghost.reveal l)));
      // SECOND: fold the other half into tail mixed_list_match_n
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all);
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all)
        as (pts_to_parsed_strong_prefix (parse_nlist ((off + 1) + nat_pred n) p) pl #((pm /. 2.0R) *. sp) l_all);
      List.Tot.Base.lemma_splitAt_snd_length off l_all;
      lemma_splitAt_tl_snd off l_all;
      assert (pure (List.Tot.tl (Ghost.reveal l) == snd (List.Tot.splitAt (off + 1) l_all) /\ (off + 1) + nat_pred n <= SZ.v count));
      fold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Serialized #t sp count pl) (List.Tot.tl (Ghost.reveal l)));
      fold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (Ghost.reveal l)));
      // Build the trade
      validator_success_pos_bound (parse_nlist off p) (reveal v') pos;
      intro_trade
        (vmatch 1.0R x_val (List.Tot.hd (Ghost.reveal l)) **
         mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (Ghost.reveal l)))
        (mixed_list_match_n vmatch p off n pm (Base (Serialized #t sp count pl)) (Ghost.reveal l))
        (trade (vmatch 1.0R x_val (List.Tot.hd (Ghost.reveal l)))
              (pts_to_parsed_strong_prefix p pl_suffix #((pm *. sp) /. 2.0R) (List.Tot.hd (Ghost.reveal l))) **
         S.pts_to pl_prefix #((pm *. sp) /. 2.0R) v_prefix **
         S.is_split pl pl_prefix pl_suffix)
        fn _ {
          rewrite (S.pts_to pl_prefix #((pm *. sp) /. 2.0R) v_prefix)
            as (S.pts_to pl_prefix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') 0 (SZ.v pos)));
          serialized_next_trade_body vmatch p off n sp count pm
            pl pl_prefix pl_suffix v' l x_val pos
            () () () ();
        };
      fold (mixed_list_next_n_post vmatch p off n pm (Base (Serialized #t sp count pl)) (Ghost.reveal l) x_val);
      rewrite each (Serialized #t sp count pl) as bi;
      x_val
      }}
    }
  }
}
```

#pop-options

let iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (l: list u)
: Tot slprop
= match i with
  | IBase bi ->
      base_mixed_list_match vmatch p pm bi l
  | IPair bi ml ->
      exists* l1 l2.
        base_mixed_list_match vmatch p pm bi l1 **
        mixed_list_match     vmatch p pm ml l2 **
        pure (
          l == List.Tot.append l1 l2 /\
          (base_mixed_list_length bi == 0sz ==> mixed_list_length ml == 0sz)
        )


#push-options "--z3rlimit 4000 --fuel 2 --ifuel 1"

inline_for_extraction
```pulse
fn iterator_start
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (pm: perm) (ml: mixed_list t) (l: Ghost.erased (list u))
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
requires
  mixed_list_match vmatch p pm ml l
returns it: iterator t
ensures exists* pm'.
  iterator_match vmatch p pm' it l **
  trade (iterator_match vmatch p pm' it l)
       (mixed_list_match vmatch p pm ml l)
{
  let total_sz = mixed_list_length ml;
  unfold (mixed_list_match vmatch p pm ml l);
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml l)
    as (mixed_list_match_n vmatch p 0 (SZ.v total_sz) pm ml l);
  if (SZ.eq total_sz 0sz) {
    // Empty: return IBase (Empty #t)
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v total_sz) pm ml l)
      as (mixed_list_match_n vmatch p 0 0 pm ml l);
    mixed_list_match_n_length vmatch p 0 0 pm ml l;
    // l == []
    fold (base_mixed_list_match_n vmatch p 0 0 pm (Empty #t) (Ghost.reveal l));
    rewrite (base_mixed_list_match_n vmatch p 0 0 pm (Empty #t) (Ghost.reveal l))
      as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Empty #t))) pm (Empty #t) (Ghost.reveal l));
    fold (base_mixed_list_match vmatch p pm (Empty #t) (Ghost.reveal l));
    fold (iterator_match vmatch p pm (IBase #t (Empty #t)) (Ghost.reveal l));
    // Trade: iterator_match → mixed_list_match
    intro (iterator_match vmatch p pm (IBase #t (Empty #t)) (Ghost.reveal l) @==>
           mixed_list_match vmatch p pm ml l)
      #(mixed_list_match_n vmatch p 0 0 pm ml l)
      fn _ {
        unfold (iterator_match vmatch p pm (IBase #t (Empty #t)) (Ghost.reveal l));
        drop_ (base_mixed_list_match vmatch p pm (Empty #t) (Ghost.reveal l));
        rewrite (mixed_list_match_n vmatch p 0 0 pm ml l)
          as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml l);
        fold (mixed_list_match vmatch p pm ml l);
      };
    rewrite each (Ghost.reveal l) as l;
    IBase #t (Empty #t)
  } else {
    // Non-empty: share, extract first base, narrow the rest
    // Step 1: Share → two copies at pm/2
    mixed_list_match_n_length vmatch p 0 (SZ.v total_sz) pm ml l;
    mixed_list_match_n_share vmatch p 0 (SZ.v total_sz) pm ml l vmatch_share;
    // Step 2: Extract first base from copy 1
    let res = mixed_list_extract_first_base_loop vmatch p j
      0 (SZ.v total_sz)
      0sz total_sz
      (pm /. 2.0R) ml l;
    let bi' = fst res;
    let len_sz = snd res;
    rewrite (
      (let (bi'', len'') = res in
       base_mixed_list_match vmatch p (pm /. 2.0R) bi'' (list_narrow l 0 (SZ.v len'')) **
       trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi'' (list_narrow l 0 (SZ.v len'')))
            (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l) **
       pure (SZ.v len'' == SZ.v (base_mixed_list_length bi'') /\ SZ.v len'' > 0 /\ SZ.v len'' <= SZ.v total_sz)))
      as (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (list_narrow l 0 (SZ.v len_sz)) **
          trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (list_narrow l 0 (SZ.v len_sz)))
               (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l) **
          pure (SZ.v len_sz == SZ.v (base_mixed_list_length bi') /\ SZ.v len_sz > 0 /\ SZ.v len_sz <= SZ.v total_sz));
    // Step 3: Narrow copy 2 to get the rest
    let rest_sz = SZ.sub total_sz len_sz;
    let rest = mixed_list_narrow_n vmatch p j
      0 (SZ.v total_sz)
      (pm /. 2.0R) ml l
      len_sz rest_sz
      vmatch_share vmatch_gather;
    let l_head : Ghost.erased (list u) = list_narrow l 0 (SZ.v len_sz);
    let l_tail : Ghost.erased (list u) = list_narrow l (SZ.v len_sz) (SZ.v rest_sz);
    rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) rest (list_narrow l (SZ.v len_sz - 0) (SZ.v rest_sz)))
      as (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail));
    rewrite (trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) rest (list_narrow l (SZ.v len_sz - 0) (SZ.v rest_sz)))
                   (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l))
      as (trade (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail))
               (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l));
    // Step 4: Share base match → two copies at pm/4
    rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (list_narrow l 0 (SZ.v len_sz)))
      as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) bi' (Ghost.reveal l_head));
    rewrite (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (list_narrow l 0 (SZ.v len_sz)))
                   (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l))
      as (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head))
               (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l));
    base_mixed_list_match_n_share vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R) bi' (Ghost.reveal l_head) vmatch_share;
    rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R /. 2.0R) bi' (Ghost.reveal l_head))
      as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' (Ghost.reveal l_head));
    rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 2.0R /. 2.0R) bi' (Ghost.reveal l_head))
      as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' (Ghost.reveal l_head));
    // Step 5: Fold iterator_match at pm/4
    rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' (Ghost.reveal l_head))
      as (base_mixed_list_match vmatch p (pm /. 4.0R) bi' (Ghost.reveal l_head));
    list_narrow_split (Ghost.reveal l) (SZ.v len_sz);
    fold (iterator_match vmatch p (pm /. 4.0R) (IPair #t bi' rest) (Ghost.reveal l));
    // Step 6: Build trade
    intro (iterator_match vmatch p (pm /. 4.0R) (IPair #t bi' rest) (Ghost.reveal l) @==>
           mixed_list_match vmatch p pm ml l)
      #(base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' (Ghost.reveal l_head) **
        trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head))
             (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l) **
        trade (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail))
             (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l))
      fn _ {
        // Unfold iterator_match (IPair case)
        unfold (iterator_match vmatch p (pm /. 4.0R) (IPair #t bi' rest) (Ghost.reveal l));
        with l1 l2 . assert (
          base_mixed_list_match vmatch p (pm /. 4.0R) bi' l1 **
          mixed_list_match vmatch p (pm /. 4.0R) rest l2 **
          pure (Ghost.reveal l == List.Tot.append l1 l2)
        );
        // Gather base: spare (pm/4) + from iterator (pm/4) → pm/2
        rewrite (base_mixed_list_match vmatch p (pm /. 4.0R) bi' l1)
          as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' l1);
        base_mixed_list_match_n_gather vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) (pm /. 4.0R) bi' l1 (Ghost.reveal l_head) vmatch_gather;
        rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) ((pm /. 4.0R) +. (pm /. 4.0R)) bi' l1)
          as (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head));
        // Elim extract trade: base_mixed_list_match (pm/2) → copy 1
        Trade.elim
          (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head))
          (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l);
        // Elim narrow trade: mixed_list_match (pm/4) rest → copy 2
        // l2 == l_tail by append injectivity
        list_narrow_split (Ghost.reveal l) (SZ.v len_sz);
        List.Tot.Properties.append_length_inv_head l1 l2 (Ghost.reveal l_head) (Ghost.reveal l_tail);
        rewrite (mixed_list_match vmatch p (pm /. 4.0R) rest l2)
          as (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail));
        Trade.elim
          (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail))
          (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l);
        // Gather two copies → full match
        mixed_list_match_n_gather vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) (pm /. 2.0R) ml l l vmatch_gather;
        rewrite (mixed_list_match_n vmatch p 0 (SZ.v total_sz) ((pm /. 2.0R) +. (pm /. 2.0R)) ml l)
          as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) ((pm /. 2.0R) +. (pm /. 2.0R)) ml l);
        fold (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml l);
        rewrite (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) ml l)
          as (mixed_list_match vmatch p pm ml l);
      };
    rewrite each (Ghost.reveal l) as l;
    IPair #t bi' rest
  }
}
```

#pop-options

noeq
type elt_or_serialized ([@@@strictly_positive] elt: Type) =
| EElement of elt
| ESerialized of S.slice U8.t

let elt_or_serialized_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: elt_or_serialized t)
  (y: u)
: Tot slprop
= match i with
  | EElement x -> vmatch pm x y
  | ESerialized pl ->
    pts_to_parsed (p) pl #pm y

// ===== iterator_next_eos =====
// Variant of iterator_next that returns elt_or_serialized, using elt_or_serialized_match
// instead of vmatch, and does not require zero_copy_parse_strong_prefix.

let mixed_list_next_n_eos_post
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off: Ghost.erased nat) (n: Ghost.erased nat) (pm: perm) (i: mixed_list t) (l: list u)
  (res: elt_or_serialized t)
: Tot slprop
= exists* pm_v hd_val tl_val .
    elt_or_serialized_match vmatch p pm_v res hd_val **
    mixed_list_match_n vmatch p (Ghost.reveal off + 1) (nat_pred (Ghost.reveal n)) (pm /. 2.0R) i tl_val **
    trade
      (elt_or_serialized_match vmatch p pm_v res hd_val **
       mixed_list_match_n vmatch p (Ghost.reveal off + 1) (nat_pred (Ghost.reveal n)) (pm /. 2.0R) i tl_val)
      (mixed_list_match_n vmatch p (Ghost.reveal off) (Ghost.reveal n) pm i l) **
    pure (Ghost.reveal n > 0 /\ l == hd_val :: tl_val)

let iterator_next_eos_post
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm) (r: R.ref (iterator t)) (i_orig: iterator t) (l: list u)
  (res: elt_or_serialized t)
: Tot slprop
= exists* pm_v hd_val tl_l it' pm' .
    elt_or_serialized_match vmatch p pm_v res hd_val **
    R.pts_to r it' **
    iterator_match vmatch p pm' it' tl_l **
    trade
      (elt_or_serialized_match vmatch p pm_v res hd_val **
       iterator_match vmatch p pm' it' tl_l)
      (iterator_match vmatch p pm i_orig l) **
    pure (l == hd_val :: tl_l)

// Ghost fn: trade body for Serialized case in eos variant.
// Recovers the original mixed_list_match_n from pts_to_parsed (instead of vmatch).
#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

```pulse
ghost fn serialized_eos_next_trade_body
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n: nat)
  (sp: perm) (count: SZ.t) (pm: perm)
  (pl pl_prefix pl_suffix pl_head pl_rest: S.slice byte)
  (v': Ghost.erased (Seq.seq byte))
  (l: Ghost.erased (list u))
  (v_rest: Ghost.erased (Seq.seq byte))
  (pos: SZ.t)
  (consumed_sz: SZ.t)
  (sq_pos_bound: squash (SZ.v pos <= Seq.length (reveal v')))
  (sq_n: squash (n > 0 /\ Cons? (reveal l)))
  (sq_validator: squash (LPS.validator_success (parse_nlist off p) 0sz (reveal v') pos))
  (sq_strong: squash (k.parser_kind_subkind == Some ParserStrong))
  (sq_consumed: squash (LPS.validator_success p 0sz (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) consumed_sz))
requires
  elt_or_serialized_match vmatch p ((pm *. sp) /. 2.0R) (ESerialized pl_head) (List.Tot.hd (reveal l)) **
  mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (reveal l)) **
  S.pts_to pl_rest #((pm *. sp) /. 2.0R) v_rest **
  S.is_split pl_suffix pl_head pl_rest **
  S.pts_to pl_prefix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') 0 (SZ.v pos)) **
  S.is_split pl pl_prefix pl_suffix
ensures
  mixed_list_match_n vmatch p off n pm (Base (Serialized #t sp count pl)) (reveal l)
{
  // Step 1: Unfold elt_or_serialized_match to get pts_to_parsed
  rewrite (elt_or_serialized_match vmatch p ((pm *. sp) /. 2.0R) (ESerialized pl_head) (List.Tot.hd (reveal l)))
    as (pts_to_parsed p pl_head #((pm *. sp) /. 2.0R) (List.Tot.hd (reveal l)));
  // Now we have: pts_to_parsed p pl_head #((pm *. sp) /. 2.0R) (hd l)

  // Step 2: Unfold pts_to_parsed to get raw bytes
  unfold (pts_to_parsed p pl_head #((pm *. sp) /. 2.0R) (List.Tot.hd (reveal l)));
  with w_head. assert (S.pts_to pl_head #((pm *. sp) /. 2.0R) w_head);

  // Capture lengths before consuming pts_to
  S.pts_to_len pl_head;

  // Step 3: Join pl_head + pl_rest → pl_suffix
  S.join pl_head pl_rest pl_suffix;
  // Now: S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.append w_head v_rest)

  // Step 4: Unfold tail mixed_list_match_n to reach S.pts_to pl at half perm
  unfold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (reveal l)));
  unfold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Serialized #t sp count pl) (List.Tot.tl (reveal l)));
  with l_all'. assert (pts_to_parsed_strong_prefix (parse_nlist ((off + 1) + nat_pred n) p) pl #((pm /. 2.0R) *. sp) l_all');
  rewrite (pts_to_parsed_strong_prefix (parse_nlist ((off + 1) + nat_pred n) p) pl #((pm /. 2.0R) *. sp) l_all')
    as (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all');
  unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all');
  with v_tail. assert (S.pts_to pl #((pm *. sp) /. 2.0R) v_tail);

  // Step 5: Join pl_prefix + pl_suffix → pl at half perm
  S.join pl_prefix pl_suffix pl;
  // Now: S.pts_to pl #((pm *. sp) /. 2.0R) (Seq.append (Seq.slice v' 0 pos) (Seq.append w_head v_rest))

  // Step 6: Gather two halves of pl
  S.gather pl;
  // Now: S.pts_to pl #((pm*sp)/2 + (pm*sp)/2) v_g ** pure (v_tail == Seq.append ...)

  // Step 7: Establish lemma preconditions
  // w_head has pts_to_parsed_prop, i.e., parse p w_head = Some (hd l, |w_head|)
  // Using parse_strong_prefix: parse p (append w_head v_rest) = Some (hd l, |w_head|)
  let v_suffix_joined = Seq.append w_head (reveal v_rest);
  parse_strong_prefix p w_head v_suffix_joined;
  // Now we have pts_to_parsed_strong_prefix_prop p v_suffix_joined (hd l)

  // Derive the original v' structure
  parser_kind_prop_equiv (parse_nlist_kind off k) (parse_nlist off p);
  Seq.lemma_eq_intro (Seq.slice (reveal v') 0 (Seq.length (reveal v'))) (reveal v');
  parse_strong_prefix (parse_nlist off p) (reveal v') (Seq.slice (reveal v') 0 (SZ.v pos));
  parse_nlist_splitAt_hd_full_lemma p off n (off + n) (reveal v_tail) l_all' (reveal l) (Seq.slice (reveal v') 0 (SZ.v pos)) v_suffix_joined (List.Tot.hd (reveal l));

  // Step 8: Fold back with l_all' and v_tail
  with v_g. assert (S.pts_to pl #((pm *. sp) /. 2.0R +. (pm *. sp) /. 2.0R) v_g);
  rewrite (S.pts_to pl #((pm *. sp) /. 2.0R +. (pm *. sp) /. 2.0R) v_g)
    as (S.pts_to pl #(pm *. sp) v_g);
  rewrite (S.pts_to pl #(pm *. sp) v_g)
    as (S.pts_to pl #(pm *. sp) (reveal v_tail));
  fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all');
  fold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l));
  fold (mixed_list_match_n vmatch p off n pm (Base (Serialized #t sp count pl)) (reveal l));
}
```

#pop-options

#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction
```pulse
fn base_mixed_list_next_n_eos
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off: Ghost.erased nat) (n: Ghost.erased nat { Ghost.reveal n > 0 })
  (off_sz: SZ.t { SZ.v off_sz == Ghost.reveal off }) (n_sz: SZ.t { SZ.v n_sz == Ghost.reveal n })
  (pm: perm) (bi: base_mixed_list t) (l: Ghost.erased (list u))
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
  (j: LPS.jumper p)
requires
  base_mixed_list_match_n vmatch p off n pm bi (Ghost.reveal l)
returns res: elt_or_serialized t
ensures
  mixed_list_next_n_eos_post vmatch p off n pm (Base bi) (Ghost.reveal l) res
{
  match bi {
    Empty -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Empty #t) (Ghost.reveal l));
      unreachable ()
    }
    Singleton sp sv s -> {
      base_mixed_list_match_n_singleton_unfold_pos vmatch p off n pm sp sv s (Ghost.reveal l) ();
      with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y **
        pure (Ghost.reveal l == [y] /\ off == 0 /\ n == 1));
      let x_val = R.read s;
      // Fold 0-case at pm/2
      fold (base_mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Singleton #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
      fold (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
      rewrite (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)))
        as (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
      rewrite each x as x_val;
      rewrite (vmatch (pm *. sv) x_val y)
        as (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)));
      let res : elt_or_serialized t = EElement x_val;
      rewrite (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)))
        as (elt_or_serialized_match vmatch p (pm *. sv) res (List.Tot.hd (Ghost.reveal l)));
      intro (elt_or_serialized_match vmatch p (pm *. sv) res (List.Tot.hd (Ghost.reveal l)) **
             mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l))
             @==>
             mixed_list_match_n vmatch p off n pm (Base (Singleton #t sp sv s)) (Ghost.reveal l))
        #(pts_to s #(pm *. sp) x_val **
          pure (Ghost.reveal l == [y] /\ off == 0 /\ n == 1))
        fn _ {
          rewrite (elt_or_serialized_match vmatch p (pm *. sv) res (List.Tot.hd (Ghost.reveal l)))
            as (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)));
          rewrite (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)))
            as (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
          unfold (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base (Singleton #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
          unfold (base_mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Singleton #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
          drop_ (pure (Nil? (List.Tot.tl (Ghost.reveal l)) /\ 1 <= 1));
          rewrite (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)))
            as (vmatch (pm *. sv) x_val y);
          base_mixed_list_match_n_singleton_fold_pos vmatch p off n pm sp sv s (Ghost.reveal l) ();
          fold (mixed_list_match_n vmatch p off n pm (Base (Singleton #t sp sv s)) (Ghost.reveal l));
        };
      fold (mixed_list_next_n_eos_post vmatch p off n pm (Base (Singleton #t sp sv s)) (Ghost.reveal l) res);
      rewrite each (Singleton #t sp sv s) as bi;
      res
    }
    Slice sp sv s -> {
      unfold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) (Ghost.reveal l));
      with l' sl1. assert (S.pts_to s #(pm *. sp) l' ** SM.seq_list_match sl1 (Ghost.reveal l) (vmatch (pm *. sv)));
      S.pts_to_len s;
      SM.seq_list_match_length (vmatch (pm *. sv)) sl1 (Ghost.reveal l);
      let x_val = S.op_Array_Access s off_sz;
      SMU.seq_list_match_cons_elim_trade sl1 (Ghost.reveal l) (vmatch (pm *. sv));
      S.share s;
      rewrite (S.pts_to s #((pm *. sp) /. 2.0R) l') as (S.pts_to s #((pm /. 2.0R) *. sp) l');
      rewrite (S.pts_to s #((pm *. sp) /. 2.0R) l') as (S.pts_to s #((pm /. 2.0R) *. sp) l');
      ghost fn share_prf_eos
        (c': t)
        (v': u { v' << List.Tot.tl (Ghost.reveal l) })
      requires vmatch (pm *. sv) c' v'
      ensures vmatch ((pm /. 2.0R) *. sv) c' v' ** vmatch ((pm /. 2.0R) *. sv) c' v'
      {
        vmatch_share c' #(pm *. sv) #v';
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
        rewrite (vmatch ((pm *. sv) /. 2.0R) c' v') as (vmatch ((pm /. 2.0R) *. sv) c' v');
      };
      seq_list_match_share (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l))
        (vmatch (pm *. sv))
        (vmatch ((pm /. 2.0R) *. sv))
        share_prf_eos;
      Seq.lemma_index_slice l' off (off + n) 0;
      assert (pure (Seq.head sl1 == Seq.index l' off));
      fold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Slice #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
      fold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Slice #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
      rewrite (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)))
        as (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)));
      let res : elt_or_serialized t = EElement x_val;
      rewrite (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)))
        as (elt_or_serialized_match vmatch p (pm *. sv) res (List.Tot.hd (Ghost.reveal l)));
      intro (elt_or_serialized_match vmatch p (pm *. sv) res (List.Tot.hd (Ghost.reveal l)) **
             mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Slice #t sp sv s)) (List.Tot.tl (Ghost.reveal l))
             @==>
             mixed_list_match_n vmatch p off n pm (Base (Slice #t sp sv s)) (Ghost.reveal l))
        #(trade
            (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)) **
             SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch (pm *. sv)))
            (SM.seq_list_match sl1 (Ghost.reveal l) (vmatch (pm *. sv))) **
          S.pts_to s #((pm /. 2.0R) *. sp) l' **
          SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)) **
          pure (off + n <= Seq.length l' /\ sl1 == Seq.slice l' off (off + n)) **
          pure (Seq.head sl1 == Seq.index l' off))
        fn _ {
          rewrite (elt_or_serialized_match vmatch p (pm *. sv) res (List.Tot.hd (Ghost.reveal l)))
            as (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)));
          rewrite (S.pts_to s #((pm /. 2.0R) *. sp) l') as (S.pts_to s #((pm *. sp) /. 2.0R) l');
          rewrite (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          unfold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Slice #t sp sv s)) (List.Tot.tl (Ghost.reveal l)));
          unfold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Slice #t sp sv s) (List.Tot.tl (Ghost.reveal l)));
          with l'2 sl1_2. assert (
            S.pts_to s #((pm /. 2.0R) *. sp) l'2 **
            SM.seq_list_match sl1_2 (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv))
          );
          rewrite (S.pts_to s #((pm /. 2.0R) *. sp) l'2) as (S.pts_to s #((pm *. sp) /. 2.0R) l'2);
          S.gather s;
          rewrite (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)));
          rewrite (SM.seq_list_match sl1_2 (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)));
          ghost fn gather_prf_eos
            (c': t) (v1': u { v1' << List.Tot.tl (Ghost.reveal l) }) (v2': u { v2' << List.Tot.tl (Ghost.reveal l) /\ List.Tot.memP v2' (List.Tot.tl (Ghost.reveal l)) })
          requires vmatch ((pm *. sv) /. 2.0R) c' v1' ** vmatch ((pm *. sv) /. 2.0R) c' v2'
          ensures vmatch (pm *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
          {
            vmatch_gather c' #((pm *. sv) /. 2.0R) #v1' #((pm *. sv) /. 2.0R) #v2';
            rewrite (vmatch ((pm *. sv) /. 2.0R +. (pm *. sv) /. 2.0R) c' v1') as (vmatch (pm *. sv) c' v1');
          };
          rewrite (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          rewrite (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch ((pm *. sv) /. 2.0R)));
          seq_list_match_gather_memP (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (List.Tot.tl (Ghost.reveal l))
            (vmatch ((pm *. sv) /. 2.0R))
            (vmatch ((pm *. sv) /. 2.0R))
            (vmatch (pm *. sv))
            gather_prf_eos;
          drop_ (pure (List.Tot.tl (Ghost.reveal l) == List.Tot.tl (Ghost.reveal l)));
          drop_ (pure (l' == l'2));
          drop_ (pure ((off + 1) + nat_pred n <= Seq.length l'2 /\ sl1_2 == Seq.slice l'2 (off + 1) (off + 1 + nat_pred n)));
          drop_ (pure (off + n <= Seq.length l' /\ sl1 == Seq.slice l' off (off + n)));
          drop_ (pure (Seq.head sl1 == Seq.index l' off));
          rewrite (vmatch (pm *. sv) x_val (List.Tot.hd (Ghost.reveal l)))
            as (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)));
          elim_trade
            (vmatch (pm *. sv) (Seq.head sl1) (List.Tot.hd (Ghost.reveal l)) **
             SM.seq_list_match (Seq.tail sl1) (List.Tot.tl (Ghost.reveal l)) (vmatch (pm *. sv)))
            (SM.seq_list_match sl1 (Ghost.reveal l) (vmatch (pm *. sv)));
          rewrite (S.pts_to s #((pm *. sp) /. 2.0R +. (pm *. sp) /. 2.0R) l') as (S.pts_to s #(pm *. sp) l');
          fold (base_mixed_list_match_n vmatch p off n pm (Slice #t sp sv s) (Ghost.reveal l));
          fold (mixed_list_match_n vmatch p off n pm (Base (Slice #t sp sv s)) (Ghost.reveal l));
        };
      fold (mixed_list_next_n_eos_post vmatch p off n pm (Base (Slice #t sp sv s)) (Ghost.reveal l) res);
      rewrite each (Slice #t sp sv s) as bi;
      res
    }
    Serialized sp count pl -> {
      // Parse element from serialized bytes at position off
      unfold (base_mixed_list_match_n vmatch p off n pm (Serialized #t sp count pl) (Ghost.reveal l));
      with l_all. assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      with v'. assert (S.pts_to pl #(pm *. sp) v');
      // Share S.pts_to
      S.share pl;
      // FIRST: use one half to jump to position off and parse head
      S.pts_to_len pl;
      parse_nlist_sum p off n (reveal v');
      intro_pure (LPS.jumper_pre' (parse_nlist off p) 0sz v') ();
      let pos = LPV.jump_nlist j off_sz pl 0sz;
      let pl_p = S.split pl pos;
      match pl_p {
        pl_prefix, pl_suffix -> {
      with v_prefix. assert (S.pts_to pl_prefix #((pm *. sp) /. 2.0R) v_prefix);
      with v_suffix. assert (S.pts_to pl_suffix #((pm *. sp) /. 2.0R) v_suffix);
      S.pts_to_len pl_suffix;
      // Establish length l == n
      List.Tot.Base.lemma_splitAt_snd_length off l_all;
      // Establish strong prefix prop for suffix
      pts_to_parsed_strong_prefix_prop_nlist_suffix p off n (reveal v') l_all (Ghost.reveal l) pos;
      assert (pure (pts_to_parsed_strong_prefix_prop (parse_nlist n p) (reveal v_suffix) (Ghost.reveal l)));
      pts_to_parsed_strong_prefix_nlist_hd p n (reveal v_suffix) (Ghost.reveal l);
      // Jump on pl_suffix to find consumed bytes for the first element
      Seq.lemma_eq_intro (Seq.slice (reveal v_suffix) 0 (Seq.length (reveal v_suffix))) (reveal v_suffix);
      intro_pure (LPS.jumper_pre' p 0sz v_suffix) ();
      let consumed_sz = j pl_suffix 0sz;
      // Split pl_suffix at consumed_sz into pl_head (first element) and pl_rest
      validator_success_pos_bound p (reveal v_suffix) consumed_sz;
      let pl_hd_p = S.split pl_suffix consumed_sz;
      match pl_hd_p {
        pl_head, pl_rest -> {
      with v_head. assert (S.pts_to pl_head #((pm *. sp) /. 2.0R) v_head);
      with v_rest. assert (S.pts_to pl_rest #((pm *. sp) /. 2.0R) v_rest);
      // Establish pts_to_parsed_prop p v_head (hd l)
      // We have: pts_to_parsed_strong_prefix_prop p v_suffix (hd l)
      //   → parse p v_suffix = Some (hd l, consumed) with consumed = SZ.v consumed_sz
      // v_head = Seq.slice v_suffix 0 consumed_sz
      // parse_strong_prefix p v_suffix v_head gives parse p v_head = Some (hd l, consumed)
      // And consumed = Seq.length v_head, so pts_to_parsed_prop p v_head (hd l)
      S.pts_to_len pl_head;
      parse_strong_prefix p (reveal v_suffix) (reveal v_head);
      assert (pure (pts_to_parsed_prop p (reveal v_head) (List.Tot.hd (Ghost.reveal l))));
      // Fold pts_to_parsed
      fold (pts_to_parsed p pl_head #((pm *. sp) /. 2.0R) (List.Tot.hd (Ghost.reveal l)));
      // Rewrite pts_to_parsed into elt_or_serialized_match
      let res : elt_or_serialized t = ESerialized pl_head;
      rewrite (pts_to_parsed p pl_head #((pm *. sp) /. 2.0R) (List.Tot.hd (Ghost.reveal l)))
        as (elt_or_serialized_match vmatch p ((pm *. sp) /. 2.0R) res (List.Tot.hd (Ghost.reveal l)));
      // SECOND: fold the other half into tail mixed_list_match_n
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all);
      rewrite (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm *. sp) /. 2.0R) l_all)
        as (pts_to_parsed_strong_prefix (parse_nlist ((off + 1) + nat_pred n) p) pl #((pm /. 2.0R) *. sp) l_all);
      List.Tot.Base.lemma_splitAt_snd_length off l_all;
      lemma_splitAt_tl_snd off l_all;
      assert (pure (List.Tot.tl (Ghost.reveal l) == snd (List.Tot.splitAt (off + 1) l_all) /\ (off + 1) + nat_pred n <= SZ.v count));
      fold (base_mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Serialized #t sp count pl) (List.Tot.tl (Ghost.reveal l)));
      fold (mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (Ghost.reveal l)));
      // Build the trade
      validator_success_pos_bound (parse_nlist off p) (reveal v') pos;
      intro_trade
        (elt_or_serialized_match vmatch p ((pm *. sp) /. 2.0R) res (List.Tot.hd (Ghost.reveal l)) **
         mixed_list_match_n vmatch p (off + 1) (nat_pred n) (pm /. 2.0R) (Base (Serialized #t sp count pl)) (List.Tot.tl (Ghost.reveal l)))
        (mixed_list_match_n vmatch p off n pm (Base (Serialized #t sp count pl)) (Ghost.reveal l))
        (S.pts_to pl_rest #((pm *. sp) /. 2.0R) v_rest **
         S.is_split pl_suffix pl_head pl_rest **
         S.pts_to pl_prefix #((pm *. sp) /. 2.0R) v_prefix **
         S.is_split pl pl_prefix pl_suffix)
        fn _ {
          rewrite (S.pts_to pl_prefix #((pm *. sp) /. 2.0R) v_prefix)
            as (S.pts_to pl_prefix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') 0 (SZ.v pos)));
          rewrite (elt_or_serialized_match vmatch p ((pm *. sp) /. 2.0R) res (List.Tot.hd (Ghost.reveal l)))
            as (elt_or_serialized_match vmatch p ((pm *. sp) /. 2.0R) (ESerialized pl_head) (List.Tot.hd (Ghost.reveal l)));
          serialized_eos_next_trade_body vmatch p off n sp count pm
            pl pl_prefix pl_suffix pl_head pl_rest v' l v_rest pos consumed_sz
            () () () () ();
        };
      fold (mixed_list_next_n_eos_post vmatch p off n pm (Base (Serialized #t sp count pl)) (Ghost.reveal l) res);
      rewrite each (Serialized #t sp count pl) as bi;
      res
      }}
      }}
    }
  }
}
```

#pop-options

#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction
```pulse
fn iterator_next_eos
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (pm: perm) (r: R.ref (iterator t)) (i_orig: Ghost.erased (iterator t)) (l: Ghost.erased (list u))
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
requires
  R.pts_to r (Ghost.reveal i_orig) ** iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l) ** pure (Cons? (Ghost.reveal l))
returns res: elt_or_serialized t
ensures
  iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) res
{
  let i = R.read r;
  rewrite (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l))
    as (iterator_match vmatch p pm i (Ghost.reveal l));
  match i {
    IBase bi -> {
      rewrite each i as (IBase #t bi);
      unfold (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l));
      // Now we have just: base_mixed_list_match vmatch p pm bi l
      let len_sz = base_mixed_list_length bi;
      base_mixed_list_match_length vmatch p pm bi (Ghost.reveal l);
      if (SZ.eq len_sz 0sz) {
        // l == [], contradicting Cons? l
        unreachable ()
      } else {
      rewrite (base_mixed_list_match vmatch p pm bi (Ghost.reveal l))
        as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi)) pm bi (Ghost.reveal l));
      rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi)) pm bi (Ghost.reveal l))
        as (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm bi (Ghost.reveal l));
      let x = base_mixed_list_next_n_eos vmatch p 0 (SZ.v len_sz) 0sz len_sz pm bi l
        vmatch_share vmatch_gather j;
      unfold (mixed_list_next_n_eos_post vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l) x);
      with pm_v hd_val tl_val . assert (
        elt_or_serialized_match vmatch p pm_v x hd_val **
        mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val **
        trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
          (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l)) **
        pure (SZ.v len_sz > 0 /\ Ghost.reveal l == hd_val :: tl_val)
      );
      if (SZ.eq len_sz 1sz) {
        // Case len == 1: result iterator is IBase Empty
        rewrite (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
          as (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base bi) tl_val);
        mixed_list_match_n_length vmatch p 1 0 (pm /. 2.0R) (Base bi) (Ghost.reveal tl_val);
        // Build iterator_match (IBase Empty) directly = base_mixed_list_match Empty tl_val
        fold (base_mixed_list_match_n vmatch p 0 0 (pm /. 2.0R) (Empty #t) (Ghost.reveal tl_val));
        rewrite (base_mixed_list_match_n vmatch p 0 0 (pm /. 2.0R) (Empty #t) (Ghost.reveal tl_val))
          as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Empty #t))) (pm /. 2.0R) (Empty #t) (Ghost.reveal tl_val));
        fold (base_mixed_list_match vmatch p (pm /. 2.0R) (Empty #t) (Ghost.reveal tl_val));
        fold (iterator_match vmatch p (pm /. 2.0R) (IBase #t (Empty #t)) (Ghost.reveal tl_val));
        R.write r (IBase #t (Empty #t));
        // Build composite trade
        intro_trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           iterator_match vmatch p (pm /. 2.0R) (IBase #t (Empty #t)) (Ghost.reveal tl_val))
          (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l))
          (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base bi) tl_val **
           trade (elt_or_serialized_match vmatch p pm_v x hd_val **
                  mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
                 (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l)))
          fn _ {
            // it_new = IBase (Empty), iterator_match → base_mixed_list_match Empty tl_val
            unfold (iterator_match vmatch p (pm /. 2.0R) (IBase #t (Empty #t)) (Ghost.reveal tl_val));
            drop_ (base_mixed_list_match vmatch p (pm /. 2.0R) (Empty #t) (Ghost.reveal tl_val));
            rewrite (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base bi) tl_val)
              as (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val);
            elim_trade
              (elt_or_serialized_match vmatch p pm_v x hd_val **
               mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
              (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l));
            unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l));
            rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm bi (Ghost.reveal l))
              as (base_mixed_list_match vmatch p pm bi (Ghost.reveal l));
            fold (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l));
          };
        rewrite (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) (IBase #t (Empty #t)) (Ghost.reveal tl_val))
                       (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l)))
          as (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) (IBase #t (Empty #t)) (Ghost.reveal tl_val))
                    (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
        fold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
        x
      } else {
        // Case len > 1 (IBase): narrow tail base, result iterator is IBase bi_tail
        mixed_list_match_n_length vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) (Ghost.reveal tl_val);
        unfold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val);
        let n_tail_sz = SZ.sub len_sz 1sz;
        rewrite (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) bi tl_val)
          as (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val);
        let bi_tail = base_mixed_list_narrow_n vmatch p j 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val 1sz n_tail_sz;
        FStar.List.Pure.Properties.splitAt_length_total (Ghost.reveal tl_val);
        rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
          as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
        rewrite (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
                       (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val))
          as (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
                   (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val));
        // Form new iterator IBase bi_tail
        fold (iterator_match vmatch p (pm /. 2.0R) (IBase #t bi_tail) (Ghost.reveal tl_val));
        R.write r (IBase #t bi_tail);
        // Build composite trade
        intro_trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           iterator_match vmatch p (pm /. 2.0R) (IBase #t bi_tail) (Ghost.reveal tl_val))
          (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l))
          (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
                (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val) **
           trade (elt_or_serialized_match vmatch p pm_v x hd_val **
                  mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
                 (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l)))
          fn _ {
            // it_new = IBase bi_tail: iterator_match → base_mixed_list_match bi_tail tl_val
            unfold (iterator_match vmatch p (pm /. 2.0R) (IBase #t bi_tail) (Ghost.reveal tl_val));
            // Elim narrow trade
            elim_trade
              (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
              (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val);
            rewrite (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val)
              as (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) bi tl_val);
            fold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val);
            // Recover original via next_n trade
            elim_trade
              (elt_or_serialized_match vmatch p pm_v x hd_val **
               mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
              (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l));
            unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l));
            rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm bi (Ghost.reveal l))
              as (base_mixed_list_match vmatch p pm bi (Ghost.reveal l));
            fold (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l));
          };
        rewrite (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) (IBase #t bi_tail) (Ghost.reveal tl_val))
                       (iterator_match vmatch p pm (IBase #t bi) (Ghost.reveal l)))
          as (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) (IBase #t bi_tail) (Ghost.reveal tl_val))
                    (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
        fold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
        x
      }
      }
    }
    IPair bi ml -> {
      rewrite each i as (IPair #t bi ml);
      unfold (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l));
      with l1 l2 . assert (
        base_mixed_list_match vmatch p pm bi l1 **
        mixed_list_match vmatch p pm ml l2 **
        pure (Ghost.reveal l == List.Tot.append l1 l2 /\
              (base_mixed_list_length bi == 0sz ==> mixed_list_length ml == 0sz))
      );
      let len_sz = base_mixed_list_length bi;
      base_mixed_list_match_length vmatch p pm bi (Ghost.reveal l1);
      if (SZ.eq len_sz 0sz) {
        mixed_list_match_length vmatch p pm ml (Ghost.reveal l2);
        unreachable ()
      } else {
      // Call base_mixed_list_next_n_eos
      rewrite (base_mixed_list_match vmatch p pm bi l1)
        as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi)) pm bi l1);
      rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi)) pm bi l1)
        as (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm bi l1);
      let x = base_mixed_list_next_n_eos vmatch p 0 (SZ.v len_sz) 0sz len_sz pm bi l1
        vmatch_share vmatch_gather j;
      unfold (mixed_list_next_n_eos_post vmatch p 0 (SZ.v len_sz) pm (Base bi) (Ghost.reveal l1) x);
      with pm_v hd_val tl_val . assert (
        elt_or_serialized_match vmatch p pm_v x hd_val **
        mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val **
        trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
          (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1) **
        pure (SZ.v len_sz > 0 /\ Ghost.reveal l1 == hd_val :: tl_val)
      );
      if (SZ.eq len_sz 1sz) {
        // Case len == 1: tail is l2, call iterator_start on ml
        rewrite (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
          as (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base bi) tl_val);
        mixed_list_match_n_length vmatch p 1 0 (pm /. 2.0R) (Base bi) (Ghost.reveal tl_val);
        List.Tot.Properties.append_l_nil (Ghost.reveal l2);
        let it_new = iterator_start vmatch p j pm ml l2 vmatch_share vmatch_gather;
        with pm_after . assert (
          iterator_match vmatch p pm_after it_new l2 **
          trade (iterator_match vmatch p pm_after it_new l2)
               (mixed_list_match vmatch p pm ml l2)
        );
        R.write r it_new;
        // Build composite trade
        intro_trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
          (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l))
          (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base bi) tl_val **
           trade (iterator_match vmatch p pm_after it_new l2)
                (mixed_list_match vmatch p pm ml l2) **
           trade (elt_or_serialized_match vmatch p pm_v x hd_val **
                  mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
                 (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1))
          fn _ {
            rewrite (iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
              as (iterator_match vmatch p pm_after it_new l2);
            elim_trade
              (iterator_match vmatch p pm_after it_new l2)
              (mixed_list_match vmatch p pm ml l2);
            rewrite (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base bi) tl_val)
              as (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val);
            elim_trade
              (elt_or_serialized_match vmatch p pm_v x hd_val **
               mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
              (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1);
            unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1);
            rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm bi l1)
              as (base_mixed_list_match vmatch p pm bi l1);
            fold (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l));
          };
        rewrite (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
                       (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l)))
          as (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
                    (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
        fold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
        x
      } else {
        // Case len > 1: narrow the tail base, share after, result IPair bi_tail ml
        mixed_list_match_n_length vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) (Ghost.reveal tl_val);
        unfold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val);
        let n_tail_sz = SZ.sub len_sz 1sz;
        rewrite (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) bi tl_val)
          as (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val);
        let bi_tail = base_mixed_list_narrow_n vmatch p j 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val 1sz n_tail_sz;
        FStar.List.Pure.Properties.splitAt_length_total (Ghost.reveal tl_val);
        rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
          as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
        rewrite (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
                       (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val))
          as (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
                   (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val));
        // Share after
        mixed_list_match_share vmatch p pm ml (Ghost.reveal l2) vmatch_share;
        // Disambiguate the two copies by converting one to mixed_list_match_n form
        rewrite (mixed_list_match vmatch p (pm /. 2.0R) ml (Ghost.reveal l2))
          as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) (pm /. 2.0R) ml (Ghost.reveal l2));
        // Form new iterator IPair bi_tail ml at pm/2
        let tl_l : Ghost.erased (list u) = Ghost.hide (Ghost.reveal tl_val @ Ghost.reveal l2);
        List.Tot.Properties.append_cons_l (Ghost.reveal hd_val) (Ghost.reveal tl_val) (Ghost.reveal l2);
        fold (iterator_match vmatch p (pm /. 2.0R) (IPair #t bi_tail ml) (Ghost.reveal tl_l));
        R.write r (IPair #t bi_tail ml);
        // Build composite trade
        intro_trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           iterator_match vmatch p (pm /. 2.0R) (IPair #t bi_tail ml) (Ghost.reveal tl_l))
          (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l))
          (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) (pm /. 2.0R) ml (Ghost.reveal l2) **
           trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
                (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val) **
           trade (elt_or_serialized_match vmatch p pm_v x hd_val **
                  mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
                 (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1))
          fn _ {
            unfold (iterator_match vmatch p (pm /. 2.0R) (IPair #t bi_tail ml) (Ghost.reveal tl_l));
            with l1' l2' . assert (
              base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail l1' **
              mixed_list_match vmatch p (pm /. 2.0R) ml l2'
            );
            base_mixed_list_match_length vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal l1');
            mixed_list_match_length vmatch p (pm /. 2.0R) ml (Ghost.reveal l2');
            List.Tot.Properties.append_length_inv_head (Ghost.reveal l1') (Ghost.reveal l2') (Ghost.reveal tl_val) (Ghost.reveal l2);
            rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail l1')
              as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
            rewrite (mixed_list_match vmatch p (pm /. 2.0R) ml l2')
              as (mixed_list_match vmatch p (pm /. 2.0R) ml (Ghost.reveal l2));
            // Convert to _n form to gather with spare _n copy
            rewrite (mixed_list_match vmatch p (pm /. 2.0R) ml (Ghost.reveal l2))
              as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) (pm /. 2.0R) ml (Ghost.reveal l2));
            mixed_list_match_n_gather vmatch p 0 (SZ.v (mixed_list_length ml)) (pm /. 2.0R) (pm /. 2.0R) ml (Ghost.reveal l2) (Ghost.reveal l2) vmatch_gather;
            rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) ((pm /. 2.0R) +. (pm /. 2.0R)) ml (Ghost.reveal l2))
              as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml (Ghost.reveal l2));
            fold (mixed_list_match vmatch p pm ml (Ghost.reveal l2));
            rewrite (mixed_list_match vmatch p pm ml (Ghost.reveal l2))
              as (mixed_list_match vmatch p pm ml l2);
            // Recover base_mixed_list_match_n via narrow trade
            elim_trade
              (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
              (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val);
            rewrite (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) bi tl_val)
              as (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) bi tl_val);
            fold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val);
            // Recover original via next_n trade
            elim_trade
              (elt_or_serialized_match vmatch p pm_v x hd_val **
               mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base bi) tl_val)
              (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1);
            unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base bi) l1);
            rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm bi l1)
              as (base_mixed_list_match vmatch p pm bi l1);
            fold (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l));
          };
        rewrite (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) (IPair #t bi_tail ml) (Ghost.reveal tl_l))
                       (iterator_match vmatch p pm (IPair #t bi ml) (Ghost.reveal l)))
          as (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) (IPair #t bi_tail ml) (Ghost.reveal tl_l))
                    (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
        fold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
        x
      }
      }
    }
  }
}
```

#pop-options

let iterator_next_post
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm) (r: R.ref (iterator t)) (i_orig: iterator t) (l: list u)
  (res: t)
: Tot slprop
= exists* pm_v hd_val tl_l it' pm' .
    vmatch pm_v res hd_val **
    R.pts_to r it' **
    iterator_match vmatch p pm' it' tl_l **
    trade
      (vmatch pm_v res hd_val **
       iterator_match vmatch p pm' it' tl_l)
      (iterator_match vmatch p pm i_orig l) **
    pure (l == hd_val :: tl_l)

#push-options "--z3rlimit 8000 --fuel 2 --ifuel 1 --ext no:context_pruning"

inline_for_extraction
```pulse
fn iterator_next
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (pm: perm) (r: R.ref (iterator t)) (i_orig: Ghost.erased (iterator t)) (l: Ghost.erased (list u))
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (zcp: zero_copy_parse (vmatch 1.0R) p)
requires
  R.pts_to r (Ghost.reveal i_orig) ** iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l) ** pure (Cons? (Ghost.reveal l))
returns res: t
ensures
  iterator_next_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) res
{
  let eos_res = iterator_next_eos vmatch p j pm r i_orig l vmatch_share vmatch_gather;
  unfold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) eos_res);
  with pm_v hd_val tl_l it' pm' . assert (
    elt_or_serialized_match vmatch p pm_v eos_res hd_val **
    R.pts_to r it' **
    iterator_match vmatch p pm' it' tl_l **
    trade
      (elt_or_serialized_match vmatch p pm_v eos_res hd_val **
       iterator_match vmatch p pm' it' tl_l)
      (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)) **
    pure (Ghost.reveal l == hd_val :: tl_l)
  );
  match eos_res {
    EElement x -> {
      rewrite (elt_or_serialized_match vmatch p pm_v (EElement x) hd_val)
        as (vmatch pm_v x hd_val);
      rewrite (trade
        (elt_or_serialized_match vmatch p pm_v (EElement x) hd_val **
         iterator_match vmatch p pm' it' tl_l)
        (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)))
        as (trade
          (vmatch pm_v x hd_val **
           iterator_match vmatch p pm' it' tl_l)
          (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
      fold (iterator_next_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
      x
    }
    ESerialized pl -> {
      rewrite (elt_or_serialized_match vmatch p pm_v (ESerialized pl) hd_val)
        as (pts_to_parsed p pl #pm_v hd_val);
      let x = zcp pl #pm_v #hd_val;
      // Rewrite the eos trade to use pts_to_parsed
      rewrite (trade
        (elt_or_serialized_match vmatch p pm_v (ESerialized pl) hd_val **
         iterator_match vmatch p pm' it' tl_l)
        (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)))
        as (trade
          (pts_to_parsed p pl #pm_v hd_val **
           iterator_match vmatch p pm' it' tl_l)
          (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
      // Compose trades: vmatch ==> pts_to_parsed ==> (with iterator_match) ==> iterator_match_orig
      Trade.trans_hyp_l
        (vmatch 1.0R x hd_val)
        (pts_to_parsed p pl #pm_v hd_val)
        (iterator_match vmatch p pm' it' tl_l)
        (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l));
      fold (iterator_next_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
      x
    }
  }
}
```

#pop-options
