module LowParse.PulseParse.Iterator
#lang-pulse
include LowParse.PulseParse.Base
include LowParse.PulseParse.VCList
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

noeq
type base_mixed_list ([@@@strictly_positive] t: Type) =
| Empty
| Singleton: (sp: perm) -> (sv: perm) -> (sr: ref t) -> base_mixed_list t
| Slice: (sp: perm) -> (sv: perm) -> (ss: S.slice t) -> base_mixed_list t
| Serialized: (sp: perm) -> (count: SZ.t) -> (payload: S.slice U8.t) -> base_mixed_list t

noeq
type mixed_list ([@@@strictly_positive] t: Type) =
| Base of base_mixed_list t
| Append:
  (depth: Ghost.erased nat) ->
  (cb: SZ.t) ->
  (ca: SZ.t { SZ.fits (SZ.v cb + SZ.v ca) }) ->
  (ob: SZ.t) ->
  (bp: perm) ->
  (before: ref (mixed_list t)) ->
  (oa: SZ.t) ->
  (ap: perm) ->
  (after: ref (mixed_list t)) ->
  mixed_list t

let mixed_list_depth (#t: Type) (i: mixed_list t) : GTot nat =
  match i with
  | Base _ -> 0
  | Append depth _ _ _ _ _ _ _ _ -> Ghost.reveal depth

let base_mixed_list_length
  (#t: Type)
  (i: base_mixed_list t)
: Tot SZ.t
= match i with
  | Empty -> 0sz
  | Singleton _ _ _ -> 1sz
  | Slice _ _ sl -> S.len sl
  | Serialized _ count _ -> count

let mixed_list_length
  (#t: Type)
  (i: mixed_list t)
: Tot SZ.t
= match i with
  | Base bi -> base_mixed_list_length bi
  | Append _ cb ca _ _ _ _ _ _ -> SZ.add cb ca

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

noeq
type iterator ([@@@strictly_positive] t: Type) = {
  before: base_mixed_list t;
  after: mixed_list t
}

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
= exists* l1 l2 .
      base_mixed_list_match vmatch p pm i.before l1 **
      mixed_list_match vmatch p pm i.after l2 **
      pure (
        l == List.Tot.append l1 l2 /\
        (base_mixed_list_length i.before == 0sz ==> mixed_list_length i.after == 0sz)
      )


#push-options "--z3rlimit 4000 --fuel 2 --ifuel 1"

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
    // Empty: return { before = Empty; after = Base Empty }
    rewrite (mixed_list_match_n vmatch p 0 (SZ.v total_sz) pm ml l)
      as (mixed_list_match_n vmatch p 0 0 pm ml l);
    mixed_list_match_n_length vmatch p 0 0 pm ml l;
    // l == []
    fold (base_mixed_list_match_n vmatch p 0 0 pm (Empty #t) (Ghost.reveal l));
    rewrite (base_mixed_list_match_n vmatch p 0 0 pm (Empty #t) (Ghost.reveal l))
      as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length (Empty #t))) pm (Empty #t) (Ghost.reveal l));
    fold (base_mixed_list_match vmatch p pm (Empty #t) (Ghost.reveal l));
    fold (base_mixed_list_match_n vmatch p 0 0 pm (Empty #t) ([] #u));
    fold (mixed_list_match_n vmatch p 0 0 pm (Base (Empty #t)) ([] #u));
    rewrite (mixed_list_match_n vmatch p 0 0 pm (Base (Empty #t)) ([] #u))
      as (mixed_list_match vmatch p pm (Base (Empty #t)) ([] #u));
    List.Tot.Properties.append_l_nil (Ghost.reveal l);
    let it : iterator t = { before = Empty #t; after = Base (Empty #t) };
    rewrite (base_mixed_list_match vmatch p pm (Empty #t) (Ghost.reveal l))
      as (base_mixed_list_match vmatch p pm it.before (Ghost.reveal l));
    rewrite (mixed_list_match vmatch p pm (Base (Empty #t)) ([] #u))
      as (mixed_list_match vmatch p pm it.after ([] #u));
    fold (iterator_match vmatch p pm it (Ghost.reveal l));
    // Trade: iterator_match → mixed_list_match
    intro (iterator_match vmatch p pm it (Ghost.reveal l) @==>
           mixed_list_match vmatch p pm ml l)
      #(mixed_list_match_n vmatch p 0 0 pm ml l)
      fn _ {
        unfold (iterator_match vmatch p pm it (Ghost.reveal l));
        with l1 l2 . assert (
          base_mixed_list_match vmatch p pm it.before l1 **
          mixed_list_match vmatch p pm it.after l2 **
          pure (Ghost.reveal l == List.Tot.append l1 l2)
        );
        drop_ (base_mixed_list_match vmatch p pm it.before l1);
        drop_ (mixed_list_match vmatch p pm it.after l2);
        rewrite (mixed_list_match_n vmatch p 0 0 pm ml l)
          as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml l);
        fold (mixed_list_match vmatch p pm ml l);
      };
    rewrite each (Ghost.reveal l) as l;
    it
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
    let it : iterator t = { before = bi'; after = rest };
    rewrite (base_mixed_list_match vmatch p (pm /. 4.0R) bi' (Ghost.reveal l_head))
      as (base_mixed_list_match vmatch p (pm /. 4.0R) it.before (Ghost.reveal l_head));
    rewrite (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail))
      as (mixed_list_match vmatch p (pm /. 4.0R) it.after (Ghost.reveal l_tail));
    fold (iterator_match vmatch p (pm /. 4.0R) it (Ghost.reveal l));
    // Step 6: Build trade
    intro (iterator_match vmatch p (pm /. 4.0R) it (Ghost.reveal l) @==>
           mixed_list_match vmatch p pm ml l)
      #(base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' (Ghost.reveal l_head) **
        trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head))
             (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l) **
        trade (mixed_list_match vmatch p (pm /. 4.0R) rest (Ghost.reveal l_tail))
             (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l))
      fn _ {
        // Unfold iterator_match
        unfold (iterator_match vmatch p (pm /. 4.0R) it (Ghost.reveal l));
        with l1 l2 . assert (
          base_mixed_list_match vmatch p (pm /. 4.0R) it.before l1 **
          mixed_list_match vmatch p (pm /. 4.0R) it.after l2 **
          pure (Ghost.reveal l == List.Tot.append l1 l2)
        );
        // Gather base: spare (pm/4) + from iterator (pm/4) → pm/2
        rewrite (base_mixed_list_match vmatch p (pm /. 4.0R) it.before l1)
          as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) bi' l1);
        base_mixed_list_match_n_gather vmatch p 0 (SZ.v (base_mixed_list_length bi')) (pm /. 4.0R) (pm /. 4.0R) bi' l1 (Ghost.reveal l_head) vmatch_gather;
        rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi')) ((pm /. 4.0R) +. (pm /. 4.0R)) bi' l1)
          as (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head));
        // Elim extract trade: base_mixed_list_match (pm/2) → copy 1
        Trade.elim
          (base_mixed_list_match vmatch p (pm /. 2.0R) bi' (Ghost.reveal l_head))
          (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml l);
        // Elim narrow trade: mixed_list_match (pm/4) rest → copy 2
        // it.after == rest definitionally, l2 == l_tail by append injectivity
        list_narrow_split (Ghost.reveal l) (SZ.v len_sz);
        List.Tot.Properties.append_length_inv_head l1 l2 (Ghost.reveal l_head) (Ghost.reveal l_tail);
        rewrite (mixed_list_match vmatch p (pm /. 4.0R) it.after l2)
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
    it
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
  unfold (iterator_match vmatch p pm i (Ghost.reveal l));
  with l1 l2 . assert (
    base_mixed_list_match vmatch p pm i.before l1 **
    mixed_list_match vmatch p pm i.after l2 **
    pure (Ghost.reveal l == List.Tot.append l1 l2 /\
          (base_mixed_list_length i.before == 0sz ==> mixed_list_length i.after == 0sz))
  );
  let len_sz = base_mixed_list_length i.before;
  base_mixed_list_match_length vmatch p pm i.before (Ghost.reveal l1);
  if (SZ.eq len_sz 0sz) {
    mixed_list_match_length vmatch p pm i.after (Ghost.reveal l2);
    unreachable ()
  } else {
  // Call base_mixed_list_next_n_eos
  rewrite (base_mixed_list_match vmatch p pm i.before l1)
    as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length i.before)) pm i.before l1);
  rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length i.before)) pm i.before l1)
    as (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm i.before l1);
  let x = base_mixed_list_next_n_eos vmatch p 0 (SZ.v len_sz) 0sz len_sz pm i.before l1
    vmatch_share vmatch_gather j;
  unfold (mixed_list_next_n_eos_post vmatch p 0 (SZ.v len_sz) pm (Base i.before) (Ghost.reveal l1) x);
  with pm_v hd_val tl_val . assert (
    elt_or_serialized_match vmatch p pm_v x hd_val **
    mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val **
    trade
      (elt_or_serialized_match vmatch p pm_v x hd_val **
       mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
      (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1) **
    pure (SZ.v len_sz > 0 /\ Ghost.reveal l1 == hd_val :: tl_val)
  );
  if (SZ.eq len_sz 1sz) {
    // Case len == 1: tail is l2, call iterator_start on i.after
    rewrite (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
      as (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base i.before) tl_val);
    mixed_list_match_n_length vmatch p 1 0 (pm /. 2.0R) (Base i.before) (Ghost.reveal tl_val);
    List.Tot.Properties.append_l_nil (Ghost.reveal l2);
    let it_new = iterator_start vmatch p j pm i.after l2 vmatch_share vmatch_gather;
    with pm_after . assert (
      iterator_match vmatch p pm_after it_new l2 **
      trade (iterator_match vmatch p pm_after it_new l2)
           (mixed_list_match vmatch p pm i.after l2)
    );
    R.write r it_new;
    // Build composite trade
    intro_trade
      (elt_or_serialized_match vmatch p pm_v x hd_val **
       iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
      (iterator_match vmatch p pm i (Ghost.reveal l))
      (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base i.before) tl_val **
       trade (iterator_match vmatch p pm_after it_new l2)
            (mixed_list_match vmatch p pm i.after l2) **
       trade (elt_or_serialized_match vmatch p pm_v x hd_val **
              mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
             (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1))
      fn _ {
        rewrite (iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
          as (iterator_match vmatch p pm_after it_new l2);
        elim_trade
          (iterator_match vmatch p pm_after it_new l2)
          (mixed_list_match vmatch p pm i.after l2);
        rewrite (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base i.before) tl_val)
          as (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val);
        elim_trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
          (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm i.before l1)
          as (base_mixed_list_match vmatch p pm i.before l1);
        fold (iterator_match vmatch p pm i (Ghost.reveal l));
      };
    rewrite (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
                   (iterator_match vmatch p pm i (Ghost.reveal l)))
      as (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
                (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
    fold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
    x
  } else {
    // Case len > 1: narrow the tail base, share after
    mixed_list_match_n_length vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) (Ghost.reveal tl_val);
    unfold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val);
    let n_tail_sz = SZ.sub len_sz 1sz;
    rewrite (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) i.before tl_val)
      as (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val);
    let bi_tail = base_mixed_list_narrow_n vmatch p j 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val 1sz n_tail_sz;
    FStar.List.Pure.Properties.splitAt_length_total (Ghost.reveal tl_val);
    rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
      as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
    rewrite (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
                   (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val))
      as (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
               (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val));
    // Share after
    mixed_list_match_share vmatch p pm i.after (Ghost.reveal l2) vmatch_share;
    // Form new iterator at pm/2
    let it_new : iterator t = { before = bi_tail; after = i.after };
    rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
      as (base_mixed_list_match vmatch p (pm /. 2.0R) it_new.before (Ghost.reveal tl_val));
    rewrite (mixed_list_match vmatch p (pm /. 2.0R) i.after l2)
      as (mixed_list_match vmatch p (pm /. 2.0R) it_new.after (Ghost.reveal l2));
    let tl_l : Ghost.erased (list u) = Ghost.hide (Ghost.reveal tl_val @ Ghost.reveal l2);
    List.Tot.Properties.append_cons_l (Ghost.reveal hd_val) (Ghost.reveal tl_val) (Ghost.reveal l2);
    fold (iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l));
    R.write r it_new;
    // Build composite trade
    intro_trade
      (elt_or_serialized_match vmatch p pm_v x hd_val **
       iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l))
      (iterator_match vmatch p pm i (Ghost.reveal l))
      (mixed_list_match vmatch p (pm /. 2.0R) i.after l2 **
       trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
            (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val) **
       trade (elt_or_serialized_match vmatch p pm_v x hd_val **
              mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
             (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1))
      fn _ {
        unfold (iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l));
        with l1' l2' . assert (
          base_mixed_list_match vmatch p (pm /. 2.0R) it_new.before l1' **
          mixed_list_match vmatch p (pm /. 2.0R) it_new.after l2'
        );
        base_mixed_list_match_length vmatch p (pm /. 2.0R) it_new.before (Ghost.reveal l1');
        mixed_list_match_length vmatch p (pm /. 2.0R) it_new.after (Ghost.reveal l2');
        List.Tot.Properties.append_length_inv_head (Ghost.reveal l1') (Ghost.reveal l2') (Ghost.reveal tl_val) (Ghost.reveal l2);
        rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) it_new.before l1')
          as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
        rewrite (mixed_list_match vmatch p (pm /. 2.0R) it_new.after l2')
          as (mixed_list_match vmatch p (pm /. 2.0R) i.after l2);
        // Gather after
        mixed_list_match_gather vmatch p (pm /. 2.0R) (pm /. 2.0R) i.after (Ghost.reveal l2) (Ghost.reveal l2) vmatch_gather;
        rewrite (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) i.after l2)
          as (mixed_list_match vmatch p pm i.after l2);
        // Recover base_mixed_list_match_n via narrow trade
        elim_trade
          (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
          (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val);
        rewrite (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val)
          as (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) i.before tl_val);
        fold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val);
        // Recover original via next_n trade
        elim_trade
          (elt_or_serialized_match vmatch p pm_v x hd_val **
           mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
          (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm i.before l1)
          as (base_mixed_list_match vmatch p pm i.before l1);
        fold (iterator_match vmatch p pm i (Ghost.reveal l));
      };
    rewrite (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l))
                   (iterator_match vmatch p pm i (Ghost.reveal l)))
      as (trade (elt_or_serialized_match vmatch p pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l))
                (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
    fold (iterator_next_eos_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
    x
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

```pulse
fn iterator_next
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (pm: perm) (r: R.ref (iterator t)) (i_orig: Ghost.erased (iterator t)) (l: Ghost.erased (list u))
  (vmatch_share: share_t vmatch) (vmatch_gather: gather_t vmatch)
  (zcp: zero_copy_parse_strong_prefix (vmatch 1.0R) p)
requires
  R.pts_to r (Ghost.reveal i_orig) ** iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l) ** pure (Cons? (Ghost.reveal l))
returns res: t
ensures
  iterator_next_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) res
{
  let i = R.read r;
  rewrite (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l))
    as (iterator_match vmatch p pm i (Ghost.reveal l));
  unfold (iterator_match vmatch p pm i (Ghost.reveal l));
  with l1 l2 . assert (
    base_mixed_list_match vmatch p pm i.before l1 **
    mixed_list_match vmatch p pm i.after l2 **
    pure (Ghost.reveal l == List.Tot.append l1 l2 /\
          (base_mixed_list_length i.before == 0sz ==> mixed_list_length i.after == 0sz))
  );
  let len_sz = base_mixed_list_length i.before;
  // Prove len_sz > 0: if len==0 then after==0, so l==[], contradiction
  base_mixed_list_match_length vmatch p pm i.before (Ghost.reveal l1);
  if (SZ.eq len_sz 0sz) {
    mixed_list_match_length vmatch p pm i.after (Ghost.reveal l2);
    unreachable ()
  } else {
  // Call base_mixed_list_next_n (non-recursive)
  rewrite (base_mixed_list_match vmatch p pm i.before l1)
    as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length i.before)) pm i.before l1);
  rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length i.before)) pm i.before l1)
    as (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm i.before l1);
  let x = base_mixed_list_next_n vmatch p 0 (SZ.v len_sz) 0sz len_sz pm i.before l1
    vmatch_share vmatch_gather j zcp;
  unfold (mixed_list_next_n_post vmatch p 0 (SZ.v len_sz) pm (Base i.before) (Ghost.reveal l1) x);
  with pm_v hd_val tl_val . assert (
    vmatch pm_v x hd_val **
    mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val **
    trade
      (vmatch pm_v x hd_val **
       mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
      (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1) **
    pure (SZ.v len_sz > 0 /\ Ghost.reveal l1 == hd_val :: tl_val)
  );
  if (SZ.eq len_sz 1sz) {
    // Case len == 1: tail is l2, call iterator_start on i.after
    rewrite (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
      as (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base i.before) tl_val);
    // tl l == tl_val ++ l2 == [] ++ l2 == l2
    mixed_list_match_n_length vmatch p 1 0 (pm /. 2.0R) (Base i.before) (Ghost.reveal tl_val);
    List.Tot.Properties.append_l_nil (Ghost.reveal l2);
    let it_new = iterator_start vmatch p j pm i.after l2 vmatch_share vmatch_gather;
    with pm_after . assert (
      iterator_match vmatch p pm_after it_new l2 **
      trade (iterator_match vmatch p pm_after it_new l2)
           (mixed_list_match vmatch p pm i.after l2)
    );
    R.write r it_new;
    // Build composite trade
    // l == (hd_val :: tl_val) ++ l2 == hd_val :: (tl_val ++ l2) == hd_val :: l2 (since tl_val == [])
    intro_trade
      (vmatch pm_v x hd_val **
       iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
      (iterator_match vmatch p pm i (Ghost.reveal l))
      (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base i.before) tl_val **
       trade (iterator_match vmatch p pm_after it_new l2)
            (mixed_list_match vmatch p pm i.after l2) **
       trade (vmatch pm_v x hd_val **
              mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
             (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1))
      fn _ {
        rewrite (iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
          as (iterator_match vmatch p pm_after it_new l2);
        elim_trade
          (iterator_match vmatch p pm_after it_new l2)
          (mixed_list_match vmatch p pm i.after l2);
        rewrite (mixed_list_match_n vmatch p 1 0 (pm /. 2.0R) (Base i.before) tl_val)
          as (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val);
        elim_trade
          (vmatch pm_v x hd_val **
           mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
          (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm i.before l1)
          as (base_mixed_list_match vmatch p pm i.before l1);
        fold (iterator_match vmatch p pm i (Ghost.reveal l));
      };
    rewrite (trade (vmatch pm_v x hd_val ** iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
                   (iterator_match vmatch p pm i (Ghost.reveal l)))
      as (trade (vmatch pm_v x hd_val ** iterator_match vmatch p pm_after it_new (Ghost.reveal l2))
                (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
    fold (iterator_next_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
    x
  } else {
    // Case len > 1: narrow the tail base, share after
    // Get length fact before consuming the resource
    mixed_list_match_n_length vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) (Ghost.reveal tl_val);
    unfold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val);
    let n_tail_sz = SZ.sub len_sz 1sz;
    rewrite (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) i.before tl_val)
      as (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val);
    let bi_tail = base_mixed_list_narrow_n vmatch p j 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val 1sz n_tail_sz;
    // list_narrow tl_val (1-1) n_tail = list_narrow tl_val 0 (len-1) = tl_val
    FStar.List.Pure.Properties.splitAt_length_total (Ghost.reveal tl_val);
    rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
      as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
    rewrite (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (list_narrow tl_val (SZ.v 1sz - 1) (SZ.v n_tail_sz)))
                   (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val))
      as (trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
               (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val));
    // Share after
    mixed_list_match_share vmatch p pm i.after (Ghost.reveal l2) vmatch_share;
    // Form new iterator at pm/2
    let it_new : iterator t = { before = bi_tail; after = i.after };
    rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
      as (base_mixed_list_match vmatch p (pm /. 2.0R) it_new.before (Ghost.reveal tl_val));
    rewrite (mixed_list_match vmatch p (pm /. 2.0R) i.after l2)
      as (mixed_list_match vmatch p (pm /. 2.0R) it_new.after (Ghost.reveal l2));
    // tl l == tl_val ++ l2
    let tl_l : Ghost.erased (list u) = Ghost.hide (Ghost.reveal tl_val @ Ghost.reveal l2);
    List.Tot.Properties.append_cons_l (Ghost.reveal hd_val) (Ghost.reveal tl_val) (Ghost.reveal l2);
    fold (iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l));
    R.write r it_new;
    // Build composite trade
    intro_trade
      (vmatch pm_v x hd_val **
       iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l))
      (iterator_match vmatch p pm i (Ghost.reveal l))
      (mixed_list_match vmatch p (pm /. 2.0R) i.after l2 **
       trade (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
            (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val) **
       trade (vmatch pm_v x hd_val **
              mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
             (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1))
      fn _ {
        unfold (iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l));
        with l1' l2' . assert (
          base_mixed_list_match vmatch p (pm /. 2.0R) it_new.before l1' **
          mixed_list_match vmatch p (pm /. 2.0R) it_new.after l2'
        );
        base_mixed_list_match_length vmatch p (pm /. 2.0R) it_new.before (Ghost.reveal l1');
        mixed_list_match_length vmatch p (pm /. 2.0R) it_new.after (Ghost.reveal l2');
        List.Tot.Properties.append_length_inv_head (Ghost.reveal l1') (Ghost.reveal l2') (Ghost.reveal tl_val) (Ghost.reveal l2);
        rewrite (base_mixed_list_match vmatch p (pm /. 2.0R) it_new.before l1')
          as (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val));
        rewrite (mixed_list_match vmatch p (pm /. 2.0R) it_new.after l2')
          as (mixed_list_match vmatch p (pm /. 2.0R) i.after l2);
        // Gather after: spare (pm/2) + from iterator (pm/2) → pm
        mixed_list_match_gather vmatch p (pm /. 2.0R) (pm /. 2.0R) i.after (Ghost.reveal l2) (Ghost.reveal l2) vmatch_gather;
        rewrite (mixed_list_match vmatch p ((pm /. 2.0R) +. (pm /. 2.0R)) i.after l2)
          as (mixed_list_match vmatch p pm i.after l2);
        // Recover base_mixed_list_match_n via narrow trade
        elim_trade
          (base_mixed_list_match vmatch p (pm /. 2.0R) bi_tail (Ghost.reveal tl_val))
          (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val);
        rewrite (base_mixed_list_match_n vmatch p 1 (SZ.v n_tail_sz) (pm /. 2.0R) i.before tl_val)
          as (base_mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) i.before tl_val);
        fold (mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val);
        // Recover original via next_n trade
        elim_trade
          (vmatch pm_v x hd_val **
           mixed_list_match_n vmatch p 1 (nat_pred (SZ.v len_sz)) (pm /. 2.0R) (Base i.before) tl_val)
          (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        unfold (mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm (Base i.before) l1);
        rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v len_sz) pm i.before l1)
          as (base_mixed_list_match vmatch p pm i.before l1);
        fold (iterator_match vmatch p pm i (Ghost.reveal l));
      };
    rewrite (trade (vmatch pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l))
                   (iterator_match vmatch p pm i (Ghost.reveal l)))
      as (trade (vmatch pm_v x hd_val ** iterator_match vmatch p (pm /. 2.0R) it_new (Ghost.reveal tl_l))
                (iterator_match vmatch p pm (Ghost.reveal i_orig) (Ghost.reveal l)));
    fold (iterator_next_post vmatch p pm r (Ghost.reveal i_orig) (Ghost.reveal l) x);
    x
  }
  }
}
```

#pop-options

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

#push-options "--z3rlimit 16000 --fuel 2 --ifuel 1 --ext no:context_pruning"

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
  // Unpack refs
  with v1 v2 v3 v4 vy. assert (
    R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy
  );
  // Get total length
  let total_sz = mixed_list_length ml;
  // Share the mixed_list → two copies at pm/2
  unfold (mixed_list_match vmatch p pm ml (Ghost.reveal l));
  rewrite (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml)) pm ml (Ghost.reveal l))
    as (mixed_list_match_n vmatch p 0 (SZ.v total_sz) pm ml (Ghost.reveal l));
  mixed_list_match_n_share vmatch p 0 (SZ.v total_sz) pm ml (Ghost.reveal l) vmatch_share;
  // copy1 and copy2 both at pm/2
  // copy1 → will be used for scanning
  // copy2 → will be used for the "after" part of the result
  // Search loop: find insertion position k
  let mut r_k = 0sz;
  let mut r_continue = true;
  let mut r_found = 0sz; // 0 = found (insert before k), 1 = duplicate at k, 2 = insert at end
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
    R.pts_to r1 v1 ** R.pts_to r2 v2 ** R.pts_to r3 v3 ** R.pts_to r4 v4 ** R.pts_to ry vy **
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
      // End of list: insert at end
      r_found := 2sz;
      r_continue := false;
    } else {
      // Peek at element k: narrow copy1 to [k, 1)
      mixed_list_match_n_length vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l);
      let ml_k = mixed_list_narrow_n vmatch p j 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)
        k_val 1sz vmatch_share vmatch_gather;
      // ml_k matches [l[k]] at pm/4
      // Unfold to match_n
      let l_k : Ghost.erased (list u) = list_narrow (Ghost.reveal l) (SZ.v k_val - 0) 1;
      rewrite (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_k (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v 1sz)))
        as (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      rewrite (trade (mixed_list_match vmatch p ((pm /. 2.0R) /. 2.0R) ml_k (list_narrow (Ghost.reveal l) (SZ.v k_val - 0) (SZ.v 1sz)))
                     (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)))
        as (trade (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k))
                  (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l)));
      // Extract element from ml_k
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
      // len_bi == 1, so list_narrow l_k 0 1 == l_k
      assert (pure (SZ.v len_bi == 1));
      rewrite (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
        as (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi_k)) (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)));
      rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi_k)) (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
        as (base_mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) bi_k (Ghost.reveal l_k));
      // Extract head element
      let x_elem = base_mixed_list_next_n vmatch p 0 1 0sz 1sz (pm /. 4.0R) bi_k (Ghost.reveal l_k) vmatch_share vmatch_gather j zcp;
      unfold (mixed_list_next_n_post vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k) x_elem);
      with pm_v hd_val tl_val . assert (
        vmatch pm_v x_elem hd_val **
        mixed_list_match_n vmatch p 1 0 ((pm /. 4.0R) /. 2.0R) (Base bi_k) tl_val **
        trade (vmatch pm_v x_elem hd_val ** mixed_list_match_n vmatch p 1 0 ((pm /. 4.0R) /. 2.0R) (Base bi_k) tl_val)
              (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k)) **
        pure (1 > 0 /\ Ghost.reveal l_k == hd_val :: tl_val)
      );
      // hd_val == l[k]
      // Compare x_elem with y_elem
      let cmp_result = cmp x_elem y_elem #pm_v #hd_val #pm_y #y;
      // Recover: elim all trades to get copy1 back
      // Step 1: elim base_next trade
      Trade.elim
        (vmatch pm_v x_elem hd_val ** mixed_list_match_n vmatch p 1 0 ((pm /. 4.0R) /. 2.0R) (Base bi_k) tl_val)
        (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k));
      // Step 2: fold back to base_mixed_list_match
      rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k))
        as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length (Base bi_k))) (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k));
      // Actually Base bi_k's mixed_list_match_n unfolds to base_mixed_list_match_n
      unfold (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length (Base bi_k))) (pm /. 4.0R) (Base bi_k) (Ghost.reveal l_k));
      rewrite (base_mixed_list_match_n vmatch p 0 (SZ.v (base_mixed_list_length bi_k)) (pm /. 4.0R) bi_k (Ghost.reveal l_k))
        as (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)));
      // Step 3: elim extract trade
      Trade.elim
        (base_mixed_list_match vmatch p (pm /. 4.0R) bi_k (list_narrow (Ghost.reveal l_k) 0 (SZ.v len_bi)))
        (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      // Step 4: fold to mixed_list_match
      rewrite (mixed_list_match_n vmatch p 0 1 (pm /. 4.0R) ml_k (Ghost.reveal l_k))
        as (mixed_list_match_n vmatch p 0 (SZ.v (mixed_list_length ml_k)) (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      fold (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k));
      // Step 5: elim narrow trade
      Trade.elim
        (mixed_list_match vmatch p (pm /. 4.0R) ml_k (Ghost.reveal l_k))
        (mixed_list_match_n vmatch p 0 (SZ.v total_sz) (pm /. 2.0R) ml (Ghost.reveal l));
      // copy1 recovered!
      // Now decide based on comparison
      // Establish hd_val == index l k_val for invariant
      list_narrow_index_hd (Ghost.reveal l) (SZ.v k_val);
      assert (pure (Ghost.reveal hd_val == List.Tot.index (Ghost.reveal l) (SZ.v k_val)));
      if (SZ.eq cmp_result 0sz) {
        // x_elem < y_elem: l[k] < y, continue scanning
        r_k := SZ.add k_val 1sz;
      } else if (SZ.eq cmp_result 1sz) {
        // x_elem == y_elem: duplicate
        r_found := 1sz;
        r_continue := false;
      } else {
        // x_elem > y_elem: y < l[k], insert before k
        r_found := 0sz;
        r_continue := false;
      }
    }
  };
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
    intro_pure (
      Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
      List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
      List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
      SZ.v (mixed_list_length result_ml) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
      SZ.v (mixed_list_length inner_ml) == 1 + SZ.v rest_sz /\
      SZ.v (mixed_list_length ml_before) >= SZ.v k_val /\
      SZ.v (mixed_list_length ml_after) >= SZ.v rest_sz
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
          Ghost.reveal l_result == List.Tot.append (Ghost.reveal l_before) (Ghost.reveal y :: Ghost.reveal l_after) /\
          List.Tot.length (Ghost.reveal l_before) == SZ.v k_val /\
          List.Tot.length (Ghost.reveal l_after) == SZ.v rest_sz /\
          SZ.v (mixed_list_length result_ml) == SZ.v k_val + SZ.v (SZ.add 1sz rest_sz) /\
          SZ.v (mixed_list_length inner_ml) == 1 + SZ.v rest_sz /\
          SZ.v (mixed_list_length ml_before) >= SZ.v k_val /\
          SZ.v (mixed_list_length ml_after) >= SZ.v rest_sz
        ))
      fn _ {
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
        List.Tot.Properties.append_injective (Ghost.reveal l1_u) (Ghost.reveal l_before) (Ghost.reveal l2_u) (Ghost.reveal y :: Ghost.reveal l_after);
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
        List.Tot.Properties.append_injective (Ghost.reveal ls_u) [Ghost.reveal y] (Ghost.reveal lr_u) (Ghost.reveal l_after);
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
