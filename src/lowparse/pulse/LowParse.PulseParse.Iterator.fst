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
module B = Pulse.Lib.Box
open Pulse.Lib.Trade

let share_t = LowParse.PulseParse.Base.share_t

let gather_t = LowParse.PulseParse.Base.gather_t

noeq
type base_iterator ([@@@strictly_positive] t: Type) =
| Empty
| Singleton: (sp: perm) -> (sv: perm) -> (sr: ref t) -> base_iterator t
| Slice: (sp: perm) -> (sv: perm) -> (ss: S.slice t) -> base_iterator t
| Serialized: (sp: perm) -> (count: SZ.t) -> (payload: S.slice U8.t) -> base_iterator t

noeq
type iterator ([@@@strictly_positive] t: Type) =
| Base of base_iterator t
| Append:
  (depth: Ghost.erased nat) ->
  (cb: SZ.t) ->
  (ca: SZ.t { SZ.fits (SZ.v cb + SZ.v ca) }) ->
  (ob: SZ.t) ->
  (bp: perm) ->
  (before: ref (iterator t)) ->
  (oa: SZ.t) ->
  (ap: perm) ->
  (after: ref (iterator t)) ->
  iterator t

let iterator_depth (#t: Type) (i: iterator t) : GTot nat =
  match i with
  | Base _ -> 0
  | Append depth _ _ _ _ _ _ _ _ -> Ghost.reveal depth

let base_iterator_length
  (#t: Type)
  (i: base_iterator t)
: Tot SZ.t
= match i with
  | Empty -> 0sz
  | Singleton _ _ _ -> 1sz
  | Slice _ _ sl -> S.len sl
  | Serialized _ count _ -> count

let iterator_length
  (#t: Type)
  (i: iterator t)
: Tot SZ.t
= match i with
  | Base bi -> base_iterator_length bi
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

let base_iterator_match_n
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_iterator t)
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

let base_iterator_match
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
: Tot slprop
= base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length i)) pm i l

let rec iterator_match_n
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
: Tot slprop
  (decreases (iterator_depth i))
= match i with
  | Base i -> base_iterator_match_n vmatch p off n pm i l
  | Append depth cb ca ob bp before oa ap after ->
    let n1 = append_n_before off n (SZ.v cb) in
    let n' = append_n_after off n (SZ.v cb) in
    let off_b = append_off_before off (SZ.v ob) (SZ.v cb) in
    let off_a = append_off_after off (SZ.v oa) (SZ.v cb) in
    exists* i_before i_after l1 l2 .
      pts_to before #(pm *. bp) i_before **
      iterator_match_n vmatch p off_b n1 pm i_before l1 **
      pts_to after #(pm *. ap) i_after **
      iterator_match_n vmatch p off_a n' pm i_after l2 **
      pure (
        off + n <= SZ.v cb + SZ.v ca /\
        SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before) /\
        SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after) /\
        List.Tot.length l1 == n1 /\
        List.Tot.length l2 == n' /\
        l == List.Tot.append l1 l2 /\
        iterator_depth i_before < Ghost.reveal depth /\
        iterator_depth i_after < Ghost.reveal depth
      )

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
= iterator_match_n vmatch p 0 (SZ.v (iterator_length i)) pm i l

open FStar.Real

let slprop_rw : (p:slprop -> q:slprop -> slprop_equiv p q -> stt_ghost unit emp_inames p (fun _ -> q)) =
  _ by (FStar.Tactics.V2.exact (FStar.Tactics.V2.pack (FStar.Tactics.V2.Tv_FVar (FStar.Tactics.V2.pack_fv ["Pulse"; "Lib"; "Core"; "rewrite"]))))

// Singleton lemmas adapted for offset parameter

let base_iterator_match_n_singleton_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
: Lemma (base_iterator_match_n vmatch p off 0 pm (Singleton sp sv s) l == pure (Nil? l /\ off <= 1))
= ()

let base_iterator_match_n_singleton_unfold_0
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
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (fun _ -> pure (Nil? l /\ off <= 1))
= slprop_rw
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (pure (Nil? l /\ off <= 1))
    (Pulse.Lib.Core.slprop_equiv_ext'
       (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
       (pure (Nil? l /\ off <= 1))
       ())

let base_iterator_match_n_singleton_fold_0
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
    (fun _ -> base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
= slprop_rw
    (pure (Nil? l /\ off <= 1))
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (Pulse.Lib.Core.slprop_equiv_sym
       (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
       (pure (Nil? l /\ off <= 1))
       (Pulse.Lib.Core.slprop_equiv_ext'
          (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
          (pure (Nil? l /\ off <= 1))
          ()))

let base_iterator_match_n_singleton_pos
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
    (ensures base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l ==
             (exists* x y .
                pts_to s #(pm *. sp) x **
                vmatch (pm *. sv) x y **
                pure (l == [y] /\ off == 0 /\ n == 1)))
= norm_spec [delta_only [`%base_iterator_match_n]; iota; zeta] (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)

let base_iterator_match_n_singleton_unfold_pos
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
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (fun _ -> exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
= base_iterator_match_n_singleton_pos vmatch p off n pm sp sv s l ();
  slprop_rw
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
    (Pulse.Lib.Core.slprop_equiv_ext'
       (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
       (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
       ())

let base_iterator_match_n_singleton_fold_pos
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
    (fun _ -> base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
= base_iterator_match_n_singleton_pos vmatch p off n pm sp sv s l ();
  slprop_rw
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (Pulse.Lib.Core.slprop_equiv_sym
       (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
       (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1))
       (Pulse.Lib.Core.slprop_equiv_ext'
          (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
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
fn base_iterator_match_n_singleton_share_pos_inner
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
requires base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l
ensures base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l **
        base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l
{
  base_iterator_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
  with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ off == 0 /\ n == 1));
  R.share s;
  rewrite (R.pts_to s #(pm *. sp /. 2.0R) x) as (R.pts_to s #(pm /. 2.0R *. sp) x);
  rewrite (R.pts_to s #(pm *. sp /. 2.0R) x) as (R.pts_to s #(pm /. 2.0R *. sp) x);
  vmatch_share x (pm *. sv) y;
  rewrite (vmatch (pm *. sv /. 2.0R) x y) as (vmatch (pm /. 2.0R *. sv) x y);
  rewrite (vmatch (pm *. sv /. 2.0R) x y) as (vmatch (pm /. 2.0R *. sv) x y);
  base_iterator_match_n_singleton_fold_pos vmatch p off n (pm /. 2.0R) sp sv s l ();
  base_iterator_match_n_singleton_fold_pos vmatch p off n (pm /. 2.0R) sp sv s l ()
}
```

let base_iterator_match_n_singleton_share
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
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
    (fun _ -> base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l **
              base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l)
= if n = 0
  then begin
    base_iterator_match_n_singleton_0 vmatch p off pm sp sv s l;
    base_iterator_match_n_singleton_0 vmatch p off (pm /. 2.0R) sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l)
      (fun _ -> base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l **
                base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton sp sv s) l)
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (dup_pure (Nil? l /\ off <= 1))
  end
  else
    base_iterator_match_n_singleton_share_pos_inner #t #u vmatch #k p off n pm sp sv s l (fun x1 pm0 x2 -> vmatch_share x1 #pm0 #x2) ()

```pulse
ghost
fn base_iterator_match_n_singleton_gather_pos_inner
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
requires base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l **
         base_iterator_match_n vmatch p off n pm' (Singleton sp sv s) l'
ensures base_iterator_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l ** pure (l == l')
{
  base_iterator_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
  base_iterator_match_n_singleton_unfold_pos vmatch p off n pm' sp sv s l' ();
  with x1 y1. assert (pts_to s #(pm *. sp) x1 ** vmatch (pm *. sv) x1 y1 ** pure (l == [y1] /\ off == 0 /\ n == 1));
  with x2 y2. assert (pts_to s #(pm' *. sp) x2 ** vmatch (pm' *. sv) x2 y2 ** pure (l' == [y2] /\ off == 0 /\ n == 1));
  R.gather s;
  rewrite (R.pts_to s #(pm *. sp +. pm' *. sp) x1) as (R.pts_to s #((pm +. pm') *. sp) x1);
  rewrite each x2 as x1;
  vmatch_gather x1 (pm *. sv) y1 (pm' *. sv) y2;
  rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
  base_iterator_match_n_singleton_fold_pos vmatch p off n (pm +. pm') sp sv s l ()
}
```

let base_iterator_match_n_singleton_gather
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
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l **
     base_iterator_match_n vmatch p off n pm' (Singleton sp sv s) l')
    (fun _ -> base_iterator_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
              pure (l == l'))
= if n = 0
  then begin
    base_iterator_match_n_singleton_0 vmatch p off pm sp sv s l;
    base_iterator_match_n_singleton_0 vmatch p off pm' sp sv s l';
    base_iterator_match_n_singleton_0 vmatch p off (pm +. pm') sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l **
       base_iterator_match_n vmatch p off n pm' (Singleton sp sv s) l')
      (fun _ -> base_iterator_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
                pure (l == l'))
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (replace_second_pure (Nil? l /\ off <= 1) (Nil? l' /\ off <= 1) (l == l') ())
  end
  else
    base_iterator_match_n_singleton_gather_pos_inner #t #u vmatch #k p off n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2') ()

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
fn base_iterator_match_n_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
requires
  base_iterator_match_n vmatch p off n pm i l
ensures
  base_iterator_match_n vmatch p off n (pm /. 2.0R) i l **
  base_iterator_match_n vmatch p off n (pm /. 2.0R) i l
{
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p off n pm (Empty #t) l);
      fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
      fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_iterator_match_n_singleton_share vmatch p off n pm sp sv s l vmatch_share;
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
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
      fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Slice #t sp sv s) l);
      fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      with l' . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l');
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l');
      with v' . assert (S.pts_to pl #(pm *. sp) v');
      S.share pl;
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) l');
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #((pm /. 2.0R) *. sp) l');
      fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Serialized #t sp count pl) l);
      fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options

```pulse
ghost
fn base_iterator_match_n_singleton_gather_bound_pos_inner
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
requires base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l **
         base_iterator_match_n vmatch p off n pm' (Singleton sp sv s) l'
ensures base_iterator_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l ** pure (l == l')
{
  base_iterator_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
  base_iterator_match_n_singleton_unfold_pos vmatch p off n pm' sp sv s l' ();
  with x1 y1. assert (pts_to s #(pm *. sp) x1 ** vmatch (pm *. sv) x1 y1 ** pure (l == [y1] /\ off == 0 /\ n == 1));
  with x2 y2. assert (pts_to s #(pm' *. sp) x2 ** vmatch (pm' *. sv) x2 y2 ** pure (l' == [y2] /\ off == 0 /\ n == 1));
  R.gather s;
  rewrite (R.pts_to s #(pm *. sp +. pm' *. sp) x1) as (R.pts_to s #((pm +. pm') *. sp) x1);
  rewrite each x2 as x1;
  vmatch_gather x1 (pm *. sv) y1 (pm' *. sv) y2;
  rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
  base_iterator_match_n_singleton_fold_pos vmatch p off n (pm +. pm') sp sv s l ()
}
```

let base_iterator_match_n_singleton_gather_bound
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
    (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l **
     base_iterator_match_n vmatch p off n pm' (Singleton sp sv s) l')
    (fun _ -> base_iterator_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
              pure (l == l'))
= if n = 0
  then begin
    base_iterator_match_n_singleton_0 vmatch p off pm sp sv s l;
    base_iterator_match_n_singleton_0 vmatch p off pm' sp sv s l';
    base_iterator_match_n_singleton_0 vmatch p off (pm +. pm') sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_iterator_match_n vmatch p off n pm (Singleton sp sv s) l **
       base_iterator_match_n vmatch p off n pm' (Singleton sp sv s) l')
      (fun _ -> base_iterator_match_n vmatch p off n (pm +. pm') (Singleton sp sv s) l **
                pure (l == l'))
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (replace_second_pure (Nil? l /\ off <= 1) (Nil? l' /\ off <= 1) (l == l') ())
  end
  else
    base_iterator_match_n_singleton_gather_bound_pos_inner #t #u vmatch #k p off n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' x2') ()

#push-options "--z3rlimit 20"

```pulse
ghost
fn base_iterator_match_n_gather_bound
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: base_iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
requires
  base_iterator_match_n vmatch p off n pm i l **
  base_iterator_match_n vmatch p off n pm' i l'
ensures
  base_iterator_match_n vmatch p off n (pm +. pm') i l **
  pure (l == l')
{
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p off n pm (Empty #t) l);
      unfold (base_iterator_match_n vmatch p off n pm' (Empty #t) l');
      fold (base_iterator_match_n vmatch p off n (pm +. pm') (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_iterator_match_n_singleton_gather_bound #t #u vmatch p off n pm pm' sp sv s l l' vmatch_gather;
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
      unfold (base_iterator_match_n vmatch p off n pm' (Slice #t sp sv s) l');
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
      fold (base_iterator_match_n vmatch p off n (pm +. pm') (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      unfold (base_iterator_match_n vmatch p off n pm' (Serialized #t sp count pl) l');
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
      fold (base_iterator_match_n vmatch p off n (pm +. pm') (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options

let base_iterator_match_n_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: base_iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p off n pm i l **
     base_iterator_match_n vmatch p off n pm' i l')
    (fun _ ->
      base_iterator_match_n vmatch p off n (pm +. pm') i l **
      pure (l == l'))
= base_iterator_match_n_gather_bound #t #u vmatch #k p off n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')

#push-options "--z3rlimit 20"

```pulse
ghost
fn rec iterator_match_n_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
requires
  iterator_match_n vmatch p off n pm i l
ensures
  iterator_match_n vmatch p off n (pm /. 2.0R) i l **
  iterator_match_n vmatch p off n (pm /. 2.0R) i l
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p off n pm (Base bi) l);
      base_iterator_match_n_share vmatch p off n pm bi l vmatch_share;
      fold (iterator_match_n vmatch p off n (pm /. 2.0R) (Base bi) l);
      fold (iterator_match_n vmatch p off n (pm /. 2.0R) (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before) /\
          SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after) /\
          List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
          l == List.Tot.append l1 l2 /\
          iterator_depth i_before < Ghost.reveal depth /\
          iterator_depth i_after < Ghost.reveal depth
        )
      );
      R.share before;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      iterator_match_n_share vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 vmatch_share;
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      iterator_match_n_share vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 vmatch_share;
      dup_pure (
        off + n <= SZ.v cb + SZ.v ca /\
        SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before) /\
        SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after) /\
        List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
        List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
        l == List.Tot.append l1 l2 /\
        iterator_depth i_before < Ghost.reveal depth /\
        iterator_depth i_after < Ghost.reveal depth
      );
      fold (iterator_match_n vmatch p off n (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) l);
      fold (iterator_match_n vmatch p off n (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

```pulse
ghost
fn rec iterator_match_n_gather_bound
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
requires
  iterator_match_n vmatch p off n pm i l **
  iterator_match_n vmatch p off n pm' i l'
ensures
  iterator_match_n vmatch p off n (pm +. pm') i l **
  pure (l == l')
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p off n pm (Base bi) l);
      unfold (iterator_match_n vmatch p off n pm' (Base bi) l');
      base_iterator_match_n_gather_bound vmatch p off n pm pm' bi l l' vmatch_gather;
      fold (iterator_match_n vmatch p off n (pm +. pm') (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      unfold (iterator_match_n vmatch p off n pm' (Append #t depth cb ca ob bp before oa ap after) l');
      with i_before1 i_after1 l1 l2 . assert (
        pts_to before #(pm *. bp) i_before1 **
        iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before1 l1 **
        pts_to after #(pm *. ap) i_after1 **
        iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after1 l2 **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before1) /\
          SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after1) /\
          List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
          l == List.Tot.append l1 l2 /\
          iterator_depth i_before1 < Ghost.reveal depth /\
          iterator_depth i_after1 < Ghost.reveal depth
        )
      );
      with i_before2 i_after2 l1' l2' . assert (
        pts_to before #(pm' *. bp) i_before2 **
        iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm' i_before2 l1' **
        pts_to after #(pm' *. ap) i_after2 **
        iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm' i_after2 l2' **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before2) /\
          SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after2) /\
          List.Tot.length l1' == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2' == append_n_after off n (SZ.v cb) /\
          l' == List.Tot.append l1' l2' /\
          iterator_depth i_before2 < Ghost.reveal depth /\
          iterator_depth i_after2 < Ghost.reveal depth
        )
      );
      // Gather the ref 'before'
      R.gather before;
      rewrite (R.pts_to before #(pm *. bp +. pm' *. bp) i_before1) as (R.pts_to before #((pm +. pm') *. bp) i_before1);
      rewrite each i_before2 as i_before1;
      // Align the pm' iterator_match_n for before
      with ib_x l1x . assert (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm' ib_x l1x);
      slprop_rw
        (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before1 l1)
        (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm ib_x l1)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before1 l1)
          (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm ib_x l1)
          ());
      // Gather the recursive iterator_match_n for i_before
      ghost fn before_gather_fn
        (x1: t) (#pm0: perm) (#x2: u) (#pm0': perm) (x2': u { List.Tot.memP x2' l1x })
      requires vmatch pm0 x1 x2 ** vmatch pm0' x1 x2'
      ensures vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
      {
        FStar.List.Tot.Properties.append_memP l1x l2' x2';
        vmatch_gather x1 #pm0 #x2 #pm0' x2'
      };
      iterator_match_n_gather_bound vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm pm' ib_x l1 l1x before_gather_fn;
      // Gather the ref 'after'
      R.gather after;
      rewrite (R.pts_to after #(pm *. ap +. pm' *. ap) i_after1) as (R.pts_to after #((pm +. pm') *. ap) i_after1);
      rewrite each i_after2 as i_after1;
      // Align the pm' iterator_match_n for after
      with ia_x l2x . assert (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm' ia_x l2x);
      slprop_rw
        (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after1 l2)
        (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm ia_x l2)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after1 l2)
          (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm ia_x l2)
          ());
      // Gather the recursive iterator_match_n for i_after
      ghost fn after_gather_fn
        (x1: t) (#pm0: perm) (#x2: u) (#pm0': perm) (x2': u { List.Tot.memP x2' l2x })
      requires vmatch pm0 x1 x2 ** vmatch pm0' x1 x2'
      ensures vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
      {
        FStar.List.Tot.Properties.append_memP l1 l2x x2';
        vmatch_gather x1 #pm0 #x2 #pm0' x2'
      };
      iterator_match_n_gather_bound vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm pm' ia_x l2 l2x after_gather_fn;
      // Now we have iterator_match_n ... (pm +. pm') ib_x l1 and ... (pm +. pm') ia_x l2
      // Rewrite back for fold
      slprop_rw
        (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') ib_x l1)
        (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') i_before1 l1)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') ib_x l1)
          (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) (pm +. pm') i_before1 l1)
          ());
      slprop_rw
        (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') ia_x l2)
        (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') i_after1 l2)
        (Pulse.Lib.Core.slprop_equiv_ext'
          (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') ia_x l2)
          (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) (pm +. pm') i_after1 l2)
          ());
      fold (iterator_match_n vmatch p off n (pm +. pm') (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

#pop-options

let iterator_match_n_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (iterator_match_n vmatch p off n pm i l **
     iterator_match_n vmatch p off n pm' i l')
    (fun _ ->
      iterator_match_n vmatch p off n (pm +. pm') i l **
      pure (l == l'))
= iterator_match_n_gather_bound #t #u vmatch #k p off n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')

let iterator_match_share
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
: stt_ghost unit emp_inames
    (iterator_match vmatch p pm i l)
    (fun _ ->
      iterator_match vmatch p (pm /. 2.0R) i l **
      iterator_match vmatch p (pm /. 2.0R) i l)
= iterator_match_n_share #t #u vmatch #k p 0 (SZ.v (iterator_length i)) pm i l vmatch_share

let iterator_match_gather_bound
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
: stt_ghost unit emp_inames
    (iterator_match vmatch p pm i l **
     iterator_match vmatch p pm' i l')
    (fun _ ->
      iterator_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= iterator_match_n_gather_bound #t #u vmatch #k p 0 (SZ.v (iterator_length i)) pm pm' i l l' vmatch_gather

let iterator_match_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (iterator_match vmatch p pm i l **
     iterator_match vmatch p pm' i l')
    (fun _ ->
      iterator_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= iterator_match_n_gather #t #u vmatch #k p 0 (SZ.v (iterator_length i)) pm pm' i l l' vmatch_gather

```pulse
ghost
fn base_iterator_match_n_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
requires
  base_iterator_match_n vmatch p off n pm i l
ensures
  base_iterator_match_n vmatch p off n pm i l **
  pure (List.Tot.length l == n)
{
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p off n pm (Empty #t) l);
      fold (base_iterator_match_n vmatch p off n pm (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      if (n = 0) {
        base_iterator_match_n_singleton_unfold_0 vmatch p off n pm sp sv s l ();
        base_iterator_match_n_singleton_fold_0 vmatch p off n pm sp sv s l ();
        rewrite each (Singleton #t sp sv s) as i;
      } else {
        base_iterator_match_n_singleton_unfold_pos vmatch p off n pm sp sv s l ();
        base_iterator_match_n_singleton_fold_pos vmatch p off n pm sp sv s l ();
        rewrite each (Singleton #t sp sv s) as i;
      }
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
      with l' l1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      SM.seq_list_match_length (vmatch (pm *. sv)) l1 l;
      fold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      with l_all . assert (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      // l == snd (splitAt off l_all) and List.Tot.length l_all == off + n
      // so List.Tot.length l == n
      unfold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      with v' . assert (S.pts_to pl #(pm *. sp) v');
      List.Tot.Base.lemma_splitAt_snd_length off l_all;
      fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
      fold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

```pulse
ghost
fn rec iterator_match_n_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (off: nat)
  (n: nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
requires
  iterator_match_n vmatch p off n pm i l
ensures
  iterator_match_n vmatch p off n pm i l **
  pure (List.Tot.length l == n)
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p off n pm (Base bi) l);
      base_iterator_match_n_length vmatch p off n pm bi l;
      fold (iterator_match_n vmatch p off n pm (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2 **
        pure (
          off + n <= SZ.v cb + SZ.v ca /\
          SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before) /\
          SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after) /\
          List.Tot.length l1 == append_n_before off n (SZ.v cb) /\
          List.Tot.length l2 == append_n_after off n (SZ.v cb) /\
          l == List.Tot.append l1 l2 /\
          iterator_depth i_before < Ghost.reveal depth /\
          iterator_depth i_after < Ghost.reveal depth
        )
      );
      List.Tot.Properties.append_length l1 l2;
      fold (iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      rewrite each (Append #t depth cb ca ob bp before oa ap after) as i;
    }
  }
}
```

let base_iterator_match_length
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
: stt_ghost unit emp_inames
    (base_iterator_match vmatch p pm i l)
    (fun _ ->
      base_iterator_match vmatch p pm i l **
      pure (List.Tot.length l == SZ.v (base_iterator_length i)))
= base_iterator_match_n_length vmatch p 0 (SZ.v (base_iterator_length i)) pm i l

let iterator_match_length
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: iterator t)
  (l: list u)
: stt_ghost unit emp_inames
    (iterator_match vmatch p pm i l)
    (fun _ ->
      iterator_match vmatch p pm i l **
      pure (List.Tot.length l == SZ.v (iterator_length i)))
= iterator_match_n_length vmatch p 0 (SZ.v (iterator_length i)) pm i l

let base_iterator_match_share
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
: stt_ghost unit emp_inames
    (base_iterator_match vmatch p pm i l)
    (fun _ ->
      base_iterator_match vmatch p (pm /. 2.0R) i l **
      base_iterator_match vmatch p (pm /. 2.0R) i l)
= base_iterator_match_n_share #t #u vmatch #k p 0 (SZ.v (base_iterator_length i)) pm i l vmatch_share

let base_iterator_match_gather_bound
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: base_iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
: stt_ghost unit emp_inames
    (base_iterator_match vmatch p pm i l **
     base_iterator_match vmatch p pm' i l')
    (fun _ ->
      base_iterator_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= base_iterator_match_n_gather_bound #t #u vmatch #k p 0 (SZ.v (base_iterator_length i)) pm pm' i l l' vmatch_gather

let base_iterator_match_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (pm': perm)
  (i: base_iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_iterator_match vmatch p pm i l **
     base_iterator_match vmatch p pm' i l')
    (fun _ ->
      base_iterator_match vmatch p (pm +. pm') i l **
      pure (l == l'))
= base_iterator_match_n_gather #t #u vmatch #k p 0 (SZ.v (base_iterator_length i)) pm pm' i l l' vmatch_gather

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
