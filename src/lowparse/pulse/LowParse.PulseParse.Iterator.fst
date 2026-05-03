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

#push-options "--z3rlimit 80"

```pulse
ghost
fn base_iterator_match_n_narrow
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n off' n': nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
requires
  base_iterator_match_n vmatch p off n pm i l **
  pure (off <= off' /\ off' + n' <= off + n)
ensures
  base_iterator_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n') **
  trade (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n'))
        (base_iterator_match_n vmatch p off n pm i l)
{
  base_iterator_match_n_share vmatch p off n pm i l vmatch_share;
  match i {
    Empty -> {
      // n = 0, off = 0, so off' = 0, n' = 0
      unfold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
      fold (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Empty #t) (list_narrow l (off' - off) n'));
      intro (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Empty #t) (list_narrow l (off' - off) n') @==>
             base_iterator_match_n vmatch p off n pm (Empty #t) l)
        #(base_iterator_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l)
        fn _ {
          unfold (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Empty #t) (list_narrow l (off' - off) n'));
          drop_ (pure (Nil? (list_narrow l (off' - off) n') /\ n' == 0 /\ off' == 0));
          fold (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Empty #t) l);
          base_iterator_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Empty #t) l l vmatch_gather;
          drop_ (pure (l == l));
          rewrite (base_iterator_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Empty #t) l)
            as (base_iterator_match_n vmatch p off n pm (Empty #t) l);
        };
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      if (off' = off && n' = n) {
        // No change in window — just return one copy
        base_iterator_match_n_length vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l;
        FStar.List.Pure.Properties.splitAt_length_total l;
        assert (pure (list_narrow l (off' - off) n' == l));
        rewrite (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l)
          as (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n'));
        intro (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n') @==>
               base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) l)
          #(base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l **
            pure (List.Tot.length l == n))
          fn _ {
            FStar.List.Pure.Properties.splitAt_length_total l;
            rewrite (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n'))
              as (base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l);
            drop_ (pure (List.Tot.length l == n));
            base_iterator_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Singleton #t sp sv s) l l vmatch_gather;
            drop_ (pure (l == l));
            rewrite (base_iterator_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Singleton #t sp sv s) l)
              as (base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) l);
          };
        rewrite each (Singleton #t sp sv s) as i;
      } else {
        // Shrinking a Singleton. Since off + n <= 1, either n=0 or (off=0,n=1).
        // If n=0: n'=0, off'=off=0 — handled by first branch (off'=off, n'=n).
        // So n=1, off=0. And (off',n') != (0,1), with off'<=0+1=1 and off'+n'<=1.
        // So n' = 0 (and off' = 0 or 1).
        base_iterator_match_n_singleton_unfold_pos vmatch p off n (pm /. 2.0R) sp sv s l ();
        with x y. assert (pts_to s #((pm /. 2.0R) *. sp) x ** vmatch ((pm /. 2.0R) *. sv) x y **
                          pure (l == [y] /\ off == 0 /\ n == 1));
        dup_pure (l == [y] /\ off == 0 /\ n == 1);
        base_iterator_match_n_singleton_fold_pos vmatch p off n (pm /. 2.0R) sp sv s l ();
        // n' must be 0
        replace_second_pure (off <= off' /\ off' + n' <= off + n) (l == [y] /\ off == 0 /\ n == 1) (Nil? (list_narrow l (off' - off) n') /\ n' == 0 /\ off' <= 1) ();
        drop_ (pure (off <= off' /\ off' + n' <= off + n));
        base_iterator_match_n_singleton_fold_0 vmatch p off' n' (pm /. 2.0R) sp sv s (list_narrow l (off' - off) n') ();
        intro (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n') @==>
               base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) l)
          #(base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l **
            base_iterator_match_n vmatch p off n (pm /. 2.0R) (Singleton #t sp sv s) l)
          fn _ {
            drop_ (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Singleton #t sp sv s) (list_narrow l (off' - off) n'));
            base_iterator_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Singleton #t sp sv s) l l vmatch_gather;
            drop_ (pure (l == l));
            rewrite (base_iterator_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Singleton #t sp sv s) l)
              as (base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) l);
          };
        rewrite each (Singleton #t sp sv s) as i;
      }
    }
    Slice sp sv s -> {
      // Gather two shared copies back to full perm
      base_iterator_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Slice #t sp sv s) l l vmatch_gather;
      drop_ (pure (l == l));
      rewrite (base_iterator_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Slice #t sp sv s) l)
        as (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
      // Unfold at full perm
      unfold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
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
      fold (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Slice #t sp sv s) (list_narrow l (off' - off) n'));
      // Build trade
      intro (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Slice #t sp sv s) (list_narrow l (off' - off) n') @==>
             base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l)
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
          unfold (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Slice #t sp sv s) (list_narrow l (off' - off) n'));
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
          fold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
        };
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      // Gather two shared copies back to full perm
      base_iterator_match_n_gather vmatch p off n (pm /. 2.0R) (pm /. 2.0R) (Serialized #t sp count pl) l l vmatch_gather;
      drop_ (pure (l == l));
      rewrite (base_iterator_match_n vmatch p off n (pm /. 2.0R +. pm /. 2.0R) (Serialized #t sp count pl) l)
        as (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
      // Unfold at full perm
      unfold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
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
      fold (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (snd (List.Tot.splitAt off' (reveal l_all'))));
      rewrite (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (snd (List.Tot.splitAt off' (reveal l_all'))))
        as (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (list_narrow l (off' - off) n'));
      // Build trade
      intro (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (list_narrow l (off' - off) n') @==>
             base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l)
        #(S.pts_to pl #((pm /. 2.0R) *. sp) v' **
          pure (pts_to_parsed_strong_prefix_prop (parse_nlist (off + n) p) (reveal v') l_all /\
                l == snd (List.Tot.splitAt off l_all) /\ off + n <= SZ.v count))
        fn _ {
          unfold (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) (Serialized #t sp count pl) (list_narrow l (off' - off) n'));
          with lv2. assert (pts_to_parsed_strong_prefix (parse_nlist (off' + n') p) pl #((pm /. 2.0R) *. sp) lv2);
          unfold (pts_to_parsed_strong_prefix (parse_nlist (off' + n') p) pl #((pm /. 2.0R) *. sp) lv2);
          S.gather pl;
          with v'2. assert (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2);
          rewrite (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2)
            as (S.pts_to pl #(pm *. sp) v'2);
          rewrite (S.pts_to pl #(pm *. sp) v'2) as (S.pts_to pl #(pm *. sp) v');
          fold (pts_to_parsed_strong_prefix (parse_nlist (off + n) p) pl #(pm *. sp) l_all);
          fold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
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
fn rec iterator_match_n_narrow
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (off n off' n': nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
requires
  iterator_match_n vmatch p off n pm i l **
  pure (off <= off' /\ off' + n' <= off + n)
ensures
  iterator_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n') **
  trade (iterator_match_n vmatch p off' n' (pm /. 2.0R) i (list_narrow l (off' - off) n'))
        (iterator_match_n vmatch p off n pm i l)
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p off n pm (Base bi) l);
      base_iterator_match_n_narrow vmatch p off n off' n' pm bi l vmatch_share vmatch_gather;
      fold (iterator_match_n vmatch p off' n' (pm /. 2.0R) (Base bi) (list_narrow l (off' - off) n'));
      intro (iterator_match_n vmatch p off' n' (pm /. 2.0R) (Base bi) (list_narrow l (off' - off) n') @==>
             iterator_match_n vmatch p off n pm (Base bi) l)
        #(trade (base_iterator_match_n vmatch p off' n' (pm /. 2.0R) bi (list_narrow l (off' - off) n'))
                (base_iterator_match_n vmatch p off n pm bi l))
        fn _ {
          unfold (iterator_match_n vmatch p off' n' (pm /. 2.0R) (Base bi) (list_narrow l (off' - off) n'));
          elim_trade _ _;
          fold (iterator_match_n vmatch p off n pm (Base bi) l);
        };
      rewrite each (Base bi) as i;
    }
    Append depth cb ca ob bp before oa ap after -> {
      unfold (iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
      with i_before i_after l1 l2 . assert (
        pts_to before #(pm *. bp) i_before **
        iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1 **
        pts_to after #(pm *. ap) i_after **
        iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2
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
      rewrite (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1)
        as (iterator_match_n vmatch p off_b n1 pm i_before l1);
      rewrite (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2)
        as (iterator_match_n vmatch p off_a na pm i_after l2);
      // Prove narrow preconditions for children
      append_narrow_before_ineq off n off' n' (SZ.v cb);
      append_narrow_after_ineq off n off' n' (SZ.v cb);
      // Recursively narrow before child
      iterator_match_n_narrow vmatch p off_b n1 off_b' n1' pm i_before l1 vmatch_share vmatch_gather;
      // Share R.pts_to before
      R.share before;
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      rewrite (R.pts_to before #((pm *. bp) /. 2.0R) i_before) as (R.pts_to before #((pm /. 2.0R) *. bp) i_before);
      // Recursively narrow after child
      iterator_match_n_narrow vmatch p off_a na off_a' na' pm i_after l2 vmatch_share vmatch_gather;
      // Share R.pts_to after
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i_after) as (R.pts_to after #((pm /. 2.0R) *. ap) i_after);
      // Rewrite narrow results from let-bound names back to append_* forms for fold
      rewrite (iterator_match_n vmatch p off_b' n1' (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
        as (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'));
      rewrite (iterator_match_n vmatch p off_a' na' (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
        as (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'));
      // Also rewrite the trades
      rewrite (trade (iterator_match_n vmatch p off_b' n1' (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                     (iterator_match_n vmatch p off_b n1 pm i_before l1))
        as (trade (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                  (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1));
      rewrite (trade (iterator_match_n vmatch p off_a' na' (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                     (iterator_match_n vmatch p off_a na pm i_after l2))
        as (trade (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                  (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2));
      // Establish list narrow relationship (pure facts from unfold are in SMT context)
      list_narrow_append_connect off n off' n' (SZ.v cb) (SZ.v ob) (SZ.v oa) l1 l2;
      list_narrow_length l1 (off_b' - off_b) n1';
      list_narrow_length l2 (off_a' - off_a) na';
      // Fold narrow view
      fold (iterator_match_n vmatch p off' n' (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) (list_narrow l (off' - off) n'));
      // Build trade
      intro (iterator_match_n vmatch p off' n' (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) (list_narrow l (off' - off) n') @==>
             iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l)
        #(trade (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
                (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1) **
          R.pts_to before #((pm /. 2.0R) *. bp) i_before **
          trade (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
                (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2) **
          R.pts_to after #((pm /. 2.0R) *. ap) i_after **
          pure (
            off + n <= SZ.v cb + SZ.v ca /\
            SZ.v ob + SZ.v cb <= SZ.v (iterator_length i_before) /\
            SZ.v oa + SZ.v ca <= SZ.v (iterator_length i_after) /\
            List.Tot.length l1 == n1 /\
            List.Tot.length l2 == na /\
            l == List.Tot.append l1 l2 /\
            iterator_depth i_before < Ghost.reveal depth /\
            iterator_depth i_after < Ghost.reveal depth
          ))
        fn _ {
          unfold (iterator_match_n vmatch p off' n' (pm /. 2.0R) (Append #t depth cb ca ob bp before oa ap after) (list_narrow l (off' - off) n'));
          with ib_u ia_u l1_u l2_u . assert (
            pts_to before #((pm /. 2.0R) *. bp) ib_u **
            iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_u l1_u **
            pts_to after #((pm /. 2.0R) *. ap) ia_u **
            iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_u l2_u
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
          // Rewrite before child lists/iterators to match trades
          iterator_match_n_length vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_u l1_u;
          list_narrow_length l1 (off_b' - off_b) n1';
          iterator_match_n_length vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_u l2_u;
          list_narrow_length l2 (off_a' - off_a) na';
          List.Tot.Properties.append_injective l1_u (list_narrow l1 (off_b' - off_b) n1')
            l2_u (list_narrow l2 (off_a' - off_a) na');
          with ib_x . assert (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_x l1_u);
          slprop_rw
            (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_x l1_u)
            (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
            (Pulse.Lib.Core.slprop_equiv_ext'
              (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) ib_x l1_u)
              (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
              ());
          // Elim before trade
          elim_trade
            (iterator_match_n vmatch p (append_off_before off' (SZ.v ob) (SZ.v cb)) (append_n_before off' n' (SZ.v cb)) (pm /. 2.0R) i_before (list_narrow l1 (off_b' - off_b) n1'))
            (iterator_match_n vmatch p (append_off_before off (SZ.v ob) (SZ.v cb)) (append_n_before off n (SZ.v cb)) pm i_before l1);
          // Rewrite after child
          with ia_x . assert (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_x l2_u);
          slprop_rw
            (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_x l2_u)
            (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
            (Pulse.Lib.Core.slprop_equiv_ext'
              (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) ia_x l2_u)
              (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
              ());
          // Elim after trade
          elim_trade
            (iterator_match_n vmatch p (append_off_after off' (SZ.v oa) (SZ.v cb)) (append_n_after off' n' (SZ.v cb)) (pm /. 2.0R) i_after (list_narrow l2 (off_a' - off_a) na'))
            (iterator_match_n vmatch p (append_off_after off (SZ.v oa) (SZ.v cb)) (append_n_after off n (SZ.v cb)) pm i_after l2);
          // Fold original
          fold (iterator_match_n vmatch p off n pm (Append #t depth cb ca ob bp before oa ap after) l);
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

// Ghost helper: from raw S.pts_to + pure, folds into base_iterator_match for Serialized narrow.
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
  base_iterator_match_n vmatch p 0 off'_n' pm (Serialized #t sp new_count input)
    (fst (List.Tot.splitAt off'_n' (reveal l_all)))
{
  pts_to_parsed_strong_prefix_nlist_truncate p off_n off'_n' (reveal w) (reveal l_all);
  fold (pts_to_parsed_strong_prefix (parse_nlist off'_n' p) input #(pm *. sp) (fst (List.Tot.splitAt off'_n' (reveal l_all))));
  fold (base_iterator_match_n vmatch p 0 off'_n' pm (Serialized #t sp new_count input) (fst (List.Tot.splitAt off'_n' (reveal l_all))));
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
  base_iterator_match_n vmatch p 0 n' pm (Serialized #t sp new_count pl_suffix) (reveal l_narrow)
{
  nlist_list_length (off + n) (reveal l_all);
  Seq.lemma_eq_intro (Seq.slice (reveal v') 0 (Seq.length (reveal v'))) (reveal v');
  serialized_narrow_suffix_parses p off n off' n' (reveal v') (reveal l_all) (reveal l) (reveal l_narrow) (SZ.v pos);
  S.pts_to_len pl_suffix;
  rewrite (S.pts_to pl_suffix #(pm *. sp) v_suff)
    as (S.pts_to pl_suffix #(pm *. sp) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))));
  fold (pts_to_parsed_strong_prefix (parse_nlist n' p) pl_suffix #(pm *. sp) (reveal l_narrow));
  fold (base_iterator_match_n vmatch p 0 n' pm (Serialized #t sp new_count pl_suffix) (reveal l_narrow));
}
```

#pop-options

// Trade body ghost fn for the Serialized case of base_iterator_narrow_n.
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
  base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) **
  S.is_split pl pl_prefix pl_suffix **
  S.pts_to pl_prefix #(pm *. sp) (Seq.slice (reveal v') 0 (SZ.v pos))
ensures
  base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l)
{
  // Unfold the narrow match to reach S.pts_to pl_suffix at half perm
  unfold (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  rewrite (base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length (Serialized #t (sp /. 2.0R) n' pl_suffix))) pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
    as (base_iterator_match_n vmatch p 0 (SZ.v n') pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  unfold (base_iterator_match_n vmatch p 0 (SZ.v n') pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
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
  fold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l));
}
```

#pop-options

// Ghost fn that builds the trade for the Serialized case of base_iterator_narrow_n.
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
  base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  S.pts_to pl_suffix #((pm *. sp) /. 2.0R) (Seq.slice (reveal v') (SZ.v pos) (Seq.length (reveal v'))) **
  S.is_split pl pl_prefix pl_suffix **
  S.pts_to pl_prefix #(pm *. sp) (Seq.slice (reveal v') 0 (SZ.v pos))
ensures
  base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  trade (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
       (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l))
{
  intro (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) @==>
         base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l))
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
  base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow) **
  trade (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
       (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l))
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
  fold (base_iterator_match_n vmatch p 0 n'_elem pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  rewrite (base_iterator_match_n vmatch p 0 n'_elem pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow))
    as (base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length (Serialized #t (sp /. 2.0R) n' pl_suffix))) pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  fold (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) n' pl_suffix) (reveal l_narrow));
  // Build trade
  serialized_narrow_build_trade vmatch p
    off n n'
    sp count pm pl pl_prefix pl_suffix v' l_all l l_narrow pos
    () () () ();
}
```

#pop-options

#push-options "--z3rlimit 2000 --ext no:context_pruning"

// Concrete fn for the Serialized case of base_iterator_narrow_n.
// Inlines all ghost fn logic — pures from unfold are SMT hypotheses for fold.
```pulse
fn base_iterator_narrow_n_serialized
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
  base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l
returns i': base_iterator t
ensures
  base_iterator_match vmatch p pm i' (reveal l_narrow) **
  trade (base_iterator_match vmatch p pm i' (reveal l_narrow))
       (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l)) **
  pure (base_iterator_length i' == n')
{
  // Step 1: Unfold base_iterator_match_n and pts_to_parsed_strong_prefix
  unfold (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) l);
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

  intro_pure (base_iterator_length (Serialized #t (sp /. 2.0R) n' pl_suffix) == n') ();
  let i' = Serialized #t (sp /. 2.0R) n' pl_suffix;
  rewrite each (Serialized #t (sp /. 2.0R) n' pl_suffix) as i';
  i'
  }}
}
```

```pulse
fn base_iterator_narrow_n
  (#t: Type0) (#u: Type0) (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (j: LPS.jumper p)
  (off: Ghost.erased nat) (n: Ghost.erased nat)
  (pm: perm) (i: base_iterator t) (l: Ghost.erased (list u))
  (off': SZ.t) (n': SZ.t)
requires
  base_iterator_match_n vmatch p off n pm i l **
  pure (Ghost.reveal off <= SZ.v off' /\ SZ.v off' + SZ.v n' <= Ghost.reveal off + Ghost.reveal n)
returns i': base_iterator t
ensures
  base_iterator_match vmatch p pm i' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')) **
  trade (base_iterator_match vmatch p pm i' (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n')))
       (base_iterator_match_n vmatch p off n pm i l) **
  pure (base_iterator_length i' == n')
{
  let l_narrow : Ghost.erased (list u) = list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n');
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p off n pm (Empty #t) l);
      fold (base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length (Empty #t))) pm (Empty #t) (reveal l_narrow));
      fold (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow));
      Trade.refl (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow));
      rewrite
        (trade (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow))
               (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow)))
        as (trade (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow))
                  (base_iterator_match_n vmatch p off n pm i l));
      let i' = Empty #t;
      rewrite each (Empty #t) as i';
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
    }
    Singleton sp sv s -> {
      if (n' = 0sz) {
        fold (base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length (Empty #t))) pm (Empty #t) (reveal l_narrow));
        fold (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow));
        intro (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow) @==>
               base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) (reveal l))
          #(base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) (reveal l))
          fn _ {
            unfold (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow));
            unfold (base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length (Empty #t))) pm (Empty #t) (reveal l_narrow));
            drop_ (pure (Nil? (reveal l_narrow) /\ SZ.v (base_iterator_length (Empty #t)) == 0 /\ 0 == 0));
          };
        rewrite
          (trade (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow))
                 (base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) (reveal l)))
          as (trade (base_iterator_match vmatch p pm (Empty #t) (reveal l_narrow))
                    (base_iterator_match_n vmatch p off n pm i l));
        let i' = Empty #t;
        rewrite each (Empty #t) as i';
        rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
        i'
      } else {
        base_iterator_match_n_singleton_unfold_pos vmatch p (Ghost.reveal off) (Ghost.reveal n) pm sp sv s l ();
        with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ Ghost.reveal off == 0 /\ Ghost.reveal n == 1));
        base_iterator_match_n_singleton_fold_pos vmatch p (Ghost.reveal off) (Ghost.reveal n) pm sp sv s l ();
        rewrite (base_iterator_match_n vmatch p off n pm (Singleton #t sp sv s) l)
          as (base_iterator_match_n vmatch p 0 (SZ.v (base_iterator_length (Singleton #t sp sv s))) pm (Singleton #t sp sv s) l);
        fold (base_iterator_match vmatch p pm (Singleton #t sp sv s) l);
        assert (pure (reveal l == [y]));
        FStar.List.Pure.Properties.splitAt_length_total (reveal l);
        assert (pure (reveal l_narrow == reveal l));
        Trade.rewrite_with_trade
          (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l))
          (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l_narrow));
        rewrite
          (trade (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l_narrow))
                 (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l)))
          as (trade (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l_narrow))
                    (base_iterator_match_n vmatch p off n pm i l));
        let i' = Singleton sp sv s;
        rewrite each (Singleton #t sp sv s) as i';
        rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
        i'
      }
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) l);
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
      // Fold base_iterator_match for s_middle
      Seq.lemma_eq_intro (reveal middle_seq) (reveal v_middle);
      Seq.lemma_eq_intro (reveal middle_seq) (Seq.slice (reveal v_middle) 0 (SZ.v n'));
      rewrite (SM.seq_list_match (reveal middle_seq) (reveal middle_l) (vmatch (pm *. sv)))
        as (SM.seq_list_match (Seq.slice (reveal v_middle) 0 (SZ.v (S.len s_middle))) (reveal l_narrow) (vmatch (pm *. sv)));
      fold (base_iterator_match_n vmatch p 0 (SZ.v (S.len s_middle)) pm (Slice #t sp sv s_middle) (reveal l_narrow));
      fold (base_iterator_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow));

      // Build the trade
      intro (base_iterator_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow) @==>
             base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) (reveal l))
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
          unfold (base_iterator_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow));
          unfold (base_iterator_match_n vmatch p 0 (SZ.v (S.len s_middle)) pm (Slice #t sp sv s_middle) (reveal l_narrow));
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
          fold (base_iterator_match_n vmatch p (Ghost.reveal off) (Ghost.reveal n) pm (Slice #t sp sv s) (reveal l));
        };

      rewrite
        (trade (base_iterator_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow))
               (base_iterator_match_n vmatch p off n pm (Slice #t sp sv s) (reveal l)))
        as (trade (base_iterator_match vmatch p pm (Slice #t sp sv s_middle) (reveal l_narrow))
                  (base_iterator_match_n vmatch p off n pm i l));
      let i' = Slice #t sp sv s_middle;
      rewrite each (Slice #t sp sv s_middle) as i';
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
      }}
      }}
    }
    Serialized sp count pl -> {
      let i' = base_iterator_narrow_n_serialized vmatch p j off n pm sp count pl l off' n' l_narrow () ();
      rewrite
        (trade (base_iterator_match vmatch p pm i' (reveal l_narrow))
               (base_iterator_match_n vmatch p off n pm (Serialized #t sp count pl) (reveal l)))
        as (trade (base_iterator_match vmatch p pm i' (reveal l_narrow))
                  (base_iterator_match_n vmatch p off n pm i l));
      rewrite each (reveal l_narrow) as (list_narrow l (SZ.v off' - Ghost.reveal off) (SZ.v n'));
      i'
    }
  }
}
```

#pop-options
