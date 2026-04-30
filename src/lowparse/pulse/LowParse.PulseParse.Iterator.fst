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
  (before: base_iterator t) ->
  (ap: perm) ->
  (after: ref (iterator t)) ->
  iterator t

let iterator_depth (#t: Type) (i: iterator t) : GTot nat =
  match i with
  | Base _ -> 0
  | Append depth _ _ _ _ _ -> Ghost.reveal depth

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
  | Append _ cb ca _ _ _ -> SZ.add cb ca

module SM = Pulse.Lib.SeqMatch

let base_iterator_match_n
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
: Tot slprop
= match i with
  | Empty -> pure (Nil? l /\ n == 0)
  | Singleton sp sv s -> if n = 0 then pure (Nil? l) else exists* x y .
    pts_to s #(pm *. sp) x **
    vmatch (pm *. sv) x y **
    pure (l == [y] /\ n == 1)
  | Slice sp sv s -> exists* l' l1 .
    pts_to s #(pm *. sp) l' **
    SM.seq_list_match l1 l (vmatch (pm *. sv)) **
    pure (
      n <= Seq.length l' /\
      l1 == Seq.slice l' 0 n
    )
  | Serialized sp count pl -> exists* l' .
    pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) l' **
    pure ((l' <: list u) == l /\ n <= SZ.v count)

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
= base_iterator_match_n vmatch p (SZ.v (base_iterator_length i)) pm i l

let rec iterator_match_n
  (#t: Type)
  (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
: Tot slprop
  (decreases (iterator_depth i))
= match i with
  | Base i -> base_iterator_match_n vmatch p n pm i l
  | Append depth cb ca before ap after ->
    exists* i1 n' i2 l2 .
      base_iterator_match vmatch p pm before i1 **
      pts_to after #(pm *. ap) i2 **
      iterator_match_n vmatch p n' pm i2 l2 **
      pure (
        SZ.v cb == List.Tot.length i1 /\
	n' <= SZ.v ca /\
	List.Tot.length l2 == n' /\
	n == SZ.v cb + n' /\
        l == List.Tot.append i1 l2 /\
        iterator_depth i2 < Ghost.reveal depth
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
= iterator_match_n vmatch p (SZ.v (iterator_length i)) pm i l

open FStar.Real

let slprop_rw : (p:slprop -> q:slprop -> slprop_equiv p q -> stt_ghost unit emp_inames p (fun _ -> q)) =
  _ by (FStar.Tactics.V2.exact (FStar.Tactics.V2.pack (FStar.Tactics.V2.Tv_FVar (FStar.Tactics.V2.pack_fv ["Pulse"; "Lib"; "Core"; "rewrite"]))))

let base_iterator_match_n_singleton_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
: Lemma (base_iterator_match_n vmatch p 0 pm (Singleton sp sv s) l == pure (Nil? l))
= ()

let base_iterator_match_n_singleton_unfold_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n == 0))
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (fun _ -> pure (Nil? l))
= slprop_rw
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (pure (Nil? l))
    (Pulse.Lib.Core.slprop_equiv_ext'
       (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
       (pure (Nil? l))
       ())

let base_iterator_match_n_singleton_fold_0
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n == 0))
: stt_ghost unit emp_inames
    (pure (Nil? l))
    (fun _ -> base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
= slprop_rw
    (pure (Nil? l))
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (Pulse.Lib.Core.slprop_equiv_sym
       (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
       (pure (Nil? l))
       (Pulse.Lib.Core.slprop_equiv_ext'
          (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
          (pure (Nil? l))
          ()))

let base_iterator_match_n_singleton_pos
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n <> 0))
: Lemma
    (ensures base_iterator_match_n vmatch p n pm (Singleton sp sv s) l ==
             (exists* x y .
                pts_to s #(pm *. sp) x **
                vmatch (pm *. sv) x y **
                pure (l == [y] /\ n == 1)))
= norm_spec [delta_only [`%base_iterator_match_n]; iota; zeta] (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)

let base_iterator_match_n_singleton_unfold_pos
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n <> 0))
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (fun _ -> exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
= base_iterator_match_n_singleton_pos vmatch p n pm sp sv s l ();
  slprop_rw
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
    (Pulse.Lib.Core.slprop_equiv_ext'
       (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
       (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
       ())

let base_iterator_match_n_singleton_fold_pos
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (_: squash (n <> 0))
: stt_ghost unit emp_inames
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
    (fun _ -> base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
= base_iterator_match_n_singleton_pos vmatch p n pm sp sv s l ();
  slprop_rw
    (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (Pulse.Lib.Core.slprop_equiv_sym
       (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
       (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
       (Pulse.Lib.Core.slprop_equiv_ext'
          (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
          (exists* x y. pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1))
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
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (vmatch_share: (
    (x1: t) -> (pm0: perm) -> (x2: u) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2) (fun _ -> vmatch (pm0 /. 2.0R) x1 x2 ** vmatch (pm0 /. 2.0R) x1 x2)
  ))
  (_: squash (n <> 0))
requires base_iterator_match_n vmatch p n pm (Singleton sp sv s) l
ensures base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton sp sv s) l **
        base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton sp sv s) l
{
  base_iterator_match_n_singleton_unfold_pos vmatch p n pm sp sv s l ();
  with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ n == 1));
  R.share s;
  rewrite (R.pts_to s #(pm *. sp /. 2.0R) x) as (R.pts_to s #(pm /. 2.0R *. sp) x);
  rewrite (R.pts_to s #(pm *. sp /. 2.0R) x) as (R.pts_to s #(pm /. 2.0R *. sp) x);
  vmatch_share x (pm *. sv) y;
  rewrite (vmatch (pm *. sv /. 2.0R) x y) as (vmatch (pm /. 2.0R *. sv) x y);
  rewrite (vmatch (pm *. sv /. 2.0R) x y) as (vmatch (pm /. 2.0R *. sv) x y);
  base_iterator_match_n_singleton_fold_pos vmatch p n (pm /. 2.0R) sp sv s l ();
  base_iterator_match_n_singleton_fold_pos vmatch p n (pm /. 2.0R) sp sv s l ()
}
```

```pulse
ghost
fn base_iterator_match_n_singleton_gather_pos_inner
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l l': list u)
  (vmatch_gather: (
    (x1: t) -> (pm0: perm) -> (x2: u) -> (pm0': perm) -> (x2': u) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
  (_: squash (n <> 0))
requires base_iterator_match_n vmatch p n pm (Singleton sp sv s) l **
         base_iterator_match_n vmatch p n pm' (Singleton sp sv s) l'
ensures base_iterator_match_n vmatch p n (pm +. pm') (Singleton sp sv s) l ** pure (l == l')
{
  base_iterator_match_n_singleton_unfold_pos vmatch p n pm sp sv s l ();
  base_iterator_match_n_singleton_unfold_pos vmatch p n pm' sp sv s l' ();
  with x1 y1. assert (pts_to s #(pm *. sp) x1 ** vmatch (pm *. sv) x1 y1 ** pure (l == [y1] /\ n == 1));
  with x2 y2. assert (pts_to s #(pm' *. sp) x2 ** vmatch (pm' *. sv) x2 y2 ** pure (l' == [y2] /\ n == 1));
  R.gather s;
  rewrite (R.pts_to s #(pm *. sp +. pm' *. sp) x1) as (R.pts_to s #((pm +. pm') *. sp) x1);
  rewrite each x2 as x1;
  vmatch_gather x1 (pm *. sv) y1 (pm' *. sv) y2;
  rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
  base_iterator_match_n_singleton_fold_pos vmatch p n (pm +. pm') sp sv s l ()
}
```

let base_iterator_match_n_singleton_share
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (vmatch_share: share_t vmatch)
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
    (fun _ -> base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton sp sv s) l **
              base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton sp sv s) l)
= if n = 0
  then begin
    // When n = 0, all base_iterator_match_n ... (Singleton ...) l == pure (Nil? l)
    base_iterator_match_n_singleton_0 vmatch p pm sp sv s l;
    base_iterator_match_n_singleton_0 vmatch p (pm /. 2.0R) sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l)
      (fun _ -> base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton sp sv s) l **
                base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton sp sv s) l)
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (dup_pure (Nil? l))
  end
  else
    base_iterator_match_n_singleton_share_pos_inner #t #u vmatch #k p n pm sp sv s l (fun x1 pm0 x2 -> vmatch_share x1 #pm0 #x2) ()

let base_iterator_match_n_singleton_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l **
     base_iterator_match_n vmatch p n pm' (Singleton sp sv s) l')
    (fun _ -> base_iterator_match_n vmatch p n (pm +. pm') (Singleton sp sv s) l **
              pure (l == l'))
= if n = 0
  then begin
    base_iterator_match_n_singleton_0 vmatch p pm sp sv s l;
    base_iterator_match_n_singleton_0 vmatch p pm' sp sv s l';
    base_iterator_match_n_singleton_0 vmatch p (pm +. pm') sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l **
       base_iterator_match_n vmatch p n pm' (Singleton sp sv s) l')
      (fun _ -> base_iterator_match_n vmatch p n (pm +. pm') (Singleton sp sv s) l **
                pure (l == l'))
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      // Inner: pure (Nil? l) ** pure (Nil? l') -> pure (Nil? l) ** pure (l == l')
      (replace_second_pure (Nil? l) (Nil? l') (l == l') ())
  end
  else
    base_iterator_match_n_singleton_gather_pos_inner #t #u vmatch #k p n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2') ()

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

#push-options "--z3rlimit 20"

ghost
fn base_iterator_match_n_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
requires
  base_iterator_match_n vmatch p n pm i l
ensures
  base_iterator_match_n vmatch p n (pm /. 2.0R) i l **
  base_iterator_match_n vmatch p n (pm /. 2.0R) i l
{
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p n pm (Empty #t) l);
      fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Empty #t) l);
      fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_iterator_match_n_singleton_share vmatch p n pm sp sv s l vmatch_share;
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
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
      fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Slice #t sp sv s) l);
      fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
      with l' . assert (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) l');
      unfold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) l');
      with v' . assert (S.pts_to pl #(pm *. sp) v');
      S.share pl;
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      fold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #((pm /. 2.0R) *. sp) l');
      fold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #((pm /. 2.0R) *. sp) l');
      fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Serialized #t sp count pl) l);
      fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}

#push-options "--fuel 4 --ifuel 4"

ghost
fn rec seq_list_match_gather
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
    (v2': t' { v2' << v2 }) ->
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
      (v2': t' { v2' << List.Tot.tl v2 })
    requires
      item_match1 c' v1' ** item_match2 c' v2'
    ensures
      item_match3 c' v1' ** pure ((v1' <: t') == (v2' <: t'))
    {
      prf c' v1' v2'
    };
    seq_list_match_gather (Seq.tail c) (List.Tot.tl v1) (List.Tot.tl v2) item_match1 item_match2 item_match3 prf';
    Seq.cons_head_tail c;
    SM.seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v1) (Seq.tail c) (List.Tot.tl v1) item_match3;
    rewrite (SM.seq_list_match (Seq.cons (Seq.head c) (Seq.tail c)) (List.Tot.hd v1 :: List.Tot.tl v1) item_match3)
         as (SM.seq_list_match c v1 item_match3);
    ()
  }
}

```pulse
ghost
fn base_iterator_match_n_singleton_gather_bound_pos_inner
  (#t: Type0) (#u: Type0)
  (#bound_t: Type0)
  (bound: bound_t)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (pm0: perm) -> (x2: u) -> (pm0': perm) -> (x2': u { x2' << bound }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
  (_: squash (n <> 0))
  (_: squash (l' << bound))
requires base_iterator_match_n vmatch p n pm (Singleton sp sv s) l **
         base_iterator_match_n vmatch p n pm' (Singleton sp sv s) l'
ensures base_iterator_match_n vmatch p n (pm +. pm') (Singleton sp sv s) l ** pure (l == l')
{
  base_iterator_match_n_singleton_unfold_pos vmatch p n pm sp sv s l ();
  base_iterator_match_n_singleton_unfold_pos vmatch p n pm' sp sv s l' ();
  with x1 y1. assert (pts_to s #(pm *. sp) x1 ** vmatch (pm *. sv) x1 y1 ** pure (l == [y1] /\ n == 1));
  with x2 y2. assert (pts_to s #(pm' *. sp) x2 ** vmatch (pm' *. sv) x2 y2 ** pure (l' == [y2] /\ n == 1));
  R.gather s;
  rewrite (R.pts_to s #(pm *. sp +. pm' *. sp) x1) as (R.pts_to s #((pm +. pm') *. sp) x1);
  rewrite each x2 as x1;
  vmatch_gather x1 (pm *. sv) y1 (pm' *. sv) y2;
  rewrite (vmatch (pm *. sv +. pm' *. sv) x1 y1) as (vmatch ((pm +. pm') *. sv) x1 y1);
  base_iterator_match_n_singleton_fold_pos vmatch p n (pm +. pm') sp sv s l ()
}
```

let base_iterator_match_n_singleton_gather_bound
  (#t: Type) (#u: Type)
  (#bound_t: Type)
  (bound: bound_t)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm pm': perm)
  (sp: perm) (sv: perm) (s: ref t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { x2' << bound }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
  (_: squash (l' << bound))
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l **
     base_iterator_match_n vmatch p n pm' (Singleton sp sv s) l')
    (fun _ -> base_iterator_match_n vmatch p n (pm +. pm') (Singleton sp sv s) l **
              pure (l == l'))
= if n = 0
  then begin
    base_iterator_match_n_singleton_0 vmatch p pm sp sv s l;
    base_iterator_match_n_singleton_0 vmatch p pm' sp sv s l';
    base_iterator_match_n_singleton_0 vmatch p (pm +. pm') sp sv s l;
    Pulse.Lib.Core.sub_ghost
      (base_iterator_match_n vmatch p n pm (Singleton sp sv s) l **
       base_iterator_match_n vmatch p n pm' (Singleton sp sv s) l')
      (fun _ -> base_iterator_match_n vmatch p n (pm +. pm') (Singleton sp sv s) l **
                pure (l == l'))
      (Pulse.Lib.Core.slprop_equiv_ext' _ _ ())
      (Pulse.Lib.Core.intro_slprop_post_equiv _ _ (fun _ -> Pulse.Lib.Core.slprop_equiv_ext' _ _ ()))
      (replace_second_pure (Nil? l) (Nil? l') (l == l') ())
  end
  else
    base_iterator_match_n_singleton_gather_bound_pos_inner #t #u #bound_t bound vmatch #k p n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' x2') () ()

```pulse
ghost
fn base_iterator_match_n_gather_bound
  (#t: Type0)
  (#u: Type0)
  (#bound_t: Type0)
  (bound: bound_t)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: base_iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: (
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { x2' << bound }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
  (_: squash (l' << bound))
requires
  base_iterator_match_n vmatch p n pm i l **
  base_iterator_match_n vmatch p n pm' i l'
ensures
  base_iterator_match_n vmatch p n (pm +. pm') i l **
  pure (l == l')
{
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p n pm (Empty #t) l);
      unfold (base_iterator_match_n vmatch p n pm' (Empty #t) l');
      fold (base_iterator_match_n vmatch p n (pm +. pm') (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      base_iterator_match_n_singleton_gather_bound #t #u #bound_t bound vmatch p n pm pm' sp sv s l l' vmatch_gather ();
      rewrite each (Singleton #t sp sv s) as i;
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
      unfold (base_iterator_match_n vmatch p n pm' (Slice #t sp sv s) l');
      with la l1 . assert (pts_to s #(pm *. sp) la ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      with la' l1' . assert (pts_to s #(pm' *. sp) la' ** SM.seq_list_match l1' l' (vmatch (pm' *. sv)));
      S.gather s;
      rewrite (pts_to s #(pm *. sp +. pm' *. sp) la) as (pts_to s #((pm +. pm') *. sp) la);
      rewrite each la' as la;
      rewrite each l1' as l1;
      ghost fn gather_prf
        (c': t)
        (v1': u { v1' << l })
        (v2': u { v2' << l' })
      requires vmatch (pm *. sv) c' v1' ** vmatch (pm' *. sv) c' v2'
      ensures vmatch ((pm +. pm') *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
      {
        vmatch_gather c' #(pm *. sv) #v1' #(pm' *. sv) v2';
        rewrite (vmatch (pm *. sv +. pm' *. sv) c' v1') as (vmatch ((pm +. pm') *. sv) c' v1');
      };
      seq_list_match_gather l1 l l' (vmatch (pm *. sv)) (vmatch (pm' *. sv)) (vmatch ((pm +. pm') *. sv)) gather_prf;
      fold (base_iterator_match_n vmatch p n (pm +. pm') (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
      unfold (base_iterator_match_n vmatch p n pm' (Serialized #t sp count pl) l');
      with lv . assert (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) lv);
      with lv' . assert (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm' *. sp) lv');
      unfold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) lv);
      unfold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm' *. sp) lv');
      with v1 . assert (S.pts_to pl #(pm *. sp) v1);
      with v2 . assert (S.pts_to pl #(pm' *. sp) v2);
      S.gather pl;
      rewrite (S.pts_to pl #(pm *. sp +. pm' *. sp) v1) as (S.pts_to pl #((pm +. pm') *. sp) v1);
      rewrite each v2 as v1;
      fold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #((pm +. pm') *. sp) lv);
      fold (base_iterator_match_n vmatch p n (pm +. pm') (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options
#pop-options

let base_iterator_match_n_gather
  (#t: Type) (#u: Type)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: base_iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (base_iterator_match_n vmatch p n pm i l **
     base_iterator_match_n vmatch p n pm' i l')
    (fun _ ->
      base_iterator_match_n vmatch p n (pm +. pm') i l **
      pure (l == l'))
= SM.list_cons_precedes l' ([] #(list u));
  base_iterator_match_n_gather_bound #t #u #(list (list u)) [l'] vmatch #k p n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')
    ()
