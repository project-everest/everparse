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
      base_iterator_match_n vmatch p (SZ.v cb) pm before i1 **
      pts_to after #(pm *. ap) i2 **
      iterator_match_n vmatch p n' pm i2 l2 **
      pure (
        SZ.v cb <= SZ.v (base_iterator_length before) /\
	n' <= SZ.v ca /\
	(SZ.v cb < SZ.v (base_iterator_length before) ==> n' == 0) /\
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

```pulse
ghost
fn base_iterator_match_n_singleton_gather_bound_pos_inner
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
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
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
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
    base_iterator_match_n_singleton_gather_bound_pos_inner #t #u vmatch #k p n pm pm' sp sv s l l' (fun x1 pm0 x2 pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' x2') ()

```pulse
ghost
fn base_iterator_match_n_gather_bound
  (#t: Type0)
  (#u: Type0)
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
    (x1: t) -> (#pm0: perm) -> (#x2: u) -> (#pm0': perm) -> (x2': u { List.Tot.memP x2' l' }) ->
    stt_ghost unit emp_inames (vmatch pm0 x1 x2 ** vmatch pm0' x1 x2') (fun _ -> vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2'))
  ))
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
      base_iterator_match_n_singleton_gather_bound #t #u vmatch p n pm pm' sp sv s l l' vmatch_gather;
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
        (v2': u { v2' << l' /\ List.Tot.memP v2' l' })
      requires vmatch (pm *. sv) c' v1' ** vmatch (pm' *. sv) c' v2'
      ensures vmatch ((pm +. pm') *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
      {
        vmatch_gather c' #(pm *. sv) #v1' #(pm' *. sv) v2';
        rewrite (vmatch (pm *. sv +. pm' *. sv) c' v1') as (vmatch ((pm +. pm') *. sv) c' v1');
      };
      seq_list_match_gather_memP l1 l l' (vmatch (pm *. sv)) (vmatch (pm' *. sv)) (vmatch ((pm +. pm') *. sv)) gather_prf;
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
= base_iterator_match_n_gather_bound #t #u vmatch #k p n pm pm' i l l'
    (fun x1 #pm0 #x2 #pm0' x2' -> vmatch_gather x1 #pm0 #x2 #pm0' #x2')

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
= base_iterator_match_n_gather_bound #t #u vmatch #k p (SZ.v (base_iterator_length i)) pm pm' i l l' vmatch_gather

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
= base_iterator_match_n_gather #t #u vmatch #k p (SZ.v (base_iterator_length i)) pm pm' i l l' vmatch_gather

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
= base_iterator_match_n_share #t #u vmatch #k p (SZ.v (base_iterator_length i)) pm i l vmatch_share

#push-options "--z3rlimit 20"

```pulse
ghost
fn rec iterator_match_n_share
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
requires
  iterator_match_n vmatch p n pm i l
ensures
  iterator_match_n vmatch p n (pm /. 2.0R) i l **
  iterator_match_n vmatch p n (pm /. 2.0R) i l
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p n pm (Base bi) l);
      base_iterator_match_n_share vmatch p n pm bi l vmatch_share;
      fold (iterator_match_n vmatch p n (pm /. 2.0R) (Base bi) l);
      fold (iterator_match_n vmatch p n (pm /. 2.0R) (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca before ap after -> {
      unfold (iterator_match_n vmatch p n pm (Append depth cb ca before ap after) l);
      with i1 n' i2 l2 . assert (
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
      );
      base_iterator_match_share vmatch p pm before i1 vmatch_share;
      R.share after;
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i2) as (R.pts_to after #((pm /. 2.0R) *. ap) i2);
      rewrite (R.pts_to after #((pm *. ap) /. 2.0R) i2) as (R.pts_to after #((pm /. 2.0R) *. ap) i2);
      iterator_match_n_share vmatch p n' pm i2 l2 vmatch_share;
      dup_pure (
        SZ.v cb == List.Tot.length i1 /\
        n' <= SZ.v ca /\
        List.Tot.length l2 == n' /\
        n == SZ.v cb + n' /\
        l == List.Tot.append i1 l2 /\
        iterator_depth i2 < Ghost.reveal depth
      );
      fold (iterator_match_n vmatch p n (pm /. 2.0R) (Append depth cb ca before ap after) l);
      fold (iterator_match_n vmatch p n (pm /. 2.0R) (Append depth cb ca before ap after) l);
      rewrite each (Append depth cb ca before ap after) as i;
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
  iterator_match_n vmatch p n pm i l **
  iterator_match_n vmatch p n pm' i l'
ensures
  iterator_match_n vmatch p n (pm +. pm') i l **
  pure (l == l')
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p n pm (Base bi) l);
      unfold (iterator_match_n vmatch p n pm' (Base bi) l');
      base_iterator_match_n_gather_bound vmatch p n pm pm' bi l l' vmatch_gather;
      fold (iterator_match_n vmatch p n (pm +. pm') (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca before ap after -> {
      unfold (iterator_match_n vmatch p n pm (Append depth cb ca before ap after) l);
      unfold (iterator_match_n vmatch p n pm' (Append depth cb ca before ap after) l');
      with i1 n1 i2 l2 . assert (
        base_iterator_match vmatch p pm before i1 **
        pts_to after #(pm *. ap) i2 **
        iterator_match_n vmatch p n1 pm i2 l2 **
        pure (
          SZ.v cb == List.Tot.length i1 /\
          n1 <= SZ.v ca /\
          List.Tot.length l2 == n1 /\
          n == SZ.v cb + n1 /\
          l == List.Tot.append i1 l2 /\
          iterator_depth i2 < Ghost.reveal depth
        )
      );
      with i1' n1' i2' l2' . assert (
        base_iterator_match vmatch p pm' before i1' **
        pts_to after #(pm' *. ap) i2' **
        iterator_match_n vmatch p n1' pm' i2' l2' **
        pure (
          SZ.v cb == List.Tot.length i1' /\
          n1' <= SZ.v ca /\
          List.Tot.length l2' == n1' /\
          n == SZ.v cb + n1' /\
          l' == List.Tot.append i1' l2' /\
          iterator_depth i2' < Ghost.reveal depth
        )
      );
      // Gather the base_iterator_match for 'before'
      ghost fn before_gather_fn
        (x1: t) (#pm0: perm) (#x2: u) (#pm0': perm) (x2': u { List.Tot.memP x2' i1' })
      requires vmatch pm0 x1 x2 ** vmatch pm0' x1 x2'
      ensures vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
      {
        FStar.List.Tot.Properties.append_memP i1' l2' x2';
        vmatch_gather x1 #pm0 #x2 #pm0' x2'
      };
      base_iterator_match_gather_bound vmatch p pm pm' before i1 i1' before_gather_fn;
      // Gather R.pts_to for 'after'
      R.gather after;
      rewrite (R.pts_to after #(pm *. ap +. pm' *. ap) i2) as (R.pts_to after #((pm +. pm') *. ap) i2);
      rewrite each i2' as i2;
      rewrite each i1' as i1;
      // At this point we have:
      //   iterator_match_n vmatch p n1 pm i2 l2
      //   iterator_match_n vmatch p n1' pm' i2 l2'
      // From the pure facts, n1 == n1'
      // Gather the recursive iterator_match_n for i2
      with n1x ix lx . assert (iterator_match_n vmatch p n1x pm' ix lx);
      slprop_rw _ _ (Pulse.Lib.Core.slprop_equiv_ext' (iterator_match_n vmatch p n1 pm i2 l2) (iterator_match_n vmatch p n1x pm ix l2) ());
      ghost fn rec_gather_fn
        (x1: t) (#pm0: perm) (#x2: u) (#pm0': perm) (x2': u { List.Tot.memP x2' lx })
      requires vmatch pm0 x1 x2 ** vmatch pm0' x1 x2'
      ensures vmatch (pm0 +. pm0') x1 x2 ** pure (x2 == x2')
      {
        FStar.List.Tot.Properties.append_memP i1 lx x2';
        vmatch_gather x1 #pm0 #x2 #pm0' x2'
      };
      iterator_match_n_gather_bound vmatch p n1x pm pm' ix l2 lx rec_gather_fn;
      fold (iterator_match_n vmatch p n (pm +. pm') (Append depth cb ca before ap after) l);
      rewrite each (Append depth cb ca before ap after) as i;
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
  (n: nat)
  (pm: perm)
  (pm': perm)
  (i: iterator t)
  (l: list u)
  (l': list u)
  (vmatch_gather: gather_t vmatch)
: stt_ghost unit emp_inames
    (iterator_match_n vmatch p n pm i l **
     iterator_match_n vmatch p n pm' i l')
    (fun _ ->
      iterator_match_n vmatch p n (pm +. pm') i l **
      pure (l == l'))
= iterator_match_n_gather_bound #t #u vmatch #k p n pm pm' i l l'
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
= iterator_match_n_share #t #u vmatch #k p (SZ.v (iterator_length i)) pm i l vmatch_share

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
= iterator_match_n_gather_bound #t #u vmatch #k p (SZ.v (iterator_length i)) pm pm' i l l' vmatch_gather

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
= iterator_match_n_gather #t #u vmatch #k p (SZ.v (iterator_length i)) pm pm' i l l' vmatch_gather

```pulse
ghost
fn base_iterator_match_n_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
requires
  base_iterator_match_n vmatch p n pm i l
ensures
  base_iterator_match_n vmatch p n pm i l **
  pure (List.Tot.length l == n)
{
  match i {
    Empty -> {
      unfold (base_iterator_match_n vmatch p n pm (Empty #t) l);
      fold (base_iterator_match_n vmatch p n pm (Empty #t) l);
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      if (n = 0) {
        base_iterator_match_n_singleton_unfold_0 vmatch p n pm sp sv s l ();
        base_iterator_match_n_singleton_fold_0 vmatch p n pm sp sv s l ();
        rewrite each (Singleton #t sp sv s) as i;
      } else {
        base_iterator_match_n_singleton_unfold_pos vmatch p n pm sp sv s l ();
        base_iterator_match_n_singleton_fold_pos vmatch p n pm sp sv s l ();
        rewrite each (Singleton #t sp sv s) as i;
      }
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
      with l' l1 . assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      SM.seq_list_match_length (vmatch (pm *. sv)) l1 l;
      fold (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
      fold (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
      rewrite each (Serialized #t sp count pl) as i;
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
= base_iterator_match_n_length vmatch p (SZ.v (base_iterator_length i)) pm i l

```pulse
ghost
fn rec iterator_match_n_length
  (#t: Type0)
  (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind)
  (p: parser k u)
  (n: nat)
  (pm: perm)
  (i: iterator t)
  (l: list u)
requires
  iterator_match_n vmatch p n pm i l
ensures
  iterator_match_n vmatch p n pm i l **
  pure (List.Tot.length l == n)
decreases (iterator_depth i)
{
  match i {
    Base bi -> {
      unfold (iterator_match_n vmatch p n pm (Base bi) l);
      base_iterator_match_n_length vmatch p n pm bi l;
      fold (iterator_match_n vmatch p n pm (Base bi) l);
      rewrite each (Base bi) as i;
    }
    Append depth cb ca before ap after -> {
      unfold (iterator_match_n vmatch p n pm (Append depth cb ca before ap after) l);
      with i1 n' i2 l2 . assert (
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
      );
      List.Tot.Properties.append_length i1 l2;
      fold (iterator_match_n vmatch p n pm (Append depth cb ca before ap after) l);
      rewrite each (Append depth cb ca before ap after) as i;
    }
  }
}
```

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
= iterator_match_n_length vmatch p (SZ.v (iterator_length i)) pm i l

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
  // from precondition: parse (parse_nlist n p) v' == Some (l, _)
  // parse_nlist_sum gives: parse (parse_nlist n p) v' == match parse (parse_nlist len p) v' with ...
  // where n = len + (n - len)
  assert (len + (n - len) == n);
  match parse (parse_nlist len p) v' with
  | Some (l1', consumed1) ->
    // l1' has type nlist len t, so List.Tot.length l1' == len
    // We need to show l1' == l1 (= fst (splitAt len l))
    begin match parse (parse_nlist (n - len) p) (Seq.slice v' consumed1 (Seq.length v')) with
    | Some (l2', consumed2) ->
      // parse_nlist_sum tells us: parse (parse_nlist n p) v' == Some (l1' ++ l2', consumed1 + consumed2)
      // from precondition: parse (parse_nlist n p) v' gives v' == l
      // so l1' ++ l2' == l
      List.Tot.Properties.append_length l1' l2';
      // l1' has length len, and l1' ++ l2' == l
      // By lemma_append_splitAt: splitAt (length l1') (l1' ++ l2') == (l1', l2')
      FStar.List.Pure.Properties.lemma_append_splitAt l1' l2';
      assert (List.Tot.splitAt len l == (l1', l2'));
      // So fst (splitAt len l) == l1'
      assert (l1 == l1');
      // pts_to_parsed_strong_prefix_prop (parse_nlist len p) v' l1 holds since parse gives l1' == l1
      ()
    | None -> ()
    end
  | None -> ()

let splitAt_0 (#a: Type) (l: list a)
: Lemma (fst (List.Tot.splitAt 0 l) == [])
  [SMTPat (List.Tot.splitAt 0 l)]
= ()

let splitAt_full (#a: Type) (l: list a)
: Lemma 
  (requires List.Tot.length l >= 0)
  (ensures fst (List.Tot.splitAt (List.Tot.length l) l) == l)
= FStar.List.Pure.Properties.splitAt_length_total l

#push-options "--z3rlimit 80"

```pulse
ghost
fn base_iterator_match_n_truncate
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (n: nat) (n': nat)
  (pm: perm)
  (i: base_iterator t)
  (l: list u)
  (vmatch_share: share_t vmatch)
  (vmatch_gather: gather_t vmatch)
requires
  base_iterator_match_n vmatch p n pm i l **
  pure (n' <= n)
ensures
  base_iterator_match_n vmatch p n' (pm /. 2.0R) i (fst (List.Tot.splitAt n' l)) **
  trade (base_iterator_match_n vmatch p n' (pm /. 2.0R) i (fst (List.Tot.splitAt n' l)))
        (base_iterator_match_n vmatch p n pm i l)
{
  base_iterator_match_n_share vmatch p n pm i l vmatch_share;
  // Now have: base_iterator_match_n vmatch p n (pm /. 2.0R) i l ** base_iterator_match_n vmatch p n (pm /. 2.0R) i l
  match i {
    Empty -> {
      // n = 0, n' = 0, l = [], l' = []
      unfold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Empty #t) l);
      fold (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Empty #t) (fst (List.Tot.splitAt n' l)));
      intro (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Empty #t) (fst (List.Tot.splitAt n' l)) @==>
             base_iterator_match_n vmatch p n pm (Empty #t) l)
        #(base_iterator_match_n vmatch p n (pm /. 2.0R) (Empty #t) l)
        fn _ {
          unfold (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Empty #t) (fst (List.Tot.splitAt n' l)));
          drop_ (pure (Nil? (fst (List.Tot.splitAt n' l)) /\ n' == 0));
          fold (base_iterator_match_n vmatch p n (pm /. 2.0R) (Empty #t) l);
          base_iterator_match_n_gather vmatch p n (pm /. 2.0R) (pm /. 2.0R) (Empty #t) l l vmatch_gather;
          drop_ (pure (l == l));
          rewrite (base_iterator_match_n vmatch p n (pm /. 2.0R +. pm /. 2.0R) (Empty #t) l)
            as (base_iterator_match_n vmatch p n pm (Empty #t) l);
        };
      rewrite each (Empty #t) as i;
    }
    Singleton sp sv s -> {
      if (n' = n) {
        // n' = n, so l' = l (splitAt n l == (l, []) when n >= length l)
        // Return one half directly
        base_iterator_match_n_length vmatch p n (pm /. 2.0R) (Singleton #t sp sv s) l;
        FStar.List.Pure.Properties.splitAt_length_total l;
        rewrite (base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton #t sp sv s) l)
          as (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Singleton #t sp sv s) (fst (List.Tot.splitAt n' l)));
        intro (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Singleton #t sp sv s) (fst (List.Tot.splitAt n' l)) @==>
               base_iterator_match_n vmatch p n pm (Singleton #t sp sv s) l)
          #(base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton #t sp sv s) l **
            pure (List.Tot.length l == n))
          fn _ {
            FStar.List.Pure.Properties.splitAt_length_total l;
            rewrite (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Singleton #t sp sv s) (fst (List.Tot.splitAt n' l)))
              as (base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton #t sp sv s) l);
            drop_ (pure (List.Tot.length l == n));
            base_iterator_match_n_gather vmatch p n (pm /. 2.0R) (pm /. 2.0R) (Singleton #t sp sv s) l l vmatch_gather;
            drop_ (pure (l == l));
            rewrite (base_iterator_match_n vmatch p n (pm /. 2.0R +. pm /. 2.0R) (Singleton #t sp sv s) l)
              as (base_iterator_match_n vmatch p n pm (Singleton #t sp sv s) l);
          };
        rewrite each (Singleton #t sp sv s) as i;
      } else {
        // n' < n for a Singleton. Since n' <= n and n' != n: n > 0
        // Unfold one copy to learn n == 1
        base_iterator_match_n_singleton_unfold_pos vmatch p n (pm /. 2.0R) sp sv s l ();
        with x y. assert (pts_to s #((pm /. 2.0R) *. sp) x ** vmatch ((pm /. 2.0R) *. sv) x y **
                          pure (l == [y] /\ n == 1));
        dup_pure (l == [y] /\ n == 1);
        // Fold back one copy to restore the match_n
        base_iterator_match_n_singleton_fold_pos vmatch p n (pm /. 2.0R) sp sv s l ();
        // From pure (l == [y] /\ n == 1) + n' <= n + n' != n => n' == 0
        // fst(splitAt 0 l) == [] (splitAt_0 SMTPat). Nil? [] is true.
        replace_second_pure (n' <= n) (l == [y] /\ n == 1) (Nil? (fst (List.Tot.splitAt n' l))) ();
        drop_ (pure (n' <= n));
        // Use fold_0 helper which avoids if-reduction and takes squash (n' == 0)
        base_iterator_match_n_singleton_fold_0 vmatch p n' (pm /. 2.0R) sp sv s (fst (List.Tot.splitAt n' l)) ();
        intro (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Singleton #t sp sv s) (fst (List.Tot.splitAt n' l)) @==>
               base_iterator_match_n vmatch p n pm (Singleton #t sp sv s) l)
          #(base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton #t sp sv s) l **
            base_iterator_match_n vmatch p n (pm /. 2.0R) (Singleton #t sp sv s) l)
          fn _ {
            drop_ (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Singleton #t sp sv s) (fst (List.Tot.splitAt n' l)));
            base_iterator_match_n_gather vmatch p n (pm /. 2.0R) (pm /. 2.0R) (Singleton #t sp sv s) l l vmatch_gather;
            drop_ (pure (l == l));
            rewrite (base_iterator_match_n vmatch p n (pm /. 2.0R +. pm /. 2.0R) (Singleton #t sp sv s) l)
              as (base_iterator_match_n vmatch p n pm (Singleton #t sp sv s) l);
          };
        rewrite each (Singleton #t sp sv s) as i;
      }
    }
    Slice sp sv s -> {
      // Gather the two shared copies back to full perm
      base_iterator_match_n_gather vmatch p n (pm /. 2.0R) (pm /. 2.0R) (Slice #t sp sv s) l l vmatch_gather;
      drop_ (pure (l == l));
      rewrite (base_iterator_match_n vmatch p n (pm /. 2.0R +. pm /. 2.0R) (Slice #t sp sv s) l)
        as (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
      // Now unfold at full perm
      unfold (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
      with sl sl1 . assert (pts_to s #(pm *. sp) sl ** SM.seq_list_match sl1 l (vmatch (pm *. sv)));
      // Share pts_to
      S.share s;
      rewrite (pts_to s #((pm *. sp) /. 2.0R) sl) as (pts_to s #((pm /. 2.0R) *. sp) sl);
      rewrite (pts_to s #((pm *. sp) /. 2.0R) sl) as (pts_to s #((pm /. 2.0R) *. sp) sl);
      // Share seq_list_match
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
      seq_list_match_share sl1 l (vmatch (pm *. sv)) (vmatch ((pm /. 2.0R) *. sv)) share_prf;
      // Now have two copies of seq_list_match sl1 l (vmatch ((pm/2)*sv))
      // Split one copy into prefix + suffix
      SM.seq_list_match_length (vmatch ((pm /. 2.0R) *. sv)) sl1 l;
      drop_ (pure (Seq.length (reveal sl1) == List.Tot.length l));
      let prefix_seq : Ghost.erased (Seq.seq t) = Seq.slice sl 0 n';
      let suffix_seq : Ghost.erased (Seq.seq t) = Seq.slice sl n' n;
      let prefix_l : Ghost.erased (list u) = fst (List.Tot.splitAt n' l);
      let suffix_l : Ghost.erased (list u) = snd (List.Tot.splitAt n' l);
      FStar.List.Pure.Properties.splitAt_length n' l;
      FStar.List.Pure.Properties.lemma_splitAt_append n' l;
      Seq.lemma_eq_intro (reveal sl1) (Seq.append (reveal prefix_seq) (reveal suffix_seq));
      rewrite (SM.seq_list_match sl1 l (vmatch ((pm /. 2.0R) *. sv)))
        as (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal suffix_seq)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv)));
      assert (pure (Seq.length (reveal prefix_seq) == List.Tot.length (reveal prefix_l) \/
                   Seq.length (reveal suffix_seq) == List.Tot.length (reveal suffix_l)));
      SMU.seq_list_match_append_elim_trade (vmatch ((pm /. 2.0R) *. sv)) (reveal prefix_seq) (reveal prefix_l) (reveal suffix_seq) (reveal suffix_l);
      drop_ (pure (Seq.length (reveal prefix_seq) == List.Tot.length (reveal prefix_l) /\
                   Seq.length (reveal suffix_seq) == List.Tot.length (reveal suffix_l)));
      // Rewrite prefix to match fold expectations
      rewrite (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)))
        as (SM.seq_list_match (Seq.slice (reveal sl) 0 n') (fst (List.Tot.splitAt n' l)) (vmatch ((pm /. 2.0R) *. sv)));
      // Assert the outer pure facts for capture in the trade
      assert (pure (n <= Seq.length (reveal sl) /\ reveal sl1 == Seq.slice (reveal sl) 0 n));
      // Fold the result
      fold (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Slice #t sp sv s) (fst (List.Tot.splitAt n' l)));
      // Build trade. Captured: pts_to half-2 (explicit sl), copy B of seq_list_match, suffix, append-trade, pure facts
      intro (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Slice #t sp sv s) (fst (List.Tot.splitAt n' l)) @==>
             base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l)
        #(pts_to s #((pm /. 2.0R) *. sp) sl **
          SM.seq_list_match sl1 l (vmatch ((pm /. 2.0R) *. sv)) **
          SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch ((pm /. 2.0R) *. sv)) **
          trade (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)) **
                 SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch ((pm /. 2.0R) *. sv)))
                (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal suffix_seq)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv))) **
          pure (n <= Seq.length (reveal sl) /\ reveal sl1 == Seq.slice (reveal sl) 0 n))
        fn _ {
          // Unfold trigger
          unfold (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Slice #t sp sv s) (fst (List.Tot.splitAt n' l)));
          with sl1_2 . assert (SM.seq_list_match sl1_2 (fst (List.Tot.splitAt n' l)) (vmatch ((pm /. 2.0R) *. sv)));
          // Gather the two pts_to s (trigger + captured) to prove sl2 == sl
          S.gather s;
          with sl2 . assert (pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) sl2);
          rewrite (pts_to s #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) sl2)
            as (pts_to s #(pm *. sp) sl2);
          // Now SMT knows sl2 == sl from the pure (sl2 == sl) in context
          // Rewrite trigger prefix to match the captured trade
          rewrite (SM.seq_list_match sl1_2 (fst (List.Tot.splitAt n' l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)));
          drop_ (pure (reveal sl2 == reveal sl));
          // Elim the append trade to reassemble
          elim_trade
            (SM.seq_list_match (reveal prefix_seq) (reveal prefix_l) (vmatch ((pm /. 2.0R) *. sv)) **
             SM.seq_list_match (reveal suffix_seq) (reveal suffix_l) (vmatch ((pm /. 2.0R) *. sv)))
            (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal suffix_seq)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv)));
          // Rewrite the reassembled seq_list_match back to sl1 / l form
          Seq.lemma_eq_intro (Seq.append (reveal prefix_seq) (reveal suffix_seq)) (reveal sl1);
          FStar.List.Pure.Properties.lemma_splitAt_append n' l;
          rewrite (SM.seq_list_match (Seq.append (reveal prefix_seq) (reveal suffix_seq)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch ((pm /. 2.0R) *. sv)))
            as (SM.seq_list_match sl1 l (vmatch ((pm /. 2.0R) *. sv)));
          // Gather the two seq_list_match copies to get full perm
          ghost fn gather_prf
            (c': t)
            (v1': u { v1' << l })
            (v2': u { v2' << l /\ List.Tot.memP v2' l })
          requires vmatch ((pm /. 2.0R) *. sv) c' v1' ** vmatch ((pm /. 2.0R) *. sv) c' v2'
          ensures vmatch (pm *. sv) c' v1' ** pure ((v1' <: u) == (v2' <: u))
          {
            vmatch_gather c' #((pm /. 2.0R) *. sv) #v1' #((pm /. 2.0R) *. sv) #v2';
            rewrite (vmatch ((pm /. 2.0R) *. sv +. (pm /. 2.0R) *. sv) c' v1') as (vmatch (pm *. sv) c' v1');
          };
          seq_list_match_gather_memP sl1 l l (vmatch ((pm /. 2.0R) *. sv)) (vmatch ((pm /. 2.0R) *. sv)) (vmatch (pm *. sv)) gather_prf;
          drop_ (pure (l == l));
          drop_ (pure (n <= Seq.length (reveal sl) /\ reveal sl1 == Seq.slice (reveal sl) 0 n));
          // Fold at full perm
          rewrite (pts_to s #(pm *. sp) sl2) as (pts_to s #(pm *. sp) sl);
          fold (base_iterator_match_n vmatch p n pm (Slice #t sp sv s) l);
        };
      rewrite each (Slice #t sp sv s) as i;
    }
    Serialized sp count pl -> {
      // Gather the two shared copies back to full perm
      base_iterator_match_n_gather vmatch p n (pm /. 2.0R) (pm /. 2.0R) (Serialized #t sp count pl) l l vmatch_gather;
      drop_ (pure (l == l));
      rewrite (base_iterator_match_n vmatch p n (pm /. 2.0R +. pm /. 2.0R) (Serialized #t sp count pl) l)
        as (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
      // Now unfold at full perm
      unfold (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
      with lv. assert (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) lv);
      unfold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) lv);
      with v'. assert (S.pts_to pl #(pm *. sp) v');
      // We have pts_to_parsed_strong_prefix_prop (parse_nlist n p) v' lv, lv == l, n <= SZ.v count
      pts_to_parsed_strong_prefix_nlist_truncate p n n' (reveal v') l;
      // Now we know pts_to_parsed_strong_prefix_prop (parse_nlist n' p) v' (fst (splitAt n' l))
      S.share pl;
      with v'1. assert (S.pts_to pl #((pm *. sp) /. 2.0R) v'1);
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v'1) as (S.pts_to pl #((pm /. 2.0R) *. sp) v'1);
      rewrite (S.pts_to pl #((pm *. sp) /. 2.0R) v') as (S.pts_to pl #((pm /. 2.0R) *. sp) v');
      fold (pts_to_parsed_strong_prefix (parse_nlist n' p) pl #((pm /. 2.0R) *. sp) (fst (List.Tot.splitAt n' l)));
      fold (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Serialized #t sp count pl) (fst (List.Tot.splitAt n' l)));
      intro (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Serialized #t sp count pl) (fst (List.Tot.splitAt n' l)) @==>
             base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l)
        #(S.pts_to pl #((pm /. 2.0R) *. sp) v' **
          pure (pts_to_parsed_strong_prefix_prop (parse_nlist n p) (reveal v') l /\
                n <= SZ.v count))
        fn _ {
          unfold (base_iterator_match_n vmatch p n' (pm /. 2.0R) (Serialized #t sp count pl) (fst (List.Tot.splitAt n' l)));
          with lv2. assert (pts_to_parsed_strong_prefix (parse_nlist n' p) pl #((pm /. 2.0R) *. sp) lv2);
          unfold (pts_to_parsed_strong_prefix (parse_nlist n' p) pl #((pm /. 2.0R) *. sp) lv2);
          // Now we have two S.pts_to pl at (pm/2)*sp — gather them directly
          S.gather pl;
          with v'2. assert (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2);
          rewrite (S.pts_to pl #((pm /. 2.0R) *. sp +. (pm /. 2.0R) *. sp) v'2)
            as (S.pts_to pl #(pm *. sp) v'2);
          rewrite (S.pts_to pl #(pm *. sp) v'2) as (S.pts_to pl #(pm *. sp) v');
          fold (pts_to_parsed_strong_prefix (parse_nlist n p) pl #(pm *. sp) l);
          fold (base_iterator_match_n vmatch p n pm (Serialized #t sp count pl) l);
        };
      rewrite each (Serialized #t sp count pl) as i;
    }
  }
}
```

#pop-options

#restart-solver

```pulse
ghost
fn pts_to_perm_rewrite
  (#elt: Type0) (s: S.slice elt) (pm sp: perm) (v: Ghost.erased (Seq.seq elt))
requires
  S.pts_to s #((pm *. sp) /. 2.0R) v
ensures
  S.pts_to s #(pm *. (sp /. 2.0R)) v
{
  rewrite (S.pts_to s #((pm *. sp) /. 2.0R) v) as (S.pts_to s #(pm *. (sp /. 2.0R)) v);
}
```

```pulse
fn base_iterator_truncate_n
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (n: Ghost.erased nat)
  (pm: perm)
  (i: base_iterator t)
  (l: Ghost.erased (list u))
  (len: SZ.t)
requires
  base_iterator_match_n vmatch p (Ghost.reveal n) pm i l **
  pure (SZ.v len <= Ghost.reveal n /\ Ghost.reveal n <= SZ.v (base_iterator_length i))
returns i': base_iterator t
ensures
  base_iterator_match vmatch p pm i' (fst (List.Tot.splitAt (SZ.v len) l)) **
  trade (base_iterator_match vmatch p pm i' (fst (List.Tot.splitAt (SZ.v len) l)))
       (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l) **
  pure (base_iterator_length i' == len)
{
  match i {
    Empty -> {
      // len must be 0, l must be []
      unfold (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Empty #t) l);
      // have pure (Nil? l /\ Ghost.reveal n == 0), so l == [] and len == 0
      // fst (splitAt 0 []) == []
      fold (base_iterator_match_n vmatch p (SZ.v (base_iterator_length (Empty #t))) pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
      fold (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
      Trade.refl (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)));
      rewrite
        (trade (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)))
               (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l))))
        as (trade (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) l)))
                  (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l));
      let i' = Empty #t;
      rewrite each (Empty #t) as i';
      i'
    }
    Singleton sp sv s -> {
      if (len = 0sz) {
        // len = 0, n is 0 or 1 (since n <= base_iterator_length (Singleton ..) = 1)
        // Return Empty, capture the original match in the trade
        // The precondition pure will be consumed by fold (needed prop is trivially true via splitAt_0)
        fold (base_iterator_match_n vmatch p (SZ.v (base_iterator_length (Empty #t))) pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
        fold (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
        // Build the trade: capture the original base_iterator_match_n
        intro (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))) @==>
               base_iterator_match_n vmatch p (Ghost.reveal n) pm (Singleton #t sp sv s) (reveal l))
          #(base_iterator_match_n vmatch p (Ghost.reveal n) pm (Singleton #t sp sv s) (reveal l))
          fn _ {
            unfold (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
            unfold (base_iterator_match_n vmatch p (SZ.v (base_iterator_length (Empty #t))) pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
            drop_ (pure (Nil? (fst (List.Tot.splitAt (SZ.v len) (reveal l))) /\ SZ.v (base_iterator_length (Empty #t)) == 0));
          };
        rewrite
          (trade (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))))
                 (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Singleton #t sp sv s) (reveal l)))
          as (trade (base_iterator_match vmatch p pm (Empty #t) (fst (List.Tot.splitAt (SZ.v len) (reveal l))))
                    (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l));
        let i' = Empty #t;
        rewrite each (Empty #t) as i';
        i'
      } else {
        // len >= 1, so n >= 1 (since len <= n), so n = 1 and len = 1
        base_iterator_match_n_singleton_unfold_pos vmatch p (Ghost.reveal n) pm sp sv s l ();
        with x y. assert (pts_to s #(pm *. sp) x ** vmatch (pm *. sv) x y ** pure (l == [y] /\ Ghost.reveal n == 1));
        base_iterator_match_n_singleton_fold_pos vmatch p (Ghost.reveal n) pm sp sv s l ();
        rewrite (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Singleton #t sp sv s) l)
          as (base_iterator_match_n vmatch p (SZ.v (base_iterator_length (Singleton #t sp sv s))) pm (Singleton #t sp sv s) l);
        fold (base_iterator_match vmatch p pm (Singleton #t sp sv s) l);
        // l == [y], fst (splitAt 1 [y]) == [y] == l
        assert (pure (reveal l == [y]));
        FStar.List.Pure.Properties.splitAt_length_total (reveal l);
        assert (pure (fst (List.Tot.splitAt (SZ.v len) (reveal l)) == reveal l));
        Trade.rewrite_with_trade
          (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l))
          (base_iterator_match vmatch p pm (Singleton #t sp sv s) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
        rewrite
          (trade (base_iterator_match vmatch p pm (Singleton #t sp sv s) (fst (List.Tot.splitAt (SZ.v len) (reveal l))))
                 (base_iterator_match vmatch p pm (Singleton #t sp sv s) (reveal l)))
          as (trade (base_iterator_match vmatch p pm (Singleton #t sp sv s) (fst (List.Tot.splitAt (SZ.v len) (reveal l))))
                    (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l));
        let i' = Singleton sp sv s;
        rewrite each (Singleton #t sp sv s) as i';
        i'
      }
    }
    Slice sp sv s -> {
      unfold (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Slice #t sp sv s) l);
      with l' l1. assert (pts_to s #(pm *. sp) l' ** SM.seq_list_match l1 l (vmatch (pm *. sv)));
      // Get length equality BEFORE split (pts_to s will be consumed)
      S.pts_to_len s;
      SM.seq_list_match_length (vmatch (pm *. sv)) l1 (reveal l);
      // Split the slice using S.split (gives is_split, not a trade)
      let s1, s2 = S.split s len;
      with v1_g. assert (pts_to s1 #(pm *. sp) v1_g);
      with v2_g. assert (pts_to s2 #(pm *. sp) v2_g);
      S.pts_to_len s1;
      S.pts_to_len s2;
      assert (pure (SZ.v (S.len s1) == SZ.v len));
      // Split the seq_list_match
      let c1 : Ghost.erased (Seq.seq t) = Seq.slice l1 0 (SZ.v len);
      let c2 : Ghost.erased (Seq.seq t) = Seq.slice l1 (SZ.v len) (Seq.length l1);
      Seq.lemma_split l1 (SZ.v len);
      assert (pure (Seq.equal l1 (Seq.append c1 c2)));
      let prefix_l : Ghost.erased (list u) = fst (List.Tot.splitAt (SZ.v len) (reveal l));
      let suffix_l : Ghost.erased (list u) = snd (List.Tot.splitAt (SZ.v len) (reveal l));
      FStar.List.Pure.Properties.lemma_splitAt_append (SZ.v len) (reveal l);
      assert (pure (reveal l == List.Tot.append prefix_l suffix_l));
      assert (pure (List.Tot.length prefix_l == SZ.v len));
      rewrite (SM.seq_list_match l1 (reveal l) (vmatch (pm *. sv)))
        as (SM.seq_list_match (Seq.append c1 c2) (List.Tot.append prefix_l suffix_l) (vmatch (pm *. sv)));
      assert (pure (Seq.length c1 == List.Tot.length prefix_l));
      SMU.seq_list_match_append_elim_trade (vmatch (pm *. sv)) c1 prefix_l c2 suffix_l;
      // Drop the recombination trade (we won't use it; we build our own)
      drop_ (trade (SM.seq_list_match (reveal c1) (reveal prefix_l) (vmatch (pm *. sv)) ** SM.seq_list_match (reveal c2) (reveal suffix_l) (vmatch (pm *. sv)))
               (SM.seq_list_match (Seq.append (reveal c1) (reveal c2)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch (pm *. sv))));
      
      // Fold the truncated match for s1
      assert (pure (SZ.v len <= Seq.length v1_g));
      assert (pure (Seq.equal (reveal c1) (Seq.slice v1_g 0 (SZ.v len))));
      rewrite (SM.seq_list_match c1 (reveal prefix_l) (vmatch (pm *. sv)))
        as (SM.seq_list_match (Seq.slice v1_g 0 (SZ.v (S.len s1))) (reveal prefix_l) (vmatch (pm *. sv)));
      fold (base_iterator_match_n vmatch p (SZ.v (S.len s1)) pm (Slice #t sp sv s1) (reveal prefix_l));
      fold (base_iterator_match vmatch p pm (Slice #t sp sv s1) (reveal prefix_l));
      
      // Prove c2 == Seq.slice v2_g 0 (Ghost.reveal n - SZ.v len)
      // l1 == Seq.slice l' 0 n, so c2 == Seq.slice l1 len n == Seq.slice l' len n
      // v2_g == Seq.slice l' len (Seq.length l'), so Seq.slice v2_g 0 (n - len) == Seq.slice l' len n
      Seq.lemma_eq_intro (reveal c2) (Seq.slice (reveal v2_g) 0 (Ghost.reveal n - SZ.v len));
      
      // Build the trade - capture is_split and remaining resources
      intro (base_iterator_match vmatch p pm (Slice #t sp sv s1) (reveal prefix_l) @==>
             base_iterator_match_n vmatch p (Ghost.reveal n) pm (Slice #t sp sv s) (reveal l))
        #(S.is_split s s1 s2 **
          pts_to s2 #(pm *. sp) v2_g **
          SM.seq_list_match (reveal c2) (reveal suffix_l) (vmatch (pm *. sv)) **
          pure (reveal c2 == Seq.slice (reveal v2_g) 0 (Ghost.reveal n - SZ.v len) /\
                SZ.v (S.len s1) == SZ.v len /\
                Seq.length v2_g == SZ.v (S.len s) - SZ.v len /\
                Ghost.reveal n <= SZ.v (S.len s) /\
                reveal l == List.Tot.append prefix_l suffix_l /\
                List.Tot.length (reveal prefix_l) == SZ.v len))
        fn _ {
          // Unfold the prefix match to get pts_to s1 and seq_list_match
          unfold (base_iterator_match vmatch p pm (Slice #t sp sv s1) (reveal prefix_l));
          unfold (base_iterator_match_n vmatch p (SZ.v (S.len s1)) pm (Slice #t sp sv s1) (reveal prefix_l));
          with l'2 l1_2. assert (pts_to s1 #(pm *. sp) l'2 ** SM.seq_list_match l1_2 (reveal prefix_l) (vmatch (pm *. sv)));
          // Get length of l'2
          S.pts_to_len s1;
          // Now: Seq.length l'2 == SZ.v (S.len s1) == SZ.v len
          // From pure: l1_2 == Seq.slice l'2 0 (SZ.v (S.len s1))
          //          == Seq.slice l'2 0 (Seq.length l'2) which is l'2
          // Combine seq_list_matches
          SMU.seq_list_match_append_intro_trade (vmatch (pm *. sv)) l1_2 (reveal prefix_l) (reveal c2) (reveal suffix_l);
          // Now have: slm (l1_2 ++ c2) (prefix_l ++ suffix_l) ** trade ...
          // Drop the decomposition trade
          drop_ (trade (SM.seq_list_match (Seq.append l1_2 (reveal c2)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch (pm *. sv)))
                       (SM.seq_list_match l1_2 (reveal prefix_l) (vmatch (pm *. sv)) ** SM.seq_list_match (reveal c2) (reveal suffix_l) (vmatch (pm *. sv))));
          // Rewrite the combined list to l
          rewrite (SM.seq_list_match (Seq.append l1_2 (reveal c2)) (List.Tot.append (reveal prefix_l) (reveal suffix_l)) (vmatch (pm *. sv)))
            as (SM.seq_list_match (Seq.append l1_2 (reveal c2)) (reveal l) (vmatch (pm *. sv)));
          // Join the slices
          S.join s1 s2 s;
          // Now have: pts_to s (Seq.append l'2 v2_g)
          // Need to fold base_iterator_match_n with n
          // l1_2 == Seq.slice l'2 0 (Seq.length l'2) == l'2
          // c2 == Seq.slice v2_g 0 (n - len)
          // Seq.append l1_2 c2 == Seq.append l'2 (Seq.slice v2_g 0 (n - len))
          //   == Seq.slice (l'2 ++ v2_g) 0 n
          assert (pure (Seq.length (Seq.append l'2 v2_g) == SZ.v (S.len s)));
          Seq.lemma_eq_intro l1_2 l'2;
          Seq.lemma_eq_intro (Seq.append l1_2 (reveal c2)) (Seq.slice (Seq.append l'2 (reveal v2_g)) 0 (Ghost.reveal n));
          assert (pure (Ghost.reveal n <= Seq.length (Seq.append l'2 (reveal v2_g))));
          assert (pure ((Seq.append l1_2 (reveal c2)) == Seq.slice (Seq.append l'2 (reveal v2_g)) 0 (Ghost.reveal n)));
          // Rewrite slm to use the right witness for fold
          rewrite (SM.seq_list_match (Seq.append l1_2 (reveal c2)) (reveal l) (vmatch (pm *. sv)))
            as (SM.seq_list_match (Seq.slice (Seq.append l'2 (reveal v2_g)) 0 (Ghost.reveal n)) (reveal l) (vmatch (pm *. sv)));
          drop_ (pure (SZ.v (S.len s1) <= Seq.length l'2 /\ l1_2 == Seq.slice l'2 0 (SZ.v (S.len s1))));
          drop_ (pure (Seq.length l'2 == SZ.v (S.len s1)));
          fold (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Slice #t sp sv s) (reveal l));
        };
      
      rewrite
        (trade (base_iterator_match vmatch p pm (Slice #t sp sv s1) (reveal prefix_l))
               (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Slice #t sp sv s) (reveal l)))
        as (trade (base_iterator_match vmatch p pm (Slice #t sp sv s1) (fst (List.Tot.splitAt (SZ.v len) (reveal l))))
                  (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l));
      rewrite
        (base_iterator_match vmatch p pm (Slice #t sp sv s1) (reveal prefix_l))
        as (base_iterator_match vmatch p pm (Slice #t sp sv s1) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
      
      let i' = Slice #t sp sv s1;
      rewrite each (Slice #t sp sv s1) as i';
      i'
    }
    Serialized sp count pl -> {
      unfold (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Serialized #t sp count pl) l);
      with lv. assert (pts_to_parsed_strong_prefix (parse_nlist (Ghost.reveal n) p) pl #(pm *. sp) lv);
      unfold (pts_to_parsed_strong_prefix (parse_nlist (Ghost.reveal n) p) pl #(pm *. sp) lv);
      with v'. assert (S.pts_to pl #(pm *. sp) v');
      // We have pts_to_parsed_strong_prefix_prop (parse_nlist (Ghost.reveal n) p) v' lv
      // and lv == l, Ghost.reveal n <= SZ.v count
      // Drop the precondition pure (no longer needed; relevant facts are in other pures)
      drop_ (pure (SZ.v len <= Ghost.reveal n /\ Ghost.reveal n <= SZ.v (base_iterator_length (Serialized #t sp count pl))));
      pts_to_parsed_strong_prefix_nlist_truncate p (Ghost.reveal n) (SZ.v len) v' (reveal l);
      let truncated_l : Ghost.erased (list u) = fst (List.Tot.splitAt (SZ.v len) (reveal l));
      
      // Share the slice: one half for the returned iterator, one for the trade
      S.share pl;
      // Use helper to rewrite one half's permission (avoids ambiguity with two identical resources)
      pts_to_perm_rewrite pl pm sp v';
      
      // Fold the returned iterator using the half-perm copy
      // The returned iterator uses sp/2 as sub-permission
      fold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v len) p) pl #(pm *. (sp /. 2.0R)) (reveal truncated_l));
      fold (base_iterator_match_n vmatch p (SZ.v len) pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l));
      fold (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l));
      // Build the trade: capture the other half for gather
      intro (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l) @==>
             base_iterator_match_n vmatch p (Ghost.reveal n) pm (Serialized #t sp count pl) (reveal l))
        #(S.pts_to pl #((pm *. sp) /. 2.0R) v' **
          pure (pts_to_parsed_strong_prefix_prop (parse_nlist (Ghost.reveal n) p) (reveal v') (reveal l) /\
                Ghost.reveal n <= SZ.v count))
        fn _ {
          unfold (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l));
          unfold (base_iterator_match_n vmatch p (SZ.v len) pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l));
          with lv2. assert (pts_to_parsed_strong_prefix (parse_nlist (SZ.v len) p) pl #(pm *. (sp /. 2.0R)) lv2);
          unfold (pts_to_parsed_strong_prefix (parse_nlist (SZ.v len) p) pl #(pm *. (sp /. 2.0R)) lv2);
          with v'2. assert (S.pts_to pl #(pm *. (sp /. 2.0R)) v'2);
          // Gather directly: trigger half at pm*(sp/2) + captured half at (pm*sp)/2
          // These are syntactically different perms, so gather resolves unambiguously
          S.gather pl;
          rewrite (S.pts_to pl #(pm *. (sp /. 2.0R) +. (pm *. sp) /. 2.0R) v'2)
            as (S.pts_to pl #(pm *. sp) v'2);
          // Fold back the original match
          fold (pts_to_parsed_strong_prefix (parse_nlist (Ghost.reveal n) p) pl #(pm *. sp) (reveal l));
          fold (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Serialized #t sp count pl) (reveal l));
        };
      rewrite
        (trade (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l))
               (base_iterator_match_n vmatch p (Ghost.reveal n) pm (Serialized #t sp count pl) (reveal l)))
        as (trade (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (fst (List.Tot.splitAt (SZ.v len) (reveal l))))
                  (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l));
      rewrite
        (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (reveal truncated_l))
        as (base_iterator_match vmatch p pm (Serialized #t (sp /. 2.0R) len pl) (fst (List.Tot.splitAt (SZ.v len) (reveal l))));
      let i' = Serialized #t (sp /. 2.0R) len pl;
      rewrite each (Serialized #t (sp /. 2.0R) len pl) as i';
      i'
    }
  }
}
```

```pulse
fn base_iterator_truncate
  (#t: Type0) (#u: Type0)
  (vmatch: perm -> t -> u -> slprop)
  (#k: parser_kind) (p: parser k u)
  (pm: perm)
  (i: base_iterator t)
  (l: Ghost.erased (list u))
  (len: SZ.t)
requires
  base_iterator_match vmatch p pm i l **
  pure (SZ.v len <= SZ.v (base_iterator_length i))
returns i': base_iterator t
ensures
  base_iterator_match vmatch p pm i' (fst (List.Tot.splitAt (SZ.v len) l)) **
  trade (base_iterator_match vmatch p pm i' (fst (List.Tot.splitAt (SZ.v len) l)))
       (base_iterator_match vmatch p pm i l) **
  pure (base_iterator_length i' == len)
{
  unfold (base_iterator_match vmatch p pm i l);
  let n : Ghost.erased nat = SZ.v (base_iterator_length i);
  rewrite (base_iterator_match_n vmatch p (SZ.v (base_iterator_length i)) pm i l)
    as (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l);
  let i' = base_iterator_truncate_n vmatch p n pm i l len;
  rewrite
    (trade (base_iterator_match vmatch p pm i' (fst (List.Tot.splitAt (SZ.v len) l)))
           (base_iterator_match_n vmatch p (Ghost.reveal n) pm i l))
    as (trade (base_iterator_match vmatch p pm i' (fst (List.Tot.splitAt (SZ.v len) l)))
              (base_iterator_match vmatch p pm i l));
  i'
}
```
