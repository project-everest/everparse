module CDDL.Pulse.Types.Base
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice.Util
module V = Pulse.Lib.Vec
module Spec = CDDL.Spec.Bijection

let rel (t1 t2: Type) = t1 -> t2 -> slprop

let coerce_rel (#t1 #t': Type) (r: rel t1 t') (t2: Type) (sq: squash (t1 == t2)) : Tot (rel t2 t') = r

[@@pulse_unfold]
let mk_rel (#t: Type) (#t': Type) (f: (x: t) -> (x': t') -> slprop) : Tot (rel t t') = f

let rel_always_false (t1 t2: Type0) : rel t1 t2 = mk_rel (fun _ _ -> pure False)

let rel_pure
    (t: Type)
: rel t t
= mk_rel (fun x y -> pure (x == y))

let rel_pure_eq
  (#t: Type)
  (x1 x2: t)
: Lemma
  (rel_pure t x1 x2 == pure (x1 == x2))
= ()

ghost fn rel_pure_intro
  (#t: Type0)
  (x: t)
requires emp
ensures rel_pure t x x
{
  rel_pure_eq x x;
  fold (rel_pure _ x x)
}

ghost fn rel_pure_peek
  (#t: Type0)
  (x y: t)
requires rel_pure t x y
ensures rel_pure t x y ** pure (x == y)
{
  unfold (rel_pure _ x y);
  fold (rel_pure _ x y)
}

let rel_unit : rel unit unit = mk_rel (fun _ _ -> emp)

noeq
type slice (t: Type) = {
  s: S.slice t;
  p: perm;
}

let rel_slice_of_list
  (#low #high: Type)
  (r: rel low high)
  (freeable: bool)
: rel (slice low) (list high)
= mk_rel (fun x y ->
    exists* s . pts_to x.s #x.p s ** seq_list_match s y r ** pure (freeable == false)
  )

module U64 = FStar.UInt64

noeq
type vec (t: Type) = {
  len: U64.t;
  v: V.vec t;
}

let rel_vec_of_list
  (#low #high: Type)
  (r: rel low high)
: rel (vec low) (list high)
= mk_rel (fun x y ->
    exists* s . pts_to x.v s ** seq_list_match s y r ** pure (V.is_full_vec x.v /\ V.length x.v == U64.v x.len)
  )

ghost
fn rec seq_list_match_pure_elim
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  seq_list_match s l (rel_pure _)
ensures
  pure (s `Seq.equal` Seq.seq_of_list l)
decreases l
{
  seq_list_match_length  (rel_pure t) s l;
  if (Nil? l) {
    seq_list_match_nil_elim s l (rel_pure _)
  } else {
    let _ = seq_list_match_cons_elim s l (rel_pure _);
    unfold (rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_elim (Seq.tail s) (List.Tot.tl l)
  }
}

ghost
fn rec seq_list_match_pure_intro
  (#t: Type0)
  (s: Seq.seq t)
  (l: list t)
requires
  pure (s `Seq.equal` Seq.seq_of_list l)  
ensures
  seq_list_match s l (rel_pure _)
decreases l
{
  if (Nil? l) {
    seq_list_match_nil_intro s l (rel_pure _)
  } else {
    fold (rel_pure _ (Seq.head s) (List.Tot.hd l));
    seq_list_match_pure_intro (Seq.tail s) (List.Tot.tl l);
    seq_list_match_cons_intro (Seq.head s) (List.Tot.hd l) (Seq.tail s) (List.Tot.tl l) (rel_pure _);
    rewrite (seq_list_match 
      (Seq.head s `Seq.cons` Seq.tail s) (List.Tot.hd l :: List.Tot.tl l) (rel_pure _)
    ) as (seq_list_match s l (rel_pure _))
  }
}

let rel_pair
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
: rel (low1 & low2) (high1 & high2)
= mk_rel (fun xlow xhigh -> r1 (fst xlow) (fst xhigh) ** r2 (snd xlow) (snd xhigh))

let rel_pair_eq
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w1: low1)
  (w2: low2)
  (z1: high1)
  (z2: high2)
: Lemma
  (rel_pair r1 r2 (w1, w2) (z1, z2) == r1 w1 z1 ** r2 w2 z2)
= ()

ghost fn rel_pair_intro
  (#tl1 #th1 #tl2 #th2: Type0)
  (r1: rel tl1 th1)
  (x1: tl1)
  (y1: th1)
  (r2: rel tl2 th2)
  (x2: tl2)
  (y2: th2)
requires r1 x1 y1 ** r2 x2 y2
ensures rel_pair r1 r2 (x1, x2) (y1, y2)
{
  rel_pair_eq r1 r2 x1 x2 y1 y2;
  rewrite (r1 x1 y1 ** r2 x2 y2) as (rel_pair r1 r2 (x1, x2) (y1, y2))
}

let rel_either
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
: rel (either low1 low2) (either high1 high2)
= mk_rel (fun xlow xhigh -> match xlow, xhigh with
  | Inl xl, Inl xh -> r1 xl xh
  | Inr xl, Inr xh -> r2 xl xh
  | _ -> pure False
)

let rel_either_eq_left
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w1: low1)
  (z1: high1)
: Lemma
  (rel_either r1 r2 (Inl w1) (Inl z1) == r1 w1 z1)
= ()

let rel_either_eq_right
  (#low1 #high1: Type)
  (r1: rel low1 high1)
  (#low2 #high2: Type)
  (r2: rel low2 high2)
  (w2: low2)
  (z2: high2)
: Lemma
  (rel_either r1 r2 (Inr w2) (Inr z2) == r2 w2 z2)
= ()

ghost fn rel_either_cases
  (#t1 #t2 #it1 #it2: Type0)
  (r1: rel it1 t1)
  (r2: rel it2 t2)
  (x: either it1 it2)
  (y: either t1 t2)
requires
  rel_either r1 r2 x y
ensures
  rel_either r1 r2 x y **
  pure (Inl? x <==> Inl? y)
{
  match x {
    Inl x1 -> {
      match y {
        Inl y1 -> {
          rewrite (rel_either r1 r2 (Inl x1) (Inl y1))
            as (rel_either r1 r2 x y)
        }
        Inr y2 -> {
          unfold (rel_either r1 r2 (Inl x1) (Inr y2));
          assert (pure False);
          rewrite emp as (rel_either r1 r2 x y)
        }
      }
    }
    Inr x2 -> {
      match y {
        Inl y1 -> {
          unfold (rel_either r1 r2 (Inr x2) (Inl y1));
          assert (pure False);
          rewrite emp as (rel_either r1 r2 x y)
        }
        Inr y2 -> {
          rewrite (rel_either r1 r2 (Inr x2) (Inr y2))
            as (rel_either r1 r2 x y)
        }
      }
    }
  }
}

let rel_either_left
  (#low1 #high: Type)
  (r1: rel low1 high)
  (#low2: Type)
  (r2: rel low2 high)
: rel (either low1 low2) high
= mk_rel (fun xlow xh -> match xlow with
  | Inl xl -> r1 xl xh
  | Inr xl -> r2 xl xh
)

let rel_option
  (#low #high: Type)
  (r: rel low high)
: rel (option low) (option high)
= mk_rel (fun x y -> match x, y with
  | Some x', Some y' -> r x' y'
  | None, None -> emp
  | _ -> pure False
)

ghost fn rel_option_cases
  (#t1 #it1: Type0)
  (r1: rel it1 t1)
  (x: option it1)
  (y: option t1)
requires
  rel_option r1 x y
ensures
  rel_option r1 x y **
  pure (Some? x <==> Some? y)
{
  match x {
    Some x1 -> {
      match y {
        Some y1 -> {
          rewrite (rel_option r1 (Some x1) (Some y1))
            as (rel_option r1 x y)
        }
        None -> {
          unfold (rel_option r1 (Some x1) None);
          assert (pure False);
          rewrite emp as (rel_option r1 x y)
        }
      }
    }
    None -> {
      match y {
        Some y1 -> {
          unfold (rel_option r1 None (Some y1));
          assert (pure False);
          rewrite emp as (rel_option r1 x y)
        }
        None -> {
          rewrite (rel_option r1 None None)
            as (rel_option r1 x y)
        }
      }
    }
  }
}

let rel_option_eq_some
  (#low #high: Type)
  (r: rel low high)
  (w: low)
  (z: high)
: Lemma
  (rel_option r (Some w) (Some z) == r w z)
= ()

let rel_option_eq_none
  (#low #high: Type)
  (r: rel low high)
: Lemma
  (rel_option r None None == emp)
= ()

ghost fn rel_option_some_intro
  (#t1 #t2: Type0)
  (r: rel t1 t2)
  (x: t1)
  (y: t2)
requires r x y
ensures rel_option r (Some x) (Some y)
{
  rel_option_eq_some r x y;
  rewrite (r x y) as (rel_option r (Some x) (Some y))
}

let rel_option_right
  (#impl #spec: Type0)
  (r: rel impl spec)
: Tot (rel impl (option spec))
= mk_rel (fun i s -> match s with
  | None -> pure False
  | Some s -> r i s
  )

let rel_fun
  (#impl #spec: Type0)
  (r: rel impl spec)
  (#impl' #spec' : Type0)
  (f_impl : impl' -> impl)
  (f_spec : spec' -> spec)
: Tot (rel impl' spec')
= mk_rel (fun i s -> r (f_impl i) (f_spec s))

let rel_bij_l
  (#left #right: Type)
  (r: rel left right)
  (#left': Type)
  (bij: Spec.bijection left left')
: rel left' right
= mk_rel (fun
  (x: left')
  (y: right) ->
   r (bij.bij_to_from x) y
)

let rel_bij_r
  (#left #right: Type)
  (r: rel left right)
  (#right': Type)
  (bij: Spec.bijection right right')
: rel left right'
= mk_rel (fun
  (x: left)
  (y: right')
->
 r x (bij.bij_to_from y)
)

let rel_slice_of_seq
  (#t: Type)
  (freeable: bool)
: rel (slice t) (Seq.seq t)
= mk_rel (fun x y -> pts_to x.s #x.p y ** pure (freeable == false))

let rel_vec_of_seq
  (#t: Type)
: rel (vec t) (Seq.seq t)
= mk_rel (fun x y -> pts_to x.v y ** pure (V.is_full_vec x.v /\ V.length x.v == U64.v x.len))

// A parser implementation that skips some data instead of reading
// it. This parser implementation has no equivalent serializer

let rel_skip (t: Type) : rel (Ghost.erased t) t =
  mk_rel (fun x y -> pure (Ghost.reveal x == y))

let rel_either_skip
  (#t: Type0)
  (#implt: Type0)
  (r: rel implt t)
  (skippable: bool)
: rel (either implt (Ghost.erased t)) t
= mk_rel (fun x y ->
  match x with
  | Inl x -> r x y
  | Inr x -> pure (Ghost.reveal x == y /\ skippable == true)
)
