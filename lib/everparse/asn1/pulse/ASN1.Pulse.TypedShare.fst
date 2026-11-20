module ASN1.Pulse.TypedShare
#lang-pulse

(* Sharing and gathering the permission of the writer relation,
   `arel false d`, as needed by the generic mixed-list iterator of LowParse
   (used by ASN1.Pulse.ListIterW to walk through a SEQUENCE OF / SET OF in
   writer form, whose elements may be held in an array). Gathering
   additionally recovers the equality of the spec values, which relies on
   the injectivity of the leaf encodings. Everything here is ghost. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawValueRel
open ASN1.Pulse.RawVRel
open ASN1.Pulse.RawVConv

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module I64 = FStar.Int64
module SB = LowParse.Spec.Base
module It = LowParse.PulseParse.Iterator
module AL = ASN1.Pulse.ParseAdb.Lemmas
module RS = ASN1.Pulse.RelShare
module RK = ASN1.Pulse.RelKeep
module T = FStar.Tactics
module Conf = ASN1.Spec.Conformance
module Ser = ASN1.Spec.Serializer

noeq
type sg (#t: Type0) (#u: Type0) (r: prel t u) = {
  sh: RS.share_t r;
  ga: RS.gather_t r;
}

(* Generic combinators *)

let sg_ext (#t #u: Type0) (r1 r2: prel t u) (sq: squash (pequiv r1 r2)) (c: sg r1) : sg r2 =
  let sq' : squash (RS.prel_equiv r1 r2) = () in
  { sh = RS.share_ext r1 r2 sq' c.sh; ga = RS.gather_ext r1 r2 sq' c.ga }

ghost
fn share_false (#t #u: Type0) (r: prel t u) (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == pure False))
: RS.share_t #t #u r
= (x: t) (#p: perm) (#y: u)
{
  eq p x y;
  rewrite (r p x y) as (pure False);
  unreachable ()
}

ghost
fn gather_false (#t #u: Type0) (r: prel t u) (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == pure False))
: RS.gather_t #t #u r
= (x: t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  eq p x y;
  rewrite (r p x y) as (pure False);
  unreachable ()
}

let sg_false (#t #u: Type0) (r: prel t u) (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == pure False)) : sg r =
  { sh = share_false r eq; ga = gather_false r eq }

(* Pure relations *)

let prel_pure (#t #u: Type0) (p: t -> u -> prop) (_: perm) (x: t) (y: u) : slprop = pure (p x y)

let pure_inj (#t #u: Type0) (p: t -> u -> prop) : prop =
  forall (x: t) (y y': u) . (p x y /\ p x y') ==> y == y'

ghost
fn share_pure (#t #u: Type0) (p: t -> u -> prop)
: RS.share_t #t #u (prel_pure p)
= (x: t) (#pm: perm) (#y: u)
{
  unfold (prel_pure p pm x y);
  fold (prel_pure p (pm /. 2.0R) x y);
  fold (prel_pure p (pm /. 2.0R) x y)
}

ghost
fn gather_pure (#t #u: Type0) (p: t -> u -> prop) (inj: squash (pure_inj p))
: RS.gather_t #t #u (prel_pure p)
= (x: t) (#pm: perm) (#y: u) (#pm': perm) (#y': u)
{
  unfold (prel_pure p pm x y);
  unfold (prel_pure p pm' x y');
  fold (prel_pure p (pm +. pm') x y)
}

let sg_pure (#t #u: Type0) (p: t -> u -> prop) (inj: squash (pure_inj p)) : sg (prel_pure p) =
  { sh = share_pure p; ga = gather_pure p inj }

let sg_bool : sg (prel_eq bool) =
  sg_ext (prel_pure (fun (x y: bool) -> x == y)) (prel_eq bool) () (sg_pure (fun (x y: bool) -> x == y) ())

let sg_small_int (bound: pos) : sg (asn1_small_int_rel bound) =
  sg_ext (prel_pure (fun (x: I64.t) (y: asn1_integer_t bound) -> I64.v x == y)) (asn1_small_int_rel bound) ()
    (sg_pure (fun (x: I64.t) (y: asn1_integer_t bound) -> I64.v x == y) ())

ghost
fn share_unit (_: unit)
: RS.share_t #unit #unit (prel_emp unit unit)
= (x: unit) (#p: perm) (#y: unit)
{
  rewrite (prel_emp unit unit p x y) as emp;
  rewrite emp as (prel_emp unit unit (p /. 2.0R) x y);
  rewrite emp as (prel_emp unit unit (p /. 2.0R) x y)
}

ghost
fn gather_unit (_: unit)
: RS.gather_t #unit #unit (prel_emp unit unit)
= (x: unit) (#p: perm) (#y: unit) (#p': perm) (#y': unit)
{
  rewrite (prel_emp unit unit p x y) as emp;
  rewrite (prel_emp unit unit p' x y') as emp;
  rewrite emp as (prel_emp unit unit (p +. p') x y)
}

let sg_unit : sg (prel_emp unit unit) = { sh = share_unit (); ga = gather_unit () }

let sg_slice (#u: Type0) (enc: u -> GTot SB.bytes) (inj: squash (RS.enc_injective enc)) : sg (prel_slice_ser enc) =
  { sh = RS.share_slice_ser enc; ga = RS.gather_slice_ser enc inj }

(* Big INTEGER, BIT STRING *)

let integer_enc_injective (bound: pos)
: Lemma (RS.enc_injective (integer_enc bound))
= let aux (y1 y2: asn1_integer_t bound) : Lemma (integer_enc bound y1 == integer_enc bound y2 ==> y1 == y2) =
    FStar.Classical.move_requires (leaf_enc_inj (ASN1_INTEGER bound) y1) y2
  in
  FStar.Classical.forall_intro_2 aux

ghost
fn share_int (bound: pos)
: RS.share_t #asn1_int_impl #(asn1_integer_t bound) (asn1_int_rel bound)
= (x: asn1_int_impl) (#p: perm) (#y: asn1_integer_t bound)
{
  match x {
    Small i -> {
      rewrite (asn1_int_rel bound p x y) as (pure (I64.v i == y));
      rewrite (pure (I64.v i == y)) as (asn1_int_rel bound (p /. 2.0R) x y);
      rewrite (pure (I64.v i == y)) as (asn1_int_rel bound (p /. 2.0R) x y)
    }
    Big s -> {
      rewrite (asn1_int_rel bound p x y) as (prel_slice_ser (integer_enc bound) p s y ** pure (~ (fits_i64 y)));
      RS.share_slice_ser (integer_enc bound) s #p #y;
      rewrite (prel_slice_ser (integer_enc bound) (p /. 2.0R) s y ** pure (~ (fits_i64 y))) as (asn1_int_rel bound (p /. 2.0R) x y);
      rewrite (prel_slice_ser (integer_enc bound) (p /. 2.0R) s y ** pure (~ (fits_i64 y))) as (asn1_int_rel bound (p /. 2.0R) x y)
    }
  }
}

ghost
fn gather_int (bound: pos)
: RS.gather_t #asn1_int_impl #(asn1_integer_t bound) (asn1_int_rel bound)
= (x: asn1_int_impl) (#p: perm) (#y: asn1_integer_t bound) (#p': perm) (#y': asn1_integer_t bound)
{
  match x {
    Small i -> {
      rewrite (asn1_int_rel bound p x y) as (pure (I64.v i == y));
      rewrite (asn1_int_rel bound p' x y') as (pure (I64.v i == y'));
      rewrite (pure (I64.v i == y)) as (asn1_int_rel bound (p +. p') x y)
    }
    Big s -> {
      rewrite (asn1_int_rel bound p x y) as (prel_slice_ser (integer_enc bound) p s y ** pure (~ (fits_i64 y)));
      rewrite (asn1_int_rel bound p' x y') as (prel_slice_ser (integer_enc bound) p' s y' ** pure (~ (fits_i64 y')));
      integer_enc_injective bound;
      RS.gather_slice_ser (integer_enc bound) () s #p #y #p' #y';
      rewrite (prel_slice_ser (integer_enc bound) (p +. p') s y ** pure (~ (fits_i64 y))) as (asn1_int_rel bound (p +. p') x y)
    }
  }
}

let sg_int (bound: pos) : sg (asn1_int_rel bound) = { sh = share_int bound; ga = gather_int bound }

let bitstring_ext (y y': asn1_bitstring_t)
: Lemma (requires (BYTES_WITH_UNUSEDBITS?.unused y == BYTES_WITH_UNUSEDBITS?.unused y' /\ BYTES_WITH_UNUSEDBITS?.b y == BYTES_WITH_UNUSEDBITS?.b y'))
  (ensures (y == y'))
= ()

ghost
fn share_bitstring (_: unit)
: RS.share_t #asn1_bitstring_impl #asn1_bitstring_t asn1_bitstring_rel
= (x: asn1_bitstring_impl) (#p: perm) (#y: asn1_bitstring_t)
{
  unfold (asn1_bitstring_rel p x y);
  S.share x.bytes;
  fold (asn1_bitstring_rel (p /. 2.0R) x y);
  fold (asn1_bitstring_rel (p /. 2.0R) x y)
}

ghost
fn gather_bitstring (_: unit)
: RS.gather_t #asn1_bitstring_impl #asn1_bitstring_t asn1_bitstring_rel
= (x: asn1_bitstring_impl) (#p: perm) (#y: asn1_bitstring_t) (#p': perm) (#y': asn1_bitstring_t)
{
  unfold (asn1_bitstring_rel p x y);
  unfold (asn1_bitstring_rel p' x y');
  S.gather x.bytes;
  bitstring_ext y y';
  fold (asn1_bitstring_rel (p +. p') x y)
}

let sg_bitstring : sg asn1_bitstring_rel = { sh = share_bitstring (); ga = gather_bitstring () }

let sg_integer (bound: pos) : sg (asn1_terminal_rel (ASN1_INTEGER bound)) =
  if small_integer bound
  then coerce_eq () (sg_small_int bound)
  else coerce_eq () (sg_int bound)

let leaf_enc_injective (k: leaf_k)
: Lemma (RS.enc_injective (leaf_enc k))
= let aux (y1 y2: asn1_terminal_t k) : Lemma (leaf_enc k y1 == leaf_enc k y2 ==> y1 == y2) =
    FStar.Classical.move_requires (leaf_enc_inj k y1) y2
  in
  FStar.Classical.forall_intro_2 aux

let sg_leaf (k: leaf_k) : sg (asn1_terminal_rel k) =
  match k with
  | ASN1_BOOLEAN -> coerce_eq () sg_bool
  | ASN1_NULL -> coerce_eq () sg_unit
  | ASN1_INTEGER bound -> sg_integer bound
  | ASN1_BITSTRING -> coerce_eq () sg_bitstring
  | _ -> leaf_enc_injective k; coerce_eq () (sg_slice (leaf_enc k) ())

let rec sg_terminal (k: asn1_terminal_k) : Tot (sg (asn1_terminal_rel k)) (decreases k) =
  match k with
  | ASN1_PREFIXED_TERMINAL _ k' -> coerce_eq () (sg_terminal k')
  | _ -> sg_leaf k

let value_enc_injective (_: unit)
: Lemma (RS.enc_injective asn1_value_enc)
= let aux (y1 y2: asn1_value) : Lemma (asn1_value_enc y1 == asn1_value_enc y2 ==> y1 == y2) =
    FStar.Classical.move_requires (asn1_value_enc_inj y1) y2
  in
  FStar.Classical.forall_intro_2 aux

let sg_any : sg (prel_slice_ser asn1_value_enc) =
  value_enc_injective ();
  sg_slice asn1_value_enc ()

(* Structural combinators *)

ghost
fn share_pair (#t1 #t2 #u1 #u2: Type0) (r1: prel t1 u1) (c1: sg r1) (r2: prel t2 u2) (c2: sg r2)
: RS.share_t #(t1 & t2) #(u1 & u2) (prel_pair r1 r2)
= (x: (t1 & t2)) (#p: perm) (#y: (u1 & u2))
{
  unfold (prel_pair r1 r2 p x y);
  c1.sh (fst x) #p #(fst y);
  c2.sh (snd x) #p #(snd y);
  fold (prel_pair r1 r2 (p /. 2.0R) x y);
  fold (prel_pair r1 r2 (p /. 2.0R) x y)
}

let pair_ext (#u1 #u2: Type0) (y y': (u1 & u2))
: Lemma (requires (fst y == fst y' /\ snd y == snd y')) (ensures (y == y'))
= ()

ghost
fn gather_pair (#t1 #t2 #u1 #u2: Type0) (r1: prel t1 u1) (c1: sg r1) (r2: prel t2 u2) (c2: sg r2)
: RS.gather_t #(t1 & t2) #(u1 & u2) (prel_pair r1 r2)
= (x: (t1 & t2)) (#p: perm) (#y: (u1 & u2)) (#p': perm) (#y': (u1 & u2))
{
  unfold (prel_pair r1 r2 p x y);
  unfold (prel_pair r1 r2 p' x y');
  c1.ga (fst x) #p #(fst y) #p' #(fst y');
  c2.ga (snd x) #p #(snd y) #p' #(snd y');
  pair_ext y y';
  fold (prel_pair r1 r2 (p +. p') x y)
}

let sg_pair (#t1 #t2 #u1 #u2: Type0) (r1: prel t1 u1) (c1: sg r1) (r2: prel t2 u2) (c2: sg r2) : sg (prel_pair r1 r2) =
  { sh = share_pair r1 c1 r2 c2; ga = gather_pair r1 c1 r2 c2 }

ghost
fn share_option (#t #u: Type0) (r: prel t u) (c: sg r)
: RS.share_t #(option t) #(option u) (prel_option r)
= (x: option t) (#p: perm) (#y: option u)
{
  match x {
    None -> {
      match y {
        None -> {
          rewrite (prel_option r p x y) as emp;
          rewrite emp as (prel_option r (p /. 2.0R) x y);
          rewrite emp as (prel_option r (p /. 2.0R) x y)
        }
        Some _ -> {
          rewrite (prel_option r p x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        None -> {
          rewrite (prel_option r p x y) as (pure False);
          unreachable ()
        }
        Some v -> {
          rewrite (prel_option r p x y) as (r p a v);
          c.sh a #p #v;
          rewrite (r (p /. 2.0R) a v) as (prel_option r (p /. 2.0R) x y);
          rewrite (r (p /. 2.0R) a v) as (prel_option r (p /. 2.0R) x y)
        }
      }
    }
  }
}

ghost
fn gather_option (#t #u: Type0) (r: prel t u) (c: sg r)
: RS.gather_t #(option t) #(option u) (prel_option r)
= (x: option t) (#p: perm) (#y: option u) (#p': perm) (#y': option u)
{
  match x {
    None -> {
      match y {
        None -> {
          match y' {
            None -> {
              rewrite (prel_option r p x y) as emp;
              rewrite (prel_option r p' x y') as emp;
              rewrite emp as (prel_option r (p +. p') x y)
            }
            Some _ -> {
              rewrite (prel_option r p' x y') as (pure False);
              unreachable ()
            }
          }
        }
        Some _ -> {
          rewrite (prel_option r p x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        None -> {
          rewrite (prel_option r p x y) as (pure False);
          unreachable ()
        }
        Some v -> {
          match y' {
            None -> {
              rewrite (prel_option r p' x y') as (pure False);
              unreachable ()
            }
            Some v' -> {
              rewrite (prel_option r p x y) as (r p a v);
              rewrite (prel_option r p' x y') as (r p' a v');
              c.ga a #p #v #p' #v';
              rewrite (r (p +. p') a v) as (prel_option r (p +. p') x y)
            }
          }
        }
      }
    }
  }
}

let sg_option (#t #u: Type0) (r: prel t u) (c: sg r) : sg (prel_option r) =
  { sh = share_option r c; ga = gather_option r c }

ghost
fn share_view (#t #ty #u: Type0) (r: prel t u) (c: sg r) (view: ty -> t)
: RS.share_t #ty #u (vview r view)
= (x: ty) (#p: perm) (#y: u)
{
  rewrite (vview r view p x y) as (r p (view x) y);
  c.sh (view x) #p #y;
  rewrite (r (p /. 2.0R) (view x) y) as (vview r view (p /. 2.0R) x y);
  rewrite (r (p /. 2.0R) (view x) y) as (vview r view (p /. 2.0R) x y)
}

ghost
fn gather_view (#t #ty #u: Type0) (r: prel t u) (c: sg r) (view: ty -> t)
: RS.gather_t #ty #u (vview r view)
= (x: ty) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  rewrite (vview r view p x y) as (r p (view x) y);
  rewrite (vview r view p' x y') as (r p' (view x) y');
  c.ga (view x) #p #y #p' #y';
  rewrite (r (p +. p') (view x) y) as (vview r view (p +. p') x y)
}

let sg_view (#t #ty #u: Type0) (r: prel t u) (c: sg r) (view: ty -> t) : sg (vview r view) =
  { sh = share_view r c view; ga = gather_view r c view }

(* A relation through an injective function of the spec value *)

ghost
fn share_via (#t #a: Type0) (ra: prel t a) (c: sg ra) (#u: Type0) (r: prel t u) (m: u -> GTot a)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == ra pm x (m y)))
: RS.share_t #t #u r
= (x: t) (#p: perm) (#y: u)
{
  eq p x y;
  eq (p /. 2.0R) x y;
  rewrite (r p x y) as (ra p x (m y));
  c.sh x #p #(m y);
  rewrite (ra (p /. 2.0R) x (m y)) as (r (p /. 2.0R) x y);
  rewrite (ra (p /. 2.0R) x (m y)) as (r (p /. 2.0R) x y)
}

ghost
fn gather_via (#t #a: Type0) (ra: prel t a) (c: sg ra) (#u: Type0) (r: prel t u) (m: u -> GTot a)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == ra pm x (m y)))
  (inj: (y: u) -> (y': u) -> Lemma (requires (m y == m y')) (ensures (y == y')))
: RS.gather_t #t #u r
= (x: t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  eq p x y;
  eq p' x y';
  eq (p +. p') x y;
  rewrite (r p x y) as (ra p x (m y));
  rewrite (r p' x y') as (ra p' x (m y'));
  c.ga x #p #(m y) #p' #(m y');
  inj y y';
  rewrite (ra (p +. p') x (m y)) as (r (p +. p') x y)
}

let sg_via (#t #a: Type0) (ra: prel t a) (c: sg ra) (#u: Type0) (r: prel t u) (m: u -> GTot a)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == ra pm x (m y)))
  (inj: (y: u) -> (y': u) -> Lemma (requires (m y == m y')) (ensures (y == y')))
: sg r
= { sh = share_via ra c r m eq; ga = gather_via ra c r m eq inj }

(* A relation guarded by a predicate on the spec value *)

ghost
fn share_cond (#t #a: Type0) (ra: prel t a) (c: sg ra) (#u: Type0) (r: prel t u) (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot a)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == (if p y then ra pm x (h y ()) else pure False)))
: RS.share_t #t #u r
= (x: t) (#pm: perm) (#y: u)
{
  eq pm x y;
  eq (pm /. 2.0R) x y;
  let bb : bool = p y;
  if bb {
    rewrite (r pm x y) as (ra pm x (h y ()));
    c.sh x #pm #(h y ());
    rewrite (ra (pm /. 2.0R) x (h y ())) as (r (pm /. 2.0R) x y);
    rewrite (ra (pm /. 2.0R) x (h y ())) as (r (pm /. 2.0R) x y)
  } else {
    rewrite (r pm x y) as (pure False);
    unreachable ()
  }
}

ghost
fn gather_cond (#t #a: Type0) (ra: prel t a) (c: sg ra) (#u: Type0) (r: prel t u) (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot a)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == (if p y then ra pm x (h y ()) else pure False)))
  (inj: (y: u) -> (y': u) -> Lemma (requires (p y == true /\ p y' == true /\ h y () == h y' ())) (ensures (y == y')))
: RS.gather_t #t #u r
= (x: t) (#pm: perm) (#y: u) (#pm': perm) (#y': u)
{
  eq pm x y;
  eq pm' x y';
  eq (pm +. pm') x y;
  let bb : bool = p y;
  let bb' : bool = p y';
  if bb {
    if bb' {
      rewrite (r pm x y) as (ra pm x (h y ()));
      rewrite (r pm' x y') as (ra pm' x (h y' ()));
      c.ga x #pm #(h y ()) #pm' #(h y' ());
      inj y y';
      rewrite (ra (pm +. pm') x (h y ())) as (r (pm +. pm') x y)
    } else {
      rewrite (r pm' x y') as (pure False);
      unreachable ()
    }
  } else {
    rewrite (r pm x y) as (pure False);
    unreachable ()
  }
}

let sg_cond (#t #a: Type0) (ra: prel t a) (c: sg ra) (#u: Type0) (r: prel t u) (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot a)
  (eq: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r pm x y == (if p y then ra pm x (h y ()) else pure False)))
  (inj: (y: u) -> (y': u) -> Lemma (requires (p y == true /\ p y' == true /\ h y () == h y' ())) (ensures (y == y')))
: sg r
= { sh = share_cond ra c r p h eq; ga = gather_cond ra c r p h eq inj }

(* A right-nested `either`, the position implying a predicate on the spec value *)

ghost
fn share_either (#th #tt #ah #at: Type0) (rh: prel th ah) (ch: sg rh) (rt: prel tt at) (ct: sg rt)
  (#u: Type0) (r: prel (either th tt) u)
  (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot ah) (tl: (y: u) -> squash (p y == false) -> GTot at)
  (eql: (pm: perm) -> (x: th) -> (y: u) -> Lemma (r pm (Inl x) y == (if p y then rh pm x (h y ()) else pure False)))
  (eqr: (pm: perm) -> (x: tt) -> (y: u) -> Lemma (r pm (Inr x) y == (if p y then pure False else rt pm x (tl y ()))))
: RS.share_t #(either th tt) #u r
= (x: either th tt) (#pm: perm) (#y: u)
{
  let bb : bool = p y;
  match x {
    Inl xh -> {
      eql pm xh y;
      eql (pm /. 2.0R) xh y;
      if bb {
        rewrite (r pm x y) as (rh pm xh (h y ()));
        ch.sh xh #pm #(h y ());
        rewrite (rh (pm /. 2.0R) xh (h y ())) as (r (pm /. 2.0R) x y);
        rewrite (rh (pm /. 2.0R) xh (h y ())) as (r (pm /. 2.0R) x y)
      } else {
        rewrite (r pm x y) as (pure False);
        unreachable ()
      }
    }
    Inr xt -> {
      eqr pm xt y;
      eqr (pm /. 2.0R) xt y;
      if bb {
        rewrite (r pm x y) as (pure False);
        unreachable ()
      } else {
        rewrite (r pm x y) as (rt pm xt (tl y ()));
        ct.sh xt #pm #(tl y ());
        rewrite (rt (pm /. 2.0R) xt (tl y ())) as (r (pm /. 2.0R) x y);
        rewrite (rt (pm /. 2.0R) xt (tl y ())) as (r (pm /. 2.0R) x y)
      }
    }
  }
}

ghost
fn gather_either (#th #tt #ah #at: Type0) (rh: prel th ah) (ch: sg rh) (rt: prel tt at) (ct: sg rt)
  (#u: Type0) (r: prel (either th tt) u)
  (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot ah) (tl: (y: u) -> squash (p y == false) -> GTot at)
  (eql: (pm: perm) -> (x: th) -> (y: u) -> Lemma (r pm (Inl x) y == (if p y then rh pm x (h y ()) else pure False)))
  (eqr: (pm: perm) -> (x: tt) -> (y: u) -> Lemma (r pm (Inr x) y == (if p y then pure False else rt pm x (tl y ()))))
  (injh: (y: u) -> (y': u) -> Lemma (requires (p y == true /\ p y' == true /\ h y () == h y' ())) (ensures (y == y')))
  (injt: (y: u) -> (y': u) -> Lemma (requires (p y == false /\ p y' == false /\ tl y () == tl y' ())) (ensures (y == y')))
: RS.gather_t #(either th tt) #u r
= (x: either th tt) (#pm: perm) (#y: u) (#pm': perm) (#y': u)
{
  let bb : bool = p y;
  let bb' : bool = p y';
  match x {
    Inl xh -> {
      eql pm xh y;
      eql pm' xh y';
      eql (pm +. pm') xh y;
      if bb {
        if bb' {
          rewrite (r pm x y) as (rh pm xh (h y ()));
          rewrite (r pm' x y') as (rh pm' xh (h y' ()));
          ch.ga xh #pm #(h y ()) #pm' #(h y' ());
          injh y y';
          rewrite (rh (pm +. pm') xh (h y ())) as (r (pm +. pm') x y)
        } else {
          rewrite (r pm' x y') as (pure False);
          unreachable ()
        }
      } else {
        rewrite (r pm x y) as (pure False);
        unreachable ()
      }
    }
    Inr xt -> {
      eqr pm xt y;
      eqr pm' xt y';
      eqr (pm +. pm') xt y;
      if bb {
        rewrite (r pm x y) as (pure False);
        unreachable ()
      } else {
        if bb' {
          rewrite (r pm' x y') as (pure False);
          unreachable ()
        } else {
          rewrite (r pm x y) as (rt pm xt (tl y ()));
          rewrite (r pm' x y') as (rt pm' xt (tl y' ()));
          ct.ga xt #pm #(tl y ()) #pm' #(tl y' ());
          injt y y';
          rewrite (rt (pm +. pm') xt (tl y ())) as (r (pm +. pm') x y)
        }
      }
    }
  }
}

let sg_either (#th #tt #ah #at: Type0) (rh: prel th ah) (ch: sg rh) (rt: prel tt at) (ct: sg rt)
  (#u: Type0) (r: prel (either th tt) u)
  (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot ah) (tl: (y: u) -> squash (p y == false) -> GTot at)
  (eql: (pm: perm) -> (x: th) -> (y: u) -> Lemma (r pm (Inl x) y == (if p y then rh pm x (h y ()) else pure False)))
  (eqr: (pm: perm) -> (x: tt) -> (y: u) -> Lemma (r pm (Inr x) y == (if p y then pure False else rt pm x (tl y ()))))
  (injh: (y: u) -> (y': u) -> Lemma (requires (p y == true /\ p y' == true /\ h y () == h y' ())) (ensures (y == y')))
  (injt: (y: u) -> (y': u) -> Lemma (requires (p y == false /\ p y' == false /\ tl y () == tl y' ())) (ensures (y == y')))
: sg r
= { sh = share_either rh ch rt ct r p h tl eql eqr; ga = gather_either rh ch rt ct r p h tl eql eqr injh injt }

(* DEFAULT *)

ghost
fn share_default (#t: Type0) (#u: eqtype) (r: prel t u) (c: sg r) (defv: u)
: RS.share_t #(option t) #(default_tv defv) (RS.prel_default r defv)
= (x: option t) (#p: perm) (#y: default_tv defv)
{
  match x {
    None -> {
      match y {
        Default -> {
          rewrite (RS.prel_default r defv p x y) as emp;
          rewrite emp as (RS.prel_default r defv (p /. 2.0R) x y);
          rewrite emp as (RS.prel_default r defv (p /. 2.0R) x y)
        }
        Nondefault _ -> {
          rewrite (RS.prel_default r defv p x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        Default -> {
          rewrite (RS.prel_default r defv p x y) as (pure False);
          unreachable ()
        }
        Nondefault v -> {
          rewrite (RS.prel_default r defv p x y) as (r p a v);
          c.sh a #p #v;
          rewrite (r (p /. 2.0R) a v) as (RS.prel_default r defv (p /. 2.0R) x y);
          rewrite (r (p /. 2.0R) a v) as (RS.prel_default r defv (p /. 2.0R) x y)
        }
      }
    }
  }
}

ghost
fn gather_default (#t: Type0) (#u: eqtype) (r: prel t u) (c: sg r) (defv: u)
: RS.gather_t #(option t) #(default_tv defv) (RS.prel_default r defv)
= (x: option t) (#p: perm) (#y: default_tv defv) (#p': perm) (#y': default_tv defv)
{
  match x {
    None -> {
      match y {
        Default -> {
          match y' {
            Default -> {
              rewrite (RS.prel_default r defv p x y) as emp;
              rewrite (RS.prel_default r defv p' x y') as emp;
              rewrite emp as (RS.prel_default r defv (p +. p') x y)
            }
            Nondefault _ -> {
              rewrite (RS.prel_default r defv p' x y') as (pure False);
              unreachable ()
            }
          }
        }
        Nondefault _ -> {
          rewrite (RS.prel_default r defv p x y) as (pure False);
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        Default -> {
          rewrite (RS.prel_default r defv p x y) as (pure False);
          unreachable ()
        }
        Nondefault v -> {
          match y' {
            Default -> {
              rewrite (RS.prel_default r defv p' x y') as (pure False);
              unreachable ()
            }
            Nondefault v' -> {
              rewrite (RS.prel_default r defv p x y) as (r p a v);
              rewrite (RS.prel_default r defv p' x y') as (r p' a v');
              c.ga a #p #v #p' #v';
              rewrite (r (p +. p') a v) as (RS.prel_default r defv (p +. p') x y)
            }
          }
        }
      }
    }
  }
}

let sg_default (#t: Type0) (#u: eqtype) (r: prel t u) (c: sg r) (defv: u) : sg (RS.prel_default r defv) =
  { sh = share_default r c defv; ga = gather_default r c defv }

(* SEQUENCE OF / SET OF *)

ghost
fn share_list (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: sg (arel false d))
  (#u: Type0) (r: prel (ml t) u) (g: u -> GTot (list (asn1_t k)))
  (eq: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r pm x y == tml_rel false d pm x (g y)))
: RS.share_t #(ml t) #u r
= (x: ml t) (#p: perm) (#y: u)
{
  eq p x y;
  eq (p /. 2.0R) x y;
  rewrite (r p x y) as (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p x (g y));
  It.mixed_list_match_share (arel false d) ml_ops (asn1_as_parser k) p x (g y) c.sh;
  rewrite (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p /. 2.0R) x (g y)) as (r (p /. 2.0R) x y);
  rewrite (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p /. 2.0R) x (g y)) as (r (p /. 2.0R) x y)
}

ghost
fn gather_list (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: sg (arel false d))
  (#u: Type0) (r: prel (ml t) u) (g: u -> GTot (list (asn1_t k)))
  (eq: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r pm x y == tml_rel false d pm x (g y)))
  (inj: (y: u) -> (y': u) -> Lemma (requires (g y == g y')) (ensures (y == y')))
: RS.gather_t #(ml t) #u r
= (x: ml t) (#p: perm) (#y: u) (#p': perm) (#y': u)
{
  eq p x y;
  eq p' x y';
  eq (p +. p') x y;
  rewrite (r p x y) as (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p x (g y));
  rewrite (r p' x y') as (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) p' x (g y'));
  It.mixed_list_match_gather (arel false d) ml_ops (asn1_as_parser k) p p' x (g y) (g y') c.ga;
  inj y y';
  rewrite (It.mixed_list_match (arel false d) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) (p +. p') x (g y)) as (r (p +. p') x y)
}

let sg_list (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: sg (arel false d))
  (#u: Type0) (r: prel (ml t) u) (g: u -> GTot (list (asn1_t k)))
  (eq: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r pm x y == tml_rel false d pm x (g y)))
  (inj: (y: u) -> (y': u) -> Lemma (requires (g y == g y')) (ensures (y == y')))
: sg r
= { sh = share_list d c r g eq; ga = gather_list d c r g eq inj }

let sg_seq_of (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: sg (arel false d))
: sg (crel false (CD_SEQUENCE_OF ne d))
= sg_list d c (crel false (CD_SEQUENCE_OF ne d)) (RS.seq_of_up ne k)
    (fun pm x y -> tcontent_seq_of_eq false ne d pm x y)
    (fun y y' -> ())

let sg_set_of (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (c: sg (arel false d))
: sg (crel false (CD_SET_OF ne d))
= sg_list d c (crel false (CD_SET_OF ne d)) (RS.set_of_up ne k)
    (fun pm x y -> tcontent_set_of_eq false ne d pm x y)
    (fun y y' -> ())

(* KEEP-BYTES *)

#push-options "--fuel 0 --ifuel 1"
ghost
fn share_keep_rel (#s: _) (k: asn1_k s)
: RS.share_t #(option (S.slice U8.t)) #(asn1_t k) (keep_rel k)
= (x: option (S.slice U8.t)) (#p: perm) (#y: asn1_t k)
{
  match x {
    None -> {
      rewrite (keep_rel k p x y) as emp;
      rewrite emp as (keep_rel k (p /. 2.0R) x y);
      rewrite emp as (keep_rel k (p /. 2.0R) x y)
    }
    Some sl -> {
      rewrite (keep_rel k p x y) as (pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) p sl y);
      RS.share_slice_ser (Ser.asn1_enc k) sl #p #y;
      rewrite (pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) (p /. 2.0R) sl y) as (keep_rel k (p /. 2.0R) x y);
      rewrite (pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) (p /. 2.0R) sl y) as (keep_rel k (p /. 2.0R) x y)
    }
  }
}

ghost
fn gather_keep_rel (#s: _) (k: asn1_k s) (x: option (S.slice U8.t)) (p p': perm) (y: asn1_t k)
requires keep_rel k p x y ** keep_rel k p' x y
ensures keep_rel k (p +. p') x y
{
  match x {
    None -> {
      rewrite (keep_rel k p x y) as emp;
      rewrite (keep_rel k p' x y) as emp;
      rewrite emp as (keep_rel k (p +. p') x y)
    }
    Some sl -> {
      rewrite (keep_rel k p x y) as (pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) p sl y);
      rewrite (keep_rel k p' x y) as (pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) p' sl y);
      unfold (prel_slice_ser (Ser.asn1_enc k) p sl y);
      unfold (prel_slice_ser (Ser.asn1_enc k) p' sl y);
      S.gather sl;
      fold (prel_slice_ser (Ser.asn1_enc k) (p +. p') sl y);
      rewrite (pure (Ser.encodable k y) ** prel_slice_ser (Ser.asn1_enc k) (p +. p') sl y) as (keep_rel k (p +. p') x y)
    }
  }
}

#pop-options

ghost
fn share_keep (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k)) (c: sg (arel false d))
: RS.share_t #(kept t) #(asn1_t k) (arel false (D_KEEP d wf))
= (x: kept t) (#p: perm) (#y: asn1_t k)
{
  RK.keep_eq false d wf p x y;
  RK.keep_eq false d wf (p /. 2.0R) x y;
  rewrite (arel false (D_KEEP d wf) p x y) as (arel false d (p /. 2.0R) x.kval y ** keep_rel k (p /. 2.0R) x.kraw y);
  c.sh x.kval #(p /. 2.0R) #y;
  share_keep_rel k x.kraw #(p /. 2.0R) #y;
  rewrite (arel false d ((p /. 2.0R) /. 2.0R) x.kval y ** keep_rel k ((p /. 2.0R) /. 2.0R) x.kraw y) as (arel false (D_KEEP d wf) (p /. 2.0R) x y);
  rewrite (arel false d ((p /. 2.0R) /. 2.0R) x.kval y ** keep_rel k ((p /. 2.0R) /. 2.0R) x.kraw y) as (arel false (D_KEEP d wf) (p /. 2.0R) x y)
}

ghost
fn gather_keep (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k)) (c: sg (arel false d))
: RS.gather_t #(kept t) #(asn1_t k) (arel false (D_KEEP d wf))
= (x: kept t) (#p: perm) (#y: asn1_t k) (#p': perm) (#y': asn1_t k)
{
  RK.keep_eq false d wf p x y;
  RK.keep_eq false d wf p' x y';
  RK.keep_eq false d wf (p +. p') x y;
  rewrite (arel false (D_KEEP d wf) p x y) as (arel false d (p /. 2.0R) x.kval y ** keep_rel k (p /. 2.0R) x.kraw y);
  rewrite (arel false (D_KEEP d wf) p' x y') as (arel false d (p' /. 2.0R) x.kval y' ** keep_rel k (p' /. 2.0R) x.kraw y');
  c.ga x.kval #(p /. 2.0R) #y #(p' /. 2.0R) #y';
  rewrite (keep_rel k (p' /. 2.0R) x.kraw y') as (keep_rel k (p' /. 2.0R) x.kraw y);
  gather_keep_rel k x.kraw (p /. 2.0R) (p' /. 2.0R) y;
  assert (pure ((p +. p') /. 2.0R == p /. 2.0R +. p' /. 2.0R));
  rewrite (arel false d (p /. 2.0R +. p' /. 2.0R) x.kval y ** keep_rel k (p /. 2.0R +. p' /. 2.0R) x.kraw y) as (arel false (D_KEEP d wf) (p +. p') x y)
}

let sg_keep (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k)) (c: sg (arel false d)) : sg (arel false (D_KEEP d wf)) =
  { sh = share_keep d wf c; ga = gather_keep d wf c }

(* Restricted terminals *)

let sg_restricted (k: asn1_terminal_k) (r: asn1_restriction k) : sg #(asn1_terminal_impl_t k) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) =
  sg_via (asn1_terminal_rel k) (sg_terminal k) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r)) (RS.restricted_up k r)
    (fun pm x y -> RS.content_restricted_eq k r pm x y)
    (fun y y' -> ())

(* Dependent pairs: CHOICE and ANY DEFINED BY values *)

let dtuple2_ext (#a: Type) (#b: a -> Type) (v v': dtuple2 a b)
: Lemma (requires (dfst v == dfst v' /\ dsnd v === dsnd v')) (ensures (v == v'))
= ()

(* One type per kind of descriptor *)

let sa_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type = sg (arel false d)
let sc_t (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t) : Type = sg (crel false cd)
let sd_t (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t) : Type = sg (drel false dd)
let si_t (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t) : Type = sg (irel false di)
let slc_t (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t) : Type = sg (lcrel false ld)
let ssx_t (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t) : Type =
  sg #t #(AL.ady key_k ls) (sxrel false dsx)
let sfx_t (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t) : Type =
  sg #t #(AL.ady_fb key_k ls gfb) (fxrel false dfx (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
let sia_t (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs: Type0) (sfx: prel sfxi sfxs) : Type =
  sg (iarel false dpre #sfxs sfx)

(* CHOICE alternatives *)

let sg_lc_nil : slc_t LC_NIL =
  sg_false (lcrel false LC_NIL) (tlc_nil_eq false)

let sg_lc_single (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t) (cc: sc_t cd)
: slc_t (LC_SINGLE id' cd)
= sg_cond (crel false cd) cc (lcrel false (LC_SINGLE id' cd))
    (fun v -> dfst v = id') (fun v _ -> RS.lc_head_val id' c [] v ())
    (tlc_single_eq false id' cd)
    (fun v v' -> dtuple2_ext v v')

let sg_lc_cons (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (cc: sc_t cd) (ct: slc_t dtl)
: slc_t (LC_CONS id' cd dtl)
= sg_either (crel false cd) cc (lcrel false dtl) ct (lcrel false (LC_CONS id' cd dtl))
    (fun v -> dfst v = id') (fun v _ -> RS.lc_head_val id' c (hd2 :: tl2) v ()) (fun v _ -> RS.lc_tail_val (id', c) (hd2 :: tl2) v ())
    (tlc_cons_inl_eq false id' cd dtl) (tlc_cons_inr_eq false id' cd dtl)
    (fun v v' -> dtuple2_ext v v')
    (fun v v' -> dtuple2_ext v v')

(* ANY DEFINED BY *)

let sg_sx_nil (key_k: asn1_terminal_k) : ssx_t (SX_NIL key_k) =
  sg_false (sxrel false (SX_NIL key_k)) (tadb_nil_eq false #key_k)

let sg_sx_single (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t)
  (ci: si_t di)
: ssx_t (SX_SINGLE key_k kx y di)
= sg_cond (irel false di) ci (sxrel false (SX_SINGLE key_k kx y di))
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_head_val kx y [] v ())
    (tadb_single_eq false kx y di)
    (fun v v' -> dtuple2_ext v v')

let sg_sx_cons (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (ci: si_t di) (ct: ssx_t dtl)
: ssx_t (SX_CONS key_k kx y di dtl)
= sg_either (irel false di) ci (sxrel false dtl) ct (sxrel false (SX_CONS key_k kx y di dtl))
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_head_val kx y (hd2 :: tl2) v ()) (fun v _ -> AL.ady_tail_val kx y (hd2 :: tl2) v ())
    (tadb_cons_inl_eq false kx y di dtl) (tadb_cons_inr_eq false kx y di dtl)
    (fun v v' -> dtuple2_ext v v')
    (fun v v' -> dtuple2_ext v v')

(* ANY DEFINED BY, with a fallback *)

let sg_fx_nil (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (cf: si_t dfb)
: sfx_t dfb (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb))
= sg_via (prel_pair (asn1_terminal_rel key_k) (irel false dfb))
    (sg_pair (asn1_terminal_rel key_k) (sg_terminal key_k) (irel false dfb) cf)
    (fxrel false (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (fun v -> (dfst v, AL.ady_fb_nil_val gfb v))
    (tafb_nil_eq false key_k dfb)
    (fun v v' -> dtuple2_ext v v')

let sg_fx_single (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (ci: si_t di) (cf: si_t dfb)
: sfx_t dfb (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb))
= sg_either (irel false di) ci
    (fxrel false (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (sg_fx_nil key_k dfb cf)
    (fxrel false (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_fb_head_val kx y [] gfb v ()) (fun v _ -> AL.ady_fb_tail_val kx y [] gfb v ())
    (tafb_single_inl_eq false kx y di gfb (tfbr false key_k dfb)) (tafb_single_inr_eq false kx y di gfb (tfbr false key_k dfb))
    (fun v v' -> dtuple2_ext v v')
    (fun v v' -> dtuple2_ext v v')

let sg_fx_cons (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2)
  (ci: si_t di) (ct: sfx_t dfb dtl)
: sfx_t dfb (FX_CONS key_k kx y di dtl)
= sg_either (irel false di) ci
    (fxrel false dtl (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb)) ct
    (fxrel false (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_fb_head_val kx y (hd2 :: tl2) gfb v ()) (fun v _ -> AL.ady_fb_tail_val kx y (hd2 :: tl2) gfb v ())
    (tafb_cons_inl_eq false kx y di dtl gfb (tfbr false key_k dfb)) (tafb_cons_inr_eq false kx y di dtl gfb (tfbr false key_k dfb))
    (fun v v' -> dtuple2_ext v v')
    (fun v v' -> dtuple2_ext v v')

(* By mutual recursion on the descriptor *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec sg_a (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Tot (sa_t d) (decreases d)
= match d with
  | D_ILC id cd ->
    trel_ilc_equiv false id cd;
    sg_ext (crel false cd) (arel false d) () (sg_c cd)
  | D_CHOICE lc pf ld ->
    trel_choice_equiv false lc pf ld;
    sg_ext (lcrel false ld) (arel false d) () (sg_lc ld)
  | D_ANY ->
    trel_any_equiv false ();
    sg_ext (prel_slice_ser asn1_value_enc) (arel false d) () sg_any
  | D_VIEW d' ty view mk law ->
    trel_view_equiv false d' ty view mk law;
    sg_ext (vview (arel false d') view) (arel false d) () (sg_view (arel false d') (sg_a d') view)
  | D_KEEP d' wf ->
    sg_keep d' wf (sg_a d')

and sg_c (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t)
: Tot (sc_t cd) (decreases cd)
= match cd with
  | CD_TERMINAL k' ->
    tcontent_terminal_equiv false k';
    sg_ext (asn1_terminal_rel k') (crel false cd) () (sg_terminal k')
  | CD_RESTRICTED k' r ->
    tcontent_restricted_equiv false k' r;
    sg_ext (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (crel false cd) () (sg_restricted k' r)
  | CD_PREFIXED d' ->
    tcontent_prefixed_equiv false d';
    sg_ext (arel false d') (crel false cd) () (sg_a d')
  | CD_SEQUENCE gitems di ->
    tcontent_sequence_equiv false gitems di;
    sg_ext (irel false di) (crel false cd) () (sg_i di)
  | CD_SET ids items pf di ->
    tcontent_set_equiv false ids items pf di;
    sg_ext (irel false di) (crel false cd) () (sg_i di)
  | CD_SEQUENCE_OF ne d' ->
    sg_seq_of ne d' (sg_a d')
  | CD_SET_OF ne d' ->
    sg_set_of ne d' (sg_a d')
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    tcontent_adb_none_equiv false ipd prefix kid key_k ls pf pf' dsx dpre;
    sg_ext (iarel false dpre #(AL.ady key_k ls) (sxrel false dsx)) (crel false cd) ()
      (sg_ia dpre (sxrel false dsx) (sg_sx dsx))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' #tfb dfb dfx dpre ->
    tcontent_adb_some_equiv false ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    sg_ext (iarel false dpre #(AL.ady_fb key_k ls fb) (fxrel false dfx (asn1_sequence_t_core (dsnd fb)) (tfbr false key_k #fb dfb))) (crel false cd) ()
      (sg_ia dpre (fxrel false dfx (asn1_sequence_t_core (dsnd fb)) (tfbr false key_k #fb dfb)) (sg_fx dfb (sg_i dfb) dfx))
  | CD_VIEW d' ty view mk law ->
    tcontent_view_equiv false d' ty view mk law;
    sg_ext (vview (crel false d') view) (crel false cd) () (sg_view (crel false d') (sg_c d') view)

and sg_sx (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t)
: Tot (ssx_t dsx) (decreases dsx)
= match dsx with
  | SX_NIL _ -> sg_sx_nil key_k
  | SX_SINGLE _ kx y di -> sg_sx_single kx y di (sg_i di)
  | SX_CONS _ kx y di dtl -> sg_sx_cons kx y di dtl (sg_i di) (sg_sx dtl)

and sg_fx (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (cf: si_t dfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t)
: Tot (sfx_t dfb dfx) (decreases dfx)
= match dfx with
  | FX_NIL _ -> sg_fx_nil key_k dfb cf
  | FX_SINGLE _ kx y di -> sg_fx_single kx y di dfb (sg_i di) cf
  | FX_CONS _ kx y di dtl -> sg_fx_cons kx y di dfb dtl (sg_i di) (sg_fx dfb cf dtl)

and sg_ia (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs: Type0) (sfx: prel sfxi sfxs) (cs: sg sfx)
: Tot (sia_t dpre sfx) (decreases dpre)
= match dpre with
  | IA_NIL ->
    titems_any_nil_equiv false sfx;
    sg_ext sfx (iarel false dpre sfx) () cs
  | IA_SINGLE dd ->
    titems_any_single_equiv false dd sfx;
    sg_ext (prel_pair (drel false dd) sfx) (iarel false dpre sfx) ()
      (sg_pair (drel false dd) (sg_d dd) sfx cs)
  | IA_CONS dd dtl ->
    titems_any_cons_equiv false dd dtl sfx;
    sg_ext (prel_pair (drel false dd) (iarel false dtl sfx)) (iarel false dpre sfx) ()
      (sg_pair (drel false dd) (sg_d dd) (iarel false dtl sfx) (sg_ia dtl sfx cs))

and sg_lc (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t)
: Tot (slc_t ld) (decreases ld)
= match ld with
  | LC_NIL -> sg_lc_nil
  | LC_SINGLE id' cd -> sg_lc_single id' cd (sg_c cd)
  | LC_CONS id' cd dtl -> sg_lc_cons id' cd dtl (sg_c cd) (sg_lc dtl)

and sg_d (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t)
: Tot (sd_t dd) (decreases dd)
= match dd with
  | DD_PLAIN d' ->
    tdec_plain_equiv false d';
    sg_ext (arel false d') (drel false dd) () (sg_a d')
  | DD_OPTION d' ->
    tdec_option_equiv false d';
    sg_ext (prel_option (arel false d')) (drel false dd) () (sg_option (arel false d') (sg_a d'))
  | DD_DEFAULT id0 #k' defv ->
    tdec_default_equiv false id0 defv;
    sg_ext (RS.prel_default (asn1_terminal_rel k') (key_of_lit k' defv)) (drel false dd) ()
      (sg_default (asn1_terminal_rel k') (sg_terminal k') (key_of_lit k' defv))
  | DD_DEFAULT_RESTRICTED id0 #k' r defv ->
    tdec_default_restricted_equiv false id0 r defv;
    sg_ext (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (key_of_lit k' defv)) (drel false dd) ()
      (sg_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (sg_restricted k' r) (key_of_lit k' defv))
  | DD_VIEW d' ty view mk law ->
    tdec_view_equiv false d' ty view mk law;
    sg_ext (vview (drel false d') view) (drel false dd) () (sg_view (drel false d') (sg_d d') view)

and sg_i (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t)
: Tot (si_t di) (decreases di)
= match di with
  | ID_NIL ->
    titems_nil_equiv false ();
    sg_ext (prel_emp unit unit) (irel false di) () sg_unit
  | ID_SINGLE dd ->
    titems_single_equiv false dd;
    sg_ext (drel false dd) (irel false di) () (sg_d dd)
  | ID_CONS dd dtl ->
    titems_cons_equiv false dd dtl;
    sg_ext (prel_pair (drel false dd) (irel false dtl)) (irel false di) ()
      (sg_pair (drel false dd) (sg_d dd) (irel false dtl) (sg_i dtl))
#pop-options

(* The main results *)

let share_d (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : RS.share_t (arel false d) = (sg_a d).sh
let gather_d (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : RS.gather_t (arel false d) = (sg_a d).ga
