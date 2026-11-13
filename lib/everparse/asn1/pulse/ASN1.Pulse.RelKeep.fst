module ASN1.Pulse.RelKeep
#lang-pulse

(* From the relation ensured by parsers, `arel true d`, to the relation
   required by writers, `arel false d`, with a trade back.

   `arel true d pm x y` holds `arel false d pm x y` together with the pure
   fact `kept_a d x`: every KEEP-BYTES node reachable without crossing a
   SEQUENCE OF / SET OF carries its bytes, and every SEQUENCE OF / SET OF is
   a serialized chunk of the input (so the relation of its elements is
   irrelevant). Since `kept_a d x` is pure, it can be kept as the frame of
   the trade: `to_writer` lets a user hand a parsed value to a writer, then
   recover the relation of the parser. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawValueRel
open ASN1.Pulse.RawVRel
open ASN1.Pulse.RawVConv

module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module SB = LowParse.Spec.Base
module It = LowParse.PulseParse.Iterator
module ItT = LowParse.PulseParse.Iterator.Type
module AL = ASN1.Pulse.ParseAdb.Lemmas
module RS = ASN1.Pulse.RelShare
module T = FStar.Tactics
module Trade = Pulse.Lib.Trade
module Conf = ASN1.Spec.Conformance

(* The pure facts of `arel true` that `arel false` lacks *)

let ktrue (t: Type0) (x: t) : prop = True

let kpair (#t1 #t2: Type0) (kp1: t1 -> prop) (kp2: t2 -> prop) (x: t1 & t2) : prop =
  kp1 (fst x) /\ kp2 (snd x)

let kopt (#t: Type0) (kp: t -> prop) (x: option t) : prop =
  match x with
  | None -> True
  | Some a -> kp a

let keither (#t1 #t2: Type0) (kp1: t1 -> prop) (kp2: t2 -> prop) (x: either t1 t2) : prop =
  match x with
  | Inl a -> kp1 a
  | Inr b -> kp2 b

let kview (#t #ty: Type0) (kp: t -> prop) (view: ty -> t) (x: ty) : prop =
  kp (view x)

let kkeep (#t: Type0) (kp: t -> prop) (x: kept t) : prop =
  Some? x.kraw /\ kp x.kval

let rec kept_a (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (x: t) : Tot prop (decreases d) =
  match d with
  | D_ILC _ cd -> kept_c cd x
  | D_CHOICE _ _ ld -> kept_lc ld x
  | D_ANY -> True
  | D_VIEW d' _ view _ _ -> kept_a d' (view x)
  | D_KEEP #_ #_ #t' d' _ ->
    let x' : kept t' = x in
    Some? x'.kraw /\ kept_a d' x'.kval

and kept_c (#k: asn1_content_k) (#t: Type0) (d: cdesc k t) (x: t) : Tot prop (decreases d) =
  match d with
  | CD_TERMINAL _ -> True
  | CD_RESTRICTED _ _ -> True
  | CD_SEQUENCE _ ld -> kept_i ld x
  | CD_SET _ _ _ ld -> kept_i ld x
  | CD_SEQUENCE_OF _ #_ #_ #t' _ -> is_serialized #t' x
  | CD_SET_OF _ #_ #_ #t' _ -> is_serialized #t' x
  | CD_PREFIXED d' -> kept_a d' x
  | CD_ADB_NONE _ _ _ _ _ _ _ dsx dpre ->
    kept_ia dpre (fun s -> kept_sx dsx s) x
  | CD_ADB_SOME _ _ _ key_k _ _ _ _ #tfb dfb dfx dpre ->
    kept_ia dpre (fun s -> kept_fx dfx (fun (z: asn1_terminal_impl_t key_k & tfb) -> kept_i dfb (snd z)) s) x
  | CD_VIEW d' _ view _ _ -> kept_c d' (view x)

and kept_sx (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t) (x: t)
: Tot prop (decreases d)
= match d with
  | SX_NIL _ -> True
  | SX_SINGLE _ _ _ di -> kept_i di x
  | SX_CONS _ _ _ #t1 di #_ #_ #t2 dtl ->
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> kept_i di a
    | Inr b -> kept_sx dtl b
    end

and kept_fx (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (kfb: fbt -> prop) (x: t)
: Tot prop (decreases d)
= match d with
  | FX_NIL _ -> kfb x
  | FX_SINGLE _ _ _ #t1 di ->
    let x' : either t1 fbt = x in
    begin match x' with
    | Inl a -> kept_i di a
    | Inr b -> kfb b
    end
  | FX_CONS _ _ _ #t1 di #_ #_ #_ #t2 dtl ->
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> kept_i di a
    | Inr b -> kept_fx dtl kfb b
    end

and kept_ia (#ids: _) (#ls: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (d: iadesc ls sfxi t) (ksfx: sfxi -> prop) (x: t)
: Tot prop (decreases d)
= match d with
  | IA_NIL -> ksfx x
  | IA_SINGLE #_ #_ #_ #t1 dd ->
    let x' : t1 & sfxi = x in
    kept_d dd (fst x') /\ ksfx (snd x')
  | IA_CONS #_ #_ #_ #t1 dd #_ #_ #_ #_ #_ #_ #t2 dtl ->
    let x' : t1 & t2 = x in
    kept_d dd (fst x') /\ kept_ia dtl ksfx (snd x')

and kept_lc (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (d: lcdesc lc t) (x: t) : Tot prop (decreases d) =
  match d with
  | LC_NIL -> True
  | LC_SINGLE _ cd -> kept_c cd x
  | LC_CONS _ #_ #t1 cd #_ #_ #t2 dtl ->
    let x' : either t1 t2 = x in
    begin match x' with
    | Inl a -> kept_c cd a
    | Inr b -> kept_lc dtl b
    end

and kept_d (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (d: ddesc dk t) (x: t) : Tot prop (decreases d) =
  match d with
  | DD_PLAIN d' -> kept_a d' x
  | DD_OPTION #_ #_ #t' d' ->
    let x' : option t' = x in
    begin match x' with
    | None -> True
    | Some a -> kept_a d' a
    end
  | DD_DEFAULT _ _ -> True
  | DD_DEFAULT_RESTRICTED _ _ _ -> True
  | DD_VIEW d' _ view _ _ -> kept_d d' (view x)

and kept_i (#ids: _) (#ls: asn1_gen_items_l ids) (#t: Type0) (d: idesc ls t) (x: t) : Tot prop (decreases d) =
  match d with
  | ID_NIL -> True
  | ID_SINGLE dd -> kept_d dd x
  | ID_CONS #_ #_ #_ #t1 dd #_ #_ #_ #_ #_ #t2 dtl ->
    let x' : t1 & t2 = x in
    kept_d dd (fst x') /\ kept_i dtl (snd x')

(* The ANY DEFINED BY cases involve lambdas, which SMT does not unfold *)

let kept_c_adb_none_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#ts: Type0) (dsx: sxdesc key_k ls ts) (#t: Type0) (dpre: iadesc prefix ts t) (x: t)
: Lemma (kept_c (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre) x <==> kept_ia dpre (fun s -> kept_sx dsx s) x)
= assert (kept_c (CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre) x == kept_ia dpre (fun s -> kept_sx dsx s) x)
    by (T.norm [delta_only [`%kept_c]; zeta; iota]; T.trefl ())

let kept_c_adb_some_eq (ipd: id_decs) (prefix: asn1_gen_items_l ipd) (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FStar.Set.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (#tfb: Type0) (dfb: idesc (dsnd fb) tfb)
  (#ts: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) ts) (#t: Type0) (dpre: iadesc prefix ts t) (x: t)
: Lemma (kept_c (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre) x <==>
    kept_ia dpre (fun s -> kept_fx dfx (fun (z: asn1_terminal_impl_t key_k & tfb) -> kept_i dfb (snd z)) s) x)
= assert (kept_c (CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre) x ==
    kept_ia dpre (fun s -> kept_fx dfx (fun (z: asn1_terminal_impl_t key_k & tfb) -> kept_i dfb (snd z)) s) x)
    by (T.norm [delta_only [`%kept_c]; zeta; iota]; T.trefl ())

(* Conversions between `r1` (the relation with `kb = true`) and `r2` (with
   `kb = false`), in direction `b` (`true`: weaken, from `r1` to `r2`,
   ensuring `kp x`; `false`: restore, from `r2` to `r1`, requiring `kp x`) *)

let kc_t (b: bool) (#t #u: Type0) (r1 r2: prel t u) (kp: t -> prop) : Type =
  (pm: perm) -> (x: t) -> (y: u) -> squash (b == false ==> kp x) ->
  stt_ghost unit emp_inames (cv b (r1 pm x y) (r2 pm x y)) (fun _ -> cv b (r2 pm x y) (r1 pm x y) ** pure (b == true ==> kp x))

ghost
fn kc_ext (b: bool) (#t #u: Type0) (r1 r1' r2 r2': prel t u) (kp kp': t -> prop)
  (sq: squash (pequiv r1 r1' /\ pequiv r2 r2'))
  (eqk: (x: t) -> Lemma (kp x <==> kp' x))
  (c: kc_t b r1 r2 kp)
: kc_t b r1' r2' kp'
= (pm: perm) (x: t) (y: u) (sq': squash (b == false ==> kp' x))
{
  eqk x;
  rewrite (cv b (r1' pm x y) (r2' pm x y)) as (cv b (r1 pm x y) (r2 pm x y));
  c pm x y ();
  rewrite (cv b (r2 pm x y) (r1 pm x y)) as (cv b (r2' pm x y) (r1' pm x y))
}

ghost
fn kc_refl (b: bool) (#t #u: Type0) (r: prel t u)
: kc_t b r r (ktrue t)
= (pm: perm) (x: t) (y: u) (sq': squash (b == false ==> ktrue t x))
{
  ()
}

ghost
fn kc_false (b: bool) (#t #u: Type0) (r1 r2: prel t u) (kp: t -> prop)
  (eq1: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r1 pm x y == pure False))
  (eq2: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r2 pm x y == pure False))
: kc_t b r1 r2 kp
= (pm: perm) (x: t) (y: u) (sq': squash (b == false ==> kp x))
{
  eq1 pm x y;
  eq2 pm x y;
  rewrite (cv b (r1 pm x y) (r2 pm x y)) as (pure False);
  unreachable ()
}

ghost
fn kc_pair (b: bool) (#t1 #t2 #u1 #u2: Type0)
  (ra1 ra2: prel t1 u1) (kpa: t1 -> prop) (ca: kc_t b ra1 ra2 kpa)
  (rb1 rb2: prel t2 u2) (kpb: t2 -> prop) (cb: kc_t b rb1 rb2 kpb)
: kc_t b (prel_pair ra1 rb1) (prel_pair ra2 rb2) (kpair kpa kpb)
= (pm: perm) (x: (t1 & t2)) (y: (u1 & u2)) (sq': squash (b == false ==> kpair kpa kpb x))
{
  cv_star b (ra1 pm (fst x) (fst y)) (rb1 pm (snd x) (snd y)) (ra2 pm (fst x) (fst y)) (rb2 pm (snd x) (snd y));
  rewrite (cv b (prel_pair ra1 rb1 pm x y) (prel_pair ra2 rb2 pm x y))
    as (cv b (ra1 pm (fst x) (fst y)) (ra2 pm (fst x) (fst y)) ** cv b (rb1 pm (snd x) (snd y)) (rb2 pm (snd x) (snd y)));
  ca pm (fst x) (fst y) ();
  cb pm (snd x) (snd y) ();
  cv_star b (ra2 pm (fst x) (fst y)) (rb2 pm (snd x) (snd y)) (ra1 pm (fst x) (fst y)) (rb1 pm (snd x) (snd y));
  rewrite (cv b (ra2 pm (fst x) (fst y)) (ra1 pm (fst x) (fst y)) ** cv b (rb2 pm (snd x) (snd y)) (rb1 pm (snd x) (snd y)))
    as (cv b (prel_pair ra2 rb2 pm x y) (prel_pair ra1 rb1 pm x y))
}

ghost
fn kc_option (b: bool) (#t #u: Type0) (r1 r2: prel t u) (kp: t -> prop) (c: kc_t b r1 r2 kp)
: kc_t b (prel_option r1) (prel_option r2) (kopt kp)
= (pm: perm) (x: option t) (y: option u) (sq': squash (b == false ==> kopt kp x))
{
  match x {
    None -> {
      match y {
        None -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x y))
            as (cv b (prel_option r2 pm x y) (prel_option r1 pm x y))
        }
        Some _ -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x y)) as pure False;
          unreachable ()
        }
      }
    }
    Some a -> {
      match y {
        None -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x y)) as pure False;
          unreachable ()
        }
        Some v -> {
          rewrite (cv b (prel_option r1 pm x y) (prel_option r2 pm x y)) as (cv b (r1 pm a v) (r2 pm a v));
          c pm a v ();
          rewrite (cv b (r2 pm a v) (r1 pm a v)) as (cv b (prel_option r2 pm x y) (prel_option r1 pm x y))
        }
      }
    }
  }
}

ghost
fn kc_view (b: bool) (#t #ty #u: Type0) (r1 r2: prel t u) (kp: t -> prop) (c: kc_t b r1 r2 kp) (view: ty -> t)
: kc_t b (vview r1 view) (vview r2 view) (kview kp view)
= (pm: perm) (x: ty) (y: u) (sq': squash (b == false ==> kview kp view x))
{
  rewrite (cv b (vview r1 view pm x y) (vview r2 view pm x y)) as (cv b (r1 pm (view x) y) (r2 pm (view x) y));
  c pm (view x) y ();
  rewrite (cv b (r2 pm (view x) y) (r1 pm (view x) y)) as (cv b (vview r2 view pm x y) (vview r1 view pm x y))
}

ghost
fn kc_via (b: bool) (#t #a: Type0) (ra1 ra2: prel t a) (kp: t -> prop) (c: kc_t b ra1 ra2 kp)
  (#u: Type0) (r1 r2: prel t u) (m: u -> GTot a)
  (eq1: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r1 pm x y == ra1 pm x (m y)))
  (eq2: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r2 pm x y == ra2 pm x (m y)))
: kc_t b r1 r2 kp
= (pm: perm) (x: t) (y: u) (sq': squash (b == false ==> kp x))
{
  eq1 pm x y;
  eq2 pm x y;
  rewrite (cv b (r1 pm x y) (r2 pm x y)) as (cv b (ra1 pm x (m y)) (ra2 pm x (m y)));
  c pm x (m y) ();
  rewrite (cv b (ra2 pm x (m y)) (ra1 pm x (m y))) as (cv b (r2 pm x y) (r1 pm x y))
}

ghost
fn kc_cond (b: bool) (#t #a: Type0) (ra1 ra2: prel t a) (kp: t -> prop) (c: kc_t b ra1 ra2 kp)
  (#u: Type0) (r1 r2: prel t u) (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot a)
  (eq1: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r1 pm x y == (if p y then ra1 pm x (h y ()) else pure False)))
  (eq2: (pm: perm) -> (x: t) -> (y: u) -> Lemma (r2 pm x y == (if p y then ra2 pm x (h y ()) else pure False)))
: kc_t b r1 r2 kp
= (pm: perm) (x: t) (y: u) (sq': squash (b == false ==> kp x))
{
  eq1 pm x y;
  eq2 pm x y;
  let bb : bool = p y;
  if bb {
    rewrite (cv b (r1 pm x y) (r2 pm x y)) as (cv b (ra1 pm x (h y ())) (ra2 pm x (h y ())));
    c pm x (h y ()) ();
    rewrite (cv b (ra2 pm x (h y ())) (ra1 pm x (h y ()))) as (cv b (r2 pm x y) (r1 pm x y))
  } else {
    rewrite (cv b (r1 pm x y) (r2 pm x y)) as (pure False);
    unreachable ()
  }
}

ghost
fn kc_either (b: bool) (#th #tt #ah #at: Type0)
  (rh1 rh2: prel th ah) (kph: th -> prop) (ch: kc_t b rh1 rh2 kph)
  (rt1 rt2: prel tt at) (kpt: tt -> prop) (ct: kc_t b rt1 rt2 kpt)
  (#u: Type0) (r1 r2: prel (either th tt) u)
  (p: u -> GTot bool) (h: (y: u) -> squash (p y == true) -> GTot ah) (tl: (y: u) -> squash (p y == false) -> GTot at)
  (eql1: (pm: perm) -> (x: th) -> (y: u) -> Lemma (r1 pm (Inl x) y == (if p y then rh1 pm x (h y ()) else pure False)))
  (eqr1: (pm: perm) -> (x: tt) -> (y: u) -> Lemma (r1 pm (Inr x) y == (if p y then pure False else rt1 pm x (tl y ()))))
  (eql2: (pm: perm) -> (x: th) -> (y: u) -> Lemma (r2 pm (Inl x) y == (if p y then rh2 pm x (h y ()) else pure False)))
  (eqr2: (pm: perm) -> (x: tt) -> (y: u) -> Lemma (r2 pm (Inr x) y == (if p y then pure False else rt2 pm x (tl y ()))))
: kc_t b r1 r2 (keither kph kpt)
= (pm: perm) (x: either th tt) (y: u) (sq': squash (b == false ==> keither kph kpt x))
{
  let bb : bool = p y;
  match x {
    Inl xh -> {
      eql1 pm xh y;
      eql2 pm xh y;
      if bb {
        rewrite (cv b (r1 pm x y) (r2 pm x y)) as (cv b (rh1 pm xh (h y ())) (rh2 pm xh (h y ())));
        ch pm xh (h y ()) ();
        rewrite (cv b (rh2 pm xh (h y ())) (rh1 pm xh (h y ()))) as (cv b (r2 pm x y) (r1 pm x y))
      } else {
        rewrite (cv b (r1 pm x y) (r2 pm x y)) as (pure False);
        unreachable ()
      }
    }
    Inr xt -> {
      eqr1 pm xt y;
      eqr2 pm xt y;
      if bb {
        rewrite (cv b (r1 pm x y) (r2 pm x y)) as (pure False);
        unreachable ()
      } else {
        rewrite (cv b (r1 pm x y) (r2 pm x y)) as (cv b (rt1 pm xt (tl y ())) (rt2 pm xt (tl y ())));
        ct pm xt (tl y ()) ();
        rewrite (cv b (rt2 pm xt (tl y ())) (rt1 pm xt (tl y ()))) as (cv b (r2 pm x y) (r1 pm x y))
      }
    }
  }
}

(* KEEP-BYTES nodes: `arel true` additionally requires the bytes *)

let keep_eq (kb: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k)) (pm: perm) (x: kept t) (y: asn1_t k)
: Lemma (arel kb (D_KEEP d wf) pm x y ==
    (if kb
     then arel kb d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y ** pure (Some? x.kraw)
     else arel kb d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y))
= assert (arel kb (D_KEEP d wf) pm x y ==
    (if kb
     then arel kb d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y ** pure (Some? x.kraw)
     else arel kb d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y))
    by (T.norm [delta_only [`%arel]; zeta; iota]; T.trefl ())

ghost
fn kc_keep_weaken (b: bool) (sq: squash (b == true)) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k))
  (c: kc_t b (arel true d) (arel false d) (kept_a d))
: kc_t b (arel true (D_KEEP d wf)) (arel false (D_KEEP d wf)) (kkeep (kept_a d))
= (pm: perm) (x: kept t) (y: asn1_t k) (sq': squash (b == false ==> kkeep (kept_a d) x))
{
  keep_eq true d wf pm x y;
  keep_eq false d wf pm x y;
  rewrite (cv b (arel true (D_KEEP d wf) pm x y) (arel false (D_KEEP d wf) pm x y))
    as (arel true d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y ** pure (Some? x.kraw));
  rewrite (arel true d (pm /. 2.0R) x.kval y) as (cv b (arel true d (pm /. 2.0R) x.kval y) (arel false d (pm /. 2.0R) x.kval y));
  c (pm /. 2.0R) x.kval y ();
  rewrite (cv b (arel false d (pm /. 2.0R) x.kval y) (arel true d (pm /. 2.0R) x.kval y)) as (arel false d (pm /. 2.0R) x.kval y);
  rewrite (arel false d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y)
    as (cv b (arel false (D_KEEP d wf) pm x y) (arel true (D_KEEP d wf) pm x y))
}

#push-options "--fuel 0 --ifuel 0"
ghost
fn kc_keep_restore (b: bool) (sq: squash (b == false)) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k))
  (c: kc_t b (arel true d) (arel false d) (kept_a d))
: kc_t b (arel true (D_KEEP d wf)) (arel false (D_KEEP d wf)) (kkeep (kept_a d))
= (pm: perm) (x: kept t) (y: asn1_t k) (sq': squash (b == false ==> kkeep (kept_a d) x))
{
  keep_eq true d wf pm x y;
  keep_eq false d wf pm x y;
  rewrite (cv b (arel true (D_KEEP d wf) pm x y) (arel false (D_KEEP d wf) pm x y))
    as (arel false d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y);
  rewrite (arel false d (pm /. 2.0R) x.kval y) as (cv b (arel true d (pm /. 2.0R) x.kval y) (arel false d (pm /. 2.0R) x.kval y));
  c (pm /. 2.0R) x.kval y ();
  rewrite (cv b (arel false d (pm /. 2.0R) x.kval y) (arel true d (pm /. 2.0R) x.kval y)) as (arel true d (pm /. 2.0R) x.kval y);
  rewrite (arel true d (pm /. 2.0R) x.kval y ** keep_rel k (pm /. 2.0R) x.kraw y ** pure (Some? x.kraw))
    as (cv b (arel false (D_KEEP d wf) pm x y) (arel true (D_KEEP d wf) pm x y))
}
#pop-options

let kc_keep (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (wf: squash (Conf.wf k))
  (c: kc_t b (arel true d) (arel false d) (kept_a d))
: kc_t b (arel true (D_KEEP d wf)) (arel false (D_KEEP d wf)) (kkeep (kept_a d))
= if b then kc_keep_weaken b () d wf c else kc_keep_restore b () d wf c

(* SEQUENCE OF / SET OF: a serialized list does not depend on the relation
   of its elements *)

let ml_ser_aux (#t #u: Type0) (r1 r2: prel t u) (#k: SB.parser_kind) (p: SB.parser k u) (pm sp: perm) (count: SZ.t) (pl: S.slice U8.t) (y: list u)
: Lemma (It.mixed_list_match r1 ml_ops p pm (ItT.Base (ItT.Serialized sp count pl) <: ml t) y ==
    It.mixed_list_match r2 ml_ops p pm (ItT.Base (ItT.Serialized sp count pl) <: ml t) y)
= assert (It.mixed_list_match r1 ml_ops p pm (ItT.Base (ItT.Serialized sp count pl) <: ml t) y ==
    It.mixed_list_match r2 ml_ops p pm (ItT.Base (ItT.Serialized sp count pl) <: ml t) y)
    by (T.norm [delta_only [`%It.mixed_list_match; `%It.mixed_list_match_n; `%It.base_mixed_list_match_n]; zeta; iota]; T.trefl ())

let tml_ser_eq (kb1 kb2: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: ml t) (y: list (asn1_t k))
: Lemma (requires is_serialized x) (ensures tml_rel kb1 d pm x y == tml_rel kb2 d pm x y)
= match x with
  | ItT.Base (ItT.Serialized sp count pl) -> ml_ser_aux (arel kb1 d) (arel kb2 d) #asn1_strong_parser_kind (asn1_as_parser k) pm sp count pl y
  | _ -> ()

ghost
fn kc_list_weaken (b: bool) (sq: squash (b == true)) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
  (#u: Type0) (r1 r2: prel (ml t) u) (g: u -> GTot (list (asn1_t k)))
  (eq1: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r1 pm x y == tml_rel true d pm x (g y) ** pure (is_serialized x)))
  (eq2: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r2 pm x y == tml_rel false d pm x (g y)))
: kc_t b r1 r2 (is_serialized #t)
= (pm: perm) (x: ml t) (y: u) (sq': squash (b == false ==> is_serialized x))
{
  eq1 pm x y;
  eq2 pm x y;
  rewrite (cv b (r1 pm x y) (r2 pm x y)) as (tml_rel true d pm x (g y) ** pure (is_serialized x));
  tml_ser_eq true false d pm x (g y);
  rewrite (tml_rel true d pm x (g y)) as (cv b (r2 pm x y) (r1 pm x y))
}

ghost
fn kc_list_restore (b: bool) (sq: squash (b == false)) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
  (#u: Type0) (r1 r2: prel (ml t) u) (g: u -> GTot (list (asn1_t k)))
  (eq1: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r1 pm x y == tml_rel true d pm x (g y) ** pure (is_serialized x)))
  (eq2: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r2 pm x y == tml_rel false d pm x (g y)))
: kc_t b r1 r2 (is_serialized #t)
= (pm: perm) (x: ml t) (y: u) (sq': squash (b == false ==> is_serialized x))
{
  eq1 pm x y;
  eq2 pm x y;
  rewrite (cv b (r1 pm x y) (r2 pm x y)) as (tml_rel false d pm x (g y));
  tml_ser_eq false true d pm x (g y);
  rewrite (tml_rel false d pm x (g y)) as (tml_rel true d pm x (g y));
  rewrite (tml_rel true d pm x (g y) ** pure (is_serialized x)) as (cv b (r2 pm x y) (r1 pm x y))
}

let kc_list (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
  (#u: Type0) (r1 r2: prel (ml t) u) (g: u -> GTot (list (asn1_t k)))
  (eq1: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r1 pm x y == tml_rel true d pm x (g y) ** pure (is_serialized x)))
  (eq2: (pm: perm) -> (x: ml t) -> (y: u) -> Lemma (r2 pm x y == tml_rel false d pm x (g y)))
: kc_t b r1 r2 (is_serialized #t)
= if b then kc_list_weaken b () d r1 r2 g eq1 eq2 else kc_list_restore b () d r1 r2 g eq1 eq2

let kc_seq_of (b: bool) (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: kc_t b (crel true (CD_SEQUENCE_OF ne d)) (crel false (CD_SEQUENCE_OF ne d)) (is_serialized #t)
= kc_list b d (crel true (CD_SEQUENCE_OF ne d)) (crel false (CD_SEQUENCE_OF ne d)) (RS.seq_of_up ne k)
    (fun pm x y -> tcontent_seq_of_eq true ne d pm x y)
    (fun pm x y -> tcontent_seq_of_eq false ne d pm x y)

let kc_set_of (b: bool) (ne: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: kc_t b (crel true (CD_SET_OF ne d)) (crel false (CD_SET_OF ne d)) (is_serialized #t)
= kc_list b d (crel true (CD_SET_OF ne d)) (crel false (CD_SET_OF ne d)) (RS.set_of_up ne k)
    (fun pm x y -> tcontent_set_of_eq true ne d pm x y)
    (fun pm x y -> tcontent_set_of_eq false ne d pm x y)

(* Conversion types, one per kind of descriptor *)

let ka_t (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) : Type =
  kc_t b (arel true d) (arel false d) (kept_a d)

let kcc_t (b: bool) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t) : Type =
  kc_t b (crel true cd) (crel false cd) (kept_c cd)

let kd_t (b: bool) (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t) : Type =
  kc_t b (drel true dd) (drel false dd) (kept_d dd)

let ki_t (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t) : Type =
  kc_t b (irel true di) (irel false di) (kept_i di)

let klc_t (b: bool) (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t) : Type =
  kc_t b (lcrel true ld) (lcrel false ld) (kept_lc ld)

let ksx_t (b: bool) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t) : Type =
  kc_t b #t #(AL.ady key_k ls) (sxrel true dsx) (sxrel false dsx) (kept_sx dsx)

let kfx_t (b: bool) (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (kfb: (asn1_terminal_impl_t key_k & tfb) -> prop)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t) : Type =
  kc_t b #t #(AL.ady_fb key_k ls gfb)
    (fxrel true dfx (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel false dfx (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (kept_fx dfx kfb)

let kia_t (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs: Type0) (sfx1 sfx2: prel sfxi sfxs) (ksfx: sfxi -> prop) : Type =
  kc_t b (iarel true dpre #sfxs sfx1) (iarel false dpre #sfxs sfx2) (kept_ia dpre ksfx)

(* CHOICE alternatives *)

let kc_lc_nil (b: bool) : klc_t b LC_NIL =
  kc_false b (lcrel true LC_NIL) (lcrel false LC_NIL) (kept_lc LC_NIL) (tlc_nil_eq true) (tlc_nil_eq false)

let kc_lc_single (b: bool) (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t) (cc: kcc_t b cd)
: klc_t b (LC_SINGLE id' cd)
= kc_ext b (lcrel true (LC_SINGLE id' cd)) (lcrel true (LC_SINGLE id' cd)) (lcrel false (LC_SINGLE id' cd)) (lcrel false (LC_SINGLE id' cd))
    (kept_c cd) (kept_lc (LC_SINGLE id' cd)) () (fun _ -> ())
    (kc_cond b (crel true cd) (crel false cd) (kept_c cd) cc
      (lcrel true (LC_SINGLE id' cd)) (lcrel false (LC_SINGLE id' cd))
      (fun v -> dfst v = id') (fun v _ -> RS.lc_head_val id' c [] v ())
      (tlc_single_eq true id' cd) (tlc_single_eq false id' cd))

let kc_lc_cons (b: bool) (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: (asn1_id_t & asn1_content_k)) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (cc: kcc_t b cd) (ct: klc_t b dtl)
: klc_t b (LC_CONS id' cd dtl)
= kc_ext b (lcrel true (LC_CONS id' cd dtl)) (lcrel true (LC_CONS id' cd dtl)) (lcrel false (LC_CONS id' cd dtl)) (lcrel false (LC_CONS id' cd dtl))
    (keither (kept_c cd) (kept_lc dtl)) (kept_lc (LC_CONS id' cd dtl)) () (fun _ -> ())
    (kc_either b (crel true cd) (crel false cd) (kept_c cd) cc
      (lcrel true dtl) (lcrel false dtl) (kept_lc dtl) ct
      (lcrel true (LC_CONS id' cd dtl)) (lcrel false (LC_CONS id' cd dtl))
      (fun v -> dfst v = id') (fun v _ -> RS.lc_head_val id' c (hd2 :: tl2) v ()) (fun v _ -> RS.lc_tail_val (id', c) (hd2 :: tl2) v ())
      (tlc_cons_inl_eq true id' cd dtl) (tlc_cons_inr_eq true id' cd dtl)
      (tlc_cons_inl_eq false id' cd dtl) (tlc_cons_inr_eq false id' cd dtl))

(* ANY DEFINED BY *)

let kc_sx_nil (b: bool) (key_k: asn1_terminal_k) : ksx_t b (SX_NIL key_k) =
  kc_false b (sxrel true (SX_NIL key_k)) (sxrel false (SX_NIL key_k)) (kept_sx (SX_NIL key_k)) (tadb_nil_eq true #key_k) (tadb_nil_eq false #key_k)

let kc_sx_single (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t)
  (ci: ki_t b di)
: ksx_t b (SX_SINGLE key_k kx y di)
= kc_ext b (sxrel true (SX_SINGLE key_k kx y di)) (sxrel true (SX_SINGLE key_k kx y di)) (sxrel false (SX_SINGLE key_k kx y di)) (sxrel false (SX_SINGLE key_k kx y di))
    (kept_i di) (kept_sx (SX_SINGLE key_k kx y di)) () (fun _ -> ())
    (kc_cond b (irel true di) (irel false di) (kept_i di) ci
      (sxrel true (SX_SINGLE key_k kx y di)) (sxrel false (SX_SINGLE key_k kx y di))
      (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_head_val kx y [] v ())
      (tadb_single_eq true kx y di) (tadb_single_eq false kx y di))

let kc_sx_cons (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t2: Type0) (dtl: sxdesc key_k (hd2 :: tl2) t2)
  (ci: ki_t b di) (ct: ksx_t b dtl)
: ksx_t b (SX_CONS key_k kx y di dtl)
= kc_ext b (sxrel true (SX_CONS key_k kx y di dtl)) (sxrel true (SX_CONS key_k kx y di dtl)) (sxrel false (SX_CONS key_k kx y di dtl)) (sxrel false (SX_CONS key_k kx y di dtl))
    (keither (kept_i di) (kept_sx dtl)) (kept_sx (SX_CONS key_k kx y di dtl)) () (fun _ -> ())
    (kc_either b (irel true di) (irel false di) (kept_i di) ci
      (sxrel true dtl) (sxrel false dtl) (kept_sx dtl) ct
      (sxrel true (SX_CONS key_k kx y di dtl)) (sxrel false (SX_CONS key_k kx y di dtl))
      (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_head_val kx y (hd2 :: tl2) v ()) (fun v _ -> AL.ady_tail_val kx y (hd2 :: tl2) v ())
      (tadb_cons_inl_eq true kx y di dtl) (tadb_cons_inr_eq true kx y di dtl)
      (tadb_cons_inl_eq false kx y di dtl) (tadb_cons_inr_eq false kx y di dtl))

(* ANY DEFINED BY, with a fallback *)

let kc_fx_nil (b: bool) (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (kfb: (asn1_terminal_impl_t key_k & tfb) -> prop)
  (kfb_eq: (z: (asn1_terminal_impl_t key_k & tfb)) -> Lemma (kfb z <==> kept_i dfb (snd z)))
  (cf: ki_t b dfb)
: kfx_t b dfb kfb (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb))
= kc_ext b
    (fxrel true (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel true (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel false (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (fxrel false (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (kpair (ktrue (asn1_terminal_impl_t key_k)) (kept_i dfb)) (kept_fx (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) kfb) ()
    (fun z -> kfb_eq z)
    (kc_via b (prel_pair (asn1_terminal_rel key_k) (irel true dfb)) (prel_pair (asn1_terminal_rel key_k) (irel false dfb))
      (kpair (ktrue (asn1_terminal_impl_t key_k)) (kept_i dfb))
      (kc_pair b (asn1_terminal_rel key_k) (asn1_terminal_rel key_k) (ktrue (asn1_terminal_impl_t key_k)) (kc_refl b (asn1_terminal_rel key_k))
        (irel true dfb) (irel false dfb) (kept_i dfb) cf)
      (fxrel true (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
      (fxrel false (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
      (fun v -> (dfst v, AL.ady_fb_nil_val gfb v))
      (tafb_nil_eq true key_k dfb) (tafb_nil_eq false key_k dfb))

let kc_fx_single (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (kfb: (asn1_terminal_impl_t key_k & tfb) -> prop)
  (kfb_eq: (z: (asn1_terminal_impl_t key_k & tfb)) -> Lemma (kfb z <==> kept_i dfb (snd z)))
  (ci: ki_t b di) (cf: ki_t b dfb)
: kfx_t b dfb kfb (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb))
= kc_ext b
    (fxrel true (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel true (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel false (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (fxrel false (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (keither (kept_i di) (kept_fx (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) kfb))
    (kept_fx (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) kfb) () (fun _ -> ())
    (kc_either b (irel true di) (irel false di) (kept_i di) ci
      (fxrel true (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
      (fxrel false (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
      (kept_fx (FX_NIL key_k #(asn1_terminal_impl_t key_k & tfb)) kfb)
      (kc_fx_nil b key_k dfb kfb kfb_eq cf)
      (fxrel true (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
      (fxrel false (FX_SINGLE key_k kx y di #(asn1_terminal_impl_t key_k & tfb)) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
      (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_fb_head_val kx y [] gfb v ()) (fun v _ -> AL.ady_fb_tail_val kx y [] gfb v ())
      (tafb_single_inl_eq true kx y di gfb (tfbr true key_k dfb)) (tafb_single_inr_eq true kx y di gfb (tfbr true key_k dfb))
      (tafb_single_inl_eq false kx y di gfb (tfbr false key_k dfb)) (tafb_single_inr_eq false kx y di gfb (tfbr false key_k dfb)))

let kc_fx_cons (b: bool) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (#t1: Type0) (di: idesc (dsnd y) t1)
  (#hd2: (asn1_key_lit key_k & asn1_gen_items_lk)) (#tl2: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (kfb: (asn1_terminal_impl_t key_k & tfb) -> prop)
  (#t2: Type0) (dtl: fxdesc key_k (hd2 :: tl2) (asn1_terminal_impl_t key_k & tfb) t2)
  (ci: ki_t b di) (ct: kfx_t b dfb kfb dtl)
: kfx_t b dfb kfb (FX_CONS key_k kx y di dtl)
= kc_ext b
    (fxrel true (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel true (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
    (fxrel false (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (fxrel false (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
    (keither (kept_i di) (kept_fx dtl kfb)) (kept_fx (FX_CONS key_k kx y di dtl) kfb) () (fun _ -> ())
    (kc_either b (irel true di) (irel false di) (kept_i di) ci
      (fxrel true dtl (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
      (fxrel false dtl (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
      (kept_fx dtl kfb) ct
      (fxrel true (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr true key_k dfb))
      (fxrel false (FX_CONS key_k kx y di dtl) (asn1_sequence_t_core (dsnd gfb)) (tfbr false key_k dfb))
      (fun v -> dfst v = key_of_lit key_k kx) (fun v _ -> AL.ady_fb_head_val kx y (hd2 :: tl2) gfb v ()) (fun v _ -> AL.ady_fb_tail_val kx y (hd2 :: tl2) gfb v ())
      (tafb_cons_inl_eq true kx y di dtl gfb (tfbr true key_k dfb)) (tafb_cons_inr_eq true kx y di dtl gfb (tfbr true key_k dfb))
      (tafb_cons_inl_eq false kx y di dtl gfb (tfbr false key_k dfb)) (tafb_cons_inr_eq false kx y di dtl gfb (tfbr false key_k dfb)))

(* The whole conversion, by mutual recursion on the descriptor *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 64"
let rec kc_a (b: bool) (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t)
: Tot (ka_t b d) (decreases d)
= match d with
  | D_ILC id cd ->
    trel_ilc_equiv true id cd;
    trel_ilc_equiv false id cd;
    kc_ext b (crel true cd) (arel true d) (crel false cd) (arel false d) (kept_c cd) (kept_a d) () (fun _ -> ()) (kc_c b cd)
  | D_CHOICE lc pf ld ->
    trel_choice_equiv true lc pf ld;
    trel_choice_equiv false lc pf ld;
    kc_ext b (lcrel true ld) (arel true d) (lcrel false ld) (arel false d) (kept_lc ld) (kept_a d) () (fun _ -> ()) (kc_lc b ld)
  | D_ANY ->
    trel_any_equiv true ();
    trel_any_equiv false ();
    kc_ext b (prel_slice_ser asn1_value_enc) (arel true d) (prel_slice_ser asn1_value_enc) (arel false d) (ktrue (S.slice U8.t)) (kept_a d) () (fun _ -> ())
      (kc_refl b (prel_slice_ser asn1_value_enc))
  | D_VIEW d' ty view mk law ->
    trel_view_equiv true d' ty view mk law;
    trel_view_equiv false d' ty view mk law;
    kc_ext b (vview (arel true d') view) (arel true d) (vview (arel false d') view) (arel false d) (kview (kept_a d') view) (kept_a d) () (fun _ -> ())
      (kc_view b (arel true d') (arel false d') (kept_a d') (kc_a b d') view)
  | D_KEEP d' wf ->
    kc_ext b (arel true d) (arel true d) (arel false d) (arel false d) (kkeep (kept_a d')) (kept_a d) () (fun _ -> ())
      (kc_keep b d' wf (kc_a b d'))

and kc_c (b: bool) (#k: asn1_content_k) (#t: Type0) (cd: cdesc k t)
: Tot (kcc_t b cd) (decreases cd)
= match cd with
  | CD_TERMINAL k' ->
    tcontent_terminal_equiv true k';
    tcontent_terminal_equiv false k';
    kc_ext b (asn1_terminal_rel k') (crel true cd) (asn1_terminal_rel k') (crel false cd) (ktrue _) (kept_c cd) () (fun _ -> ()) (kc_refl b (asn1_terminal_rel k'))
  | CD_RESTRICTED k' r ->
    tcontent_restricted_equiv true k' r;
    tcontent_restricted_equiv false k' r;
    kc_ext b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (crel true cd) (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (crel false cd)
      (ktrue _) (kept_c cd) () (fun _ -> ()) (kc_refl b (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)))
  | CD_PREFIXED d' ->
    tcontent_prefixed_equiv true d';
    tcontent_prefixed_equiv false d';
    kc_ext b (arel true d') (crel true cd) (arel false d') (crel false cd) (kept_a d') (kept_c cd) () (fun _ -> ()) (kc_a b d')
  | CD_SEQUENCE gitems di ->
    tcontent_sequence_equiv true gitems di;
    tcontent_sequence_equiv false gitems di;
    kc_ext b (irel true di) (crel true cd) (irel false di) (crel false cd) (kept_i di) (kept_c cd) () (fun _ -> ()) (kc_i b di)
  | CD_SET ids items pf di ->
    tcontent_set_equiv true ids items pf di;
    tcontent_set_equiv false ids items pf di;
    kc_ext b (irel true di) (crel true cd) (irel false di) (crel false cd) (kept_i di) (kept_c cd) () (fun _ -> ()) (kc_i b di)
  | CD_SEQUENCE_OF ne #_ #_ #t' d' ->
    kc_ext b (crel true cd) (crel true cd) (crel false cd) (crel false cd) (is_serialized #t') (kept_c cd) () (fun _ -> ()) (kc_seq_of b ne d')
  | CD_SET_OF ne #_ #_ #t' d' ->
    kc_ext b (crel true cd) (crel true cd) (crel false cd) (crel false cd) (is_serialized #t') (kept_c cd) () (fun _ -> ()) (kc_set_of b ne d')
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    tcontent_adb_none_equiv true ipd prefix kid key_k ls pf pf' dsx dpre;
    tcontent_adb_none_equiv false ipd prefix kid key_k ls pf pf' dsx dpre;
    kc_ext b (iarel true dpre #(AL.ady key_k ls) (sxrel true dsx)) (crel true cd) (iarel false dpre #(AL.ady key_k ls) (sxrel false dsx)) (crel false cd)
      (kept_ia dpre (fun s -> kept_sx dsx s)) (kept_c cd) () (fun x -> kept_c_adb_none_eq ipd prefix kid key_k ls pf pf' dsx dpre x)
      (kc_ia b dpre (sxrel true dsx) (sxrel false dsx) (fun s -> kept_sx dsx s) (kc_sx b dsx))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' #tfb dfb dfx dpre ->
    tcontent_adb_some_equiv true ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    tcontent_adb_some_equiv false ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    kc_ext b
      (iarel true dpre #(AL.ady_fb key_k ls fb) (fxrel true dfx (asn1_sequence_t_core (dsnd fb)) (tfbr true key_k #fb dfb))) (crel true cd)
      (iarel false dpre #(AL.ady_fb key_k ls fb) (fxrel false dfx (asn1_sequence_t_core (dsnd fb)) (tfbr false key_k #fb dfb))) (crel false cd)
      (kept_ia dpre (fun s -> kept_fx dfx (fun (z: asn1_terminal_impl_t key_k & tfb) -> kept_i dfb (snd z)) s)) (kept_c cd) () (fun x -> kept_c_adb_some_eq ipd prefix kid key_k ls fb pf pf' dfb dfx dpre x)
      (kc_ia b dpre
        (fxrel true dfx (asn1_sequence_t_core (dsnd fb)) (tfbr true key_k #fb dfb))
        (fxrel false dfx (asn1_sequence_t_core (dsnd fb)) (tfbr false key_k #fb dfb))
        (fun s -> kept_fx dfx (fun (z: asn1_terminal_impl_t key_k & tfb) -> kept_i dfb (snd z)) s)
        (kc_fx b dfb (fun (z: asn1_terminal_impl_t key_k & tfb) -> kept_i dfb (snd z)) (fun _ -> ()) (kc_i b dfb) dfx))
  | CD_VIEW d' ty view mk law ->
    tcontent_view_equiv true d' ty view mk law;
    tcontent_view_equiv false d' ty view mk law;
    kc_ext b (vview (crel true d') view) (crel true cd) (vview (crel false d') view) (crel false cd) (kview (kept_c d') view) (kept_c cd) () (fun _ -> ())
      (kc_view b (crel true d') (crel false d') (kept_c d') (kc_c b d') view)

and kc_sx (b: bool) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dsx: sxdesc key_k ls t)
: Tot (ksx_t b dsx) (decreases dsx)
= match dsx with
  | SX_NIL _ -> kc_sx_nil b key_k
  | SX_SINGLE _ kx y di -> kc_sx_single b kx y di (kc_i b di)
  | SX_CONS _ kx y di dtl -> kc_sx_cons b kx y di dtl (kc_i b di) (kc_sx b dtl)

and kc_fx (b: bool) (#key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (kfb: (asn1_terminal_impl_t key_k & tfb) -> prop)
  (kfb_eq: (z: (asn1_terminal_impl_t key_k & tfb)) -> Lemma (kfb z <==> kept_i dfb (snd z)))
  (cf: ki_t b dfb)
  (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (dfx: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t)
: Tot (kfx_t b dfb kfb dfx) (decreases dfx)
= match dfx with
  | FX_NIL _ -> kc_fx_nil b key_k dfb kfb kfb_eq cf
  | FX_SINGLE _ kx y di -> kc_fx_single b kx y di dfb kfb kfb_eq (kc_i b di) cf
  | FX_CONS _ kx y di dtl -> kc_fx_cons b kx y di dfb kfb dtl (kc_i b di) (kc_fx b dfb kfb kfb_eq cf dtl)

and kc_ia (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#sfxi: Type0) (#t: Type0) (dpre: iadesc items sfxi t)
  (#sfxs: Type0) (sfx1 sfx2: prel sfxi sfxs) (ksfx: sfxi -> prop) (cs: kc_t b sfx1 sfx2 ksfx)
: Tot (kia_t b dpre sfx1 sfx2 ksfx) (decreases dpre)
= match dpre with
  | IA_NIL ->
    titems_any_nil_equiv true sfx1;
    titems_any_nil_equiv false sfx2;
    kc_ext b sfx1 (iarel true dpre sfx1) sfx2 (iarel false dpre sfx2) ksfx (kept_ia dpre ksfx) () (fun _ -> ()) cs
  | IA_SINGLE dd ->
    titems_any_single_equiv true dd sfx1;
    titems_any_single_equiv false dd sfx2;
    kc_ext b (prel_pair (drel true dd) sfx1) (iarel true dpre sfx1) (prel_pair (drel false dd) sfx2) (iarel false dpre sfx2)
      (kpair (kept_d dd) ksfx) (kept_ia dpre ksfx) () (fun _ -> ())
      (kc_pair b (drel true dd) (drel false dd) (kept_d dd) (kc_d b dd) sfx1 sfx2 ksfx cs)
  | IA_CONS dd dtl ->
    titems_any_cons_equiv true dd dtl sfx1;
    titems_any_cons_equiv false dd dtl sfx2;
    kc_ext b (prel_pair (drel true dd) (iarel true dtl sfx1)) (iarel true dpre sfx1) (prel_pair (drel false dd) (iarel false dtl sfx2)) (iarel false dpre sfx2)
      (kpair (kept_d dd) (kept_ia dtl ksfx)) (kept_ia dpre ksfx) () (fun _ -> ())
      (kc_pair b (drel true dd) (drel false dd) (kept_d dd) (kc_d b dd) (iarel true dtl sfx1) (iarel false dtl sfx2) (kept_ia dtl ksfx) (kc_ia b dtl sfx1 sfx2 ksfx cs))

and kc_lc (b: bool) (#lc: list (asn1_id_t & asn1_content_k)) (#t: Type0) (ld: lcdesc lc t)
: Tot (klc_t b ld) (decreases ld)
= match ld with
  | LC_NIL -> kc_lc_nil b
  | LC_SINGLE id' cd -> kc_lc_single b id' cd (kc_c b cd)
  | LC_CONS id' cd dtl -> kc_lc_cons b id' cd dtl (kc_c b cd) (kc_lc b dtl)

and kc_d (b: bool) (#s: _) (#dc: _) (#dk: asn1_decorated_k s dc) (#t: Type0) (dd: ddesc dk t)
: Tot (kd_t b dd) (decreases dd)
= match dd with
  | DD_PLAIN d' ->
    tdec_plain_equiv true d';
    tdec_plain_equiv false d';
    kc_ext b (arel true d') (drel true dd) (arel false d') (drel false dd) (kept_a d') (kept_d dd) () (fun _ -> ()) (kc_a b d')
  | DD_OPTION d' ->
    tdec_option_equiv true d';
    tdec_option_equiv false d';
    kc_ext b (prel_option (arel true d')) (drel true dd) (prel_option (arel false d')) (drel false dd) (kopt (kept_a d')) (kept_d dd) () (fun _ -> ())
      (kc_option b (arel true d') (arel false d') (kept_a d') (kc_a b d'))
  | DD_DEFAULT id0 #k' defv ->
    tdec_default_equiv true id0 defv;
    tdec_default_equiv false id0 defv;
    kc_ext b (RS.prel_default (asn1_terminal_rel k') (key_of_lit k' defv)) (drel true dd) (RS.prel_default (asn1_terminal_rel k') (key_of_lit k' defv)) (drel false dd)
      (ktrue _) (kept_d dd) () (fun _ -> ()) (kc_refl b (RS.prel_default (asn1_terminal_rel k') (key_of_lit k' defv)))
  | DD_DEFAULT_RESTRICTED id0 #k' r defv ->
    tdec_default_restricted_equiv true id0 r defv;
    tdec_default_restricted_equiv false id0 r defv;
    kc_ext b (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (key_of_lit k' defv)) (drel true dd)
      (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (key_of_lit k' defv)) (drel false dd)
      (ktrue _) (kept_d dd) () (fun _ -> ()) (kc_refl b (RS.prel_default (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k' r)) (key_of_lit k' defv)))
  | DD_VIEW d' ty view mk law ->
    tdec_view_equiv true d' ty view mk law;
    tdec_view_equiv false d' ty view mk law;
    kc_ext b (vview (drel true d') view) (drel true dd) (vview (drel false d') view) (drel false dd) (kview (kept_d d') view) (kept_d dd) () (fun _ -> ())
      (kc_view b (drel true d') (drel false d') (kept_d d') (kc_d b d') view)

and kc_i (b: bool) (#ids: _) (#items: asn1_gen_items_l ids) (#t: Type0) (di: idesc items t)
: Tot (ki_t b di) (decreases di)
= match di with
  | ID_NIL ->
    titems_nil_equiv true ();
    titems_nil_equiv false ();
    kc_ext b (prel_emp unit unit) (irel true di) (prel_emp unit unit) (irel false di) (ktrue unit) (kept_i di) () (fun _ -> ()) (kc_refl b (prel_emp unit unit))
  | ID_SINGLE dd ->
    titems_single_equiv true dd;
    titems_single_equiv false dd;
    kc_ext b (drel true dd) (irel true di) (drel false dd) (irel false di) (kept_d dd) (kept_i di) () (fun _ -> ()) (kc_d b dd)
  | ID_CONS dd dtl ->
    titems_cons_equiv true dd dtl;
    titems_cons_equiv false dd dtl;
    kc_ext b (prel_pair (drel true dd) (irel true dtl)) (irel true di) (prel_pair (drel false dd) (irel false dtl)) (irel false di)
      (kpair (kept_d dd) (kept_i dtl)) (kept_i di) () (fun _ -> ())
      (kc_pair b (drel true dd) (drel false dd) (kept_d dd) (kc_d b dd) (irel true dtl) (irel false dtl) (kept_i dtl) (kc_i b dtl))
#pop-options

(* The main results *)

ghost
fn weaken (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (y: asn1_t k)
requires arel true d pm x y
ensures arel false d pm x y ** pure (kept_a d x)
{
  rewrite (arel true d pm x y) as (cv true (arel true d pm x y) (arel false d pm x y));
  kc_a true d pm x y ();
  rewrite (cv true (arel false d pm x y) (arel true d pm x y)) as (arel false d pm x y)
}

ghost
fn restore (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (y: asn1_t k)
requires arel false d pm x y ** pure (kept_a d x)
ensures arel true d pm x y
{
  rewrite (arel false d pm x y) as (cv false (arel true d pm x y) (arel false d pm x y));
  kc_a false d pm x y ();
  rewrite (cv false (arel false d pm x y) (arel true d pm x y)) as (arel true d pm x y)
}

(* From a parsed value to a value ready to be written, with a trade back *)

ghost
fn to_writer (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) (x: t) (y: asn1_t k)
requires arel true d pm x y
ensures arel false d pm x y ** Trade.trade (arel false d pm x y) (arel true d pm x y)
{
  weaken d pm x y;
  Trade.intro_trade (arel false d pm x y) (arel true d pm x y) (pure (kept_a d x)) fn _ {
    restore d pm x y
  }
}
