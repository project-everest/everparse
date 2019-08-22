module LowParse.Low.DepAcc
include LowParse.Low.Base

module M = LowParse.Math
module B = LowStar.Monotonic.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

noeq
type clens (t1: Type) (t2: (t1 -> Type)) = {
  clens_cond: t1 -> GTot bool;
  clens_get: (x1: t1 { clens_cond x1 }) -> GTot (t2 x1);
(*  
  clens_put: (x1: t1) -> t2 -> Ghost t1 (requires (clens_cond x1)) (ensures (fun x1' -> clens_cond x1'));
  clens_get_put: (x1: t1) -> (x2: t2) -> Lemma (requires (clens_cond x1)) (ensures (clens_get (clens_put x1 x2) == x2));
  clens_put_put: (x1: t1) -> (x2: t2) -> (x2' : t2) -> Lemma (requires (clens_cond x1)) (ensures (clens_put (clens_put x1 x2) x2' == clens_put x1 x2'));
  clens_put_get: (x1: t1) -> Lemma (requires (clens_cond x1)) (ensures (clens_put x1 (clens_get x1) == x1));
*)
}

let clens_id (t: Type) : Tot (clens t (fun _ -> t)) = {
  clens_cond = (fun _ -> true);
  clens_get = (fun x -> x);
}

let clens_eq (#t: Type) (#t': (t -> Type)) (cl1: clens t t') (cl2: clens t t') : GTot Type0 =
  (forall (x: t) . {:pattern (cl1.clens_cond x) \/ (cl2.clens_cond x)} cl1.clens_cond x <==> cl2.clens_cond x) /\
  (forall (x: t) . {:pattern (cl1.clens_get x) \/ (cl2.clens_get x)} (cl1.clens_cond x \/ cl2.clens_cond x) ==> (cl1.clens_get x == cl2.clens_get x))

let clens_eq_intro
  (#t: Type) (#t': (t -> Type)) (cl1: clens t t') (cl2: clens t t')
  (cond: (
    (x: t) ->
    Lemma
    (cl1.clens_cond x <==> cl2.clens_cond x)
  ))
  (get: (
    (x: t) ->
    Lemma
    (requires (cl1.clens_cond x /\ cl2.clens_cond x))
    (ensures (cl1.clens_cond x /\ cl2.clens_cond x /\ cl1.clens_get x == cl2.clens_get x))
  ))
: Lemma
  (clens_eq cl1 cl2)
= Classical.forall_intro cond;
  Classical.forall_intro (Classical.move_requires get)

let clens_eq_intro'
  (#t: Type) (#t': (t -> Type)) (cl1: clens t t') (cl2: clens t t')
  (cond: (
    (x: t) ->
    Tot (squash (cl1.clens_cond x <==> cl2.clens_cond x))
  ))
  (get: (
    (x: t) ->
    (sq: squash (cl1.clens_cond x /\ cl2.clens_cond x)) ->
    Tot (squash (cl1.clens_cond x /\ cl2.clens_cond x /\ cl1.clens_get x == cl2.clens_get x))
  ))
: Tot (squash (clens_eq cl1 cl2))
= clens_eq_intro cl1 cl2 (fun x -> cond x) (fun x -> get x ())
 

(*
let clens_get_put'
  (#t1: Type) (#clens_cond: t1 -> GTot Type0) (#t2: Type) (l: clens clens_cond t2)
  (x1: t1) (x2: t2)
: Lemma
  (requires (clens_cond x1))
  (ensures (l.clens_get (l.clens_put x1 x2) == x2))
  [SMTPat (l.clens_get (l.clens_put x1 x2))]
= l.clens_get_put x1 x2

let clens_put_put'
  (#t1: Type) (#clens_cond: t1 -> GTot Type0) (#t2: Type) (l: clens clens_cond t2)
  (x1: t1) (x2: t2) (x2' : t2)
: Lemma
  (requires (clens_cond x1))
  (ensures (l.clens_put (l.clens_put x1 x2) x2' == l.clens_put x1 x2'))
  [SMTPat (l.clens_put (l.clens_put x1 x2) x2')]
= l.clens_put_put x1 x2 x2'

let clens_put_get'
  (#t1: Type) (#clens_cond: t1 -> GTot Type0) (#t2: Type) (l: clens clens_cond t2)
  (x1: t1)
: Lemma
  (requires (clens_cond x1))
  (ensures (l.clens_put x1 (l.clens_get x1) == x1))
  [SMTPat (l.clens_put x1 (l.clens_get x1))]
= l.clens_put_get x1

abstract
let clens_disjoint_l
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
: GTot Type0
= (forall (x0: t0) (x2: t2) . (clens_cond2 x0 /\ clens_cond3 x0) ==> 
  (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0))

abstract
let clens_disjoint_l_elim
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
  (x0: t0) (x2: t2)
: Lemma
  (requires (clens_disjoint_l l2 l3 /\ clens_cond2 x0 /\ clens_cond3 x0))
  (ensures (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0))
  [SMTPat (l3.clens_get (l2.clens_put x0 x2))]
= ()

abstract
let clens_disjoint_l_intro
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
  (lem: (
    (x0: t0) ->
    (x2: t2) ->
    Lemma
    (requires (clens_cond2 x0 /\ clens_cond3 x0))
    (ensures (clens_cond2 x0 /\ clens_cond3 x0 /\ (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0)))
  ))
: Lemma
  (clens_disjoint_l l2 l3)
= let lem'
    (x0: t0)
    (x2: t2)
  : Lemma
    ((clens_cond2 x0 /\ clens_cond3 x0) ==>
    (ensures (clens_cond2 x0 /\ clens_cond3 x0 /\ (let x0' = l2.clens_put x0 x2 in clens_cond3 x0' /\ l3.clens_get x0' == l3.clens_get x0))))
  = Classical.move_requires (lem x0) x2
  in
  Classical.forall_intro_2 lem'

let clens_disjoint
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
: GTot Type0
= clens_disjoint_l l2 l3 /\ clens_disjoint_l l3 l2

let clens_disjoint_sym
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
: Lemma
  (clens_disjoint l2 l3 <==> clens_disjoint l3 l2)
  [SMTPat (clens_disjoint l2 l3)]
= ()
*)

let clens_compose_cond
  (#t1: Type)
  (#t2: (t1 -> Type))
  (l12: clens t1 t2)
  (#t3: ((x: t1) -> t2 x -> Type))
  (l23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (x1: t1)
: GTot bool
= l12.clens_cond x1 &&
  (l23 x1).clens_cond (l12.clens_get x1)

inline_for_extraction
noextract
let clens_compose_type
  (#t1: Type)
  (#t2: (t1 -> Type))
  (l12: clens t1 t2)
  (#t3: ((x: t1) -> t2 x -> Type))
  (l23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (x: t1)
: Tot Type
= if l12.clens_cond x then t3 x (l12.clens_get x) else False

let clens_compose_get
  (#t1: Type)
  (#t2: (t1 -> Type))
  (l12: clens t1 t2)
  (#t3: ((x: t1) -> t2 x -> Type))
  (l23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (x1: t1 { clens_compose_cond l12 l23 x1 } )
: GTot (clens_compose_type l12 l23 x1)
= 
    let x2 = l12.clens_get x1 in
    let l23' : clens (t2 x1) (t3 x1) = l23 x1 in
    let x3 : t3 x1 x2 = l23'.clens_get x2 in
    x3

let clens_compose
  (#t1: Type)
  (#t2: t1 -> Type)
  (#t3: (x: t1) -> t2 x -> Type)
  (l12: clens t1 t2)
  (l23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
: Tot (clens t1 (clens_compose_type l12 l23))
= {
  clens_cond = clens_compose_cond l12 l23;
  clens_get = clens_compose_get l12 l23;
}

(*  
  clens_put = (fun x1 x3 ->
    let x2' = l23.clens_put (l12.clens_get x1) x3 in
    let x1' = l12.clens_put x1 x2' in
    x1'
  );
  clens_get_put = (fun x1 x3 -> ());
  clens_put_put = (fun x1 x3 x3' -> ());
  clens_put_get = (fun x1 -> ());
*)

(*
let clens_compose_strong_pre
  (#t1: Type)
  (#t2: Type)
  (#t3: Type)
  (l12: clens t1 t2)
  (l23: clens t2 t3)
: GTot Type0
= forall (x: t1) . {:pattern (l12.clens_cond x) \/ (l23.clens_cond (l12.clens_get x))} l12.clens_cond x ==> l23.clens_cond (l12.clens_get x)

let clens_compose_strong
  (#t1: Type)
  (#t2: Type)
  (#t3: Type)
  (l12: clens t1 t2)
  (l23: clens t2 t3 { clens_compose_strong_pre l12 l23 })
: Tot (clens t1 t3)
= {
  clens_cond = l12.clens_cond;
  clens_get = (fun x1 -> l23.clens_get (l12.clens_get x1));
}
*)

(*
abstract
let clens_disjoint_compose
  (#t0: Type)
  (#clens_cond2: t0 -> GTot Type0)
  (#clens_cond3: t0 -> GTot Type0)
  (#t2 #t3: Type)
  (l2: clens clens_cond2 t2)
  (l3: clens clens_cond3 t3)
  (#clens_cond3': t3 -> GTot Type0)
  (#t3' : Type)
  (l3' : clens clens_cond3' t3')
: Lemma
  (requires (clens_disjoint l2 l3))
  (ensures (clens_disjoint l2 (clens_compose l3 l3')))
  [SMTPat (clens_disjoint l2 (clens_compose l3 l3'))]
= ()
*)

let gaccessor_pre
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (cl: clens t1 t2)
  (p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (sl: bytes)
: GTot Type0
= match parse p1 sl with
  | Some (x1, consumed) -> (consumed <: nat) == Seq.length sl /\ cl.clens_cond x1
  | _ -> False

let gaccessor_post
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (cl: clens t1 t2)
  (p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (sl: bytes)
  (res : nat & nat)
: GTot Type0
= let (pos', len) = res in
  pos' + len <= Seq.length sl /\
  begin match parse p1 sl with
  | Some (x1, consumed1) ->
    cl.clens_cond x1 /\
    begin match parse (p2 x1) (Seq.slice sl pos' (pos' + len)) with
    | Some (x2, consumed2) ->
      x2 == cl.clens_get x1 /\
      pos' + consumed2 <= consumed1 /\
      consumed2 == len
    | _ -> False
    end
  | _ -> False
  end

let gaccessor_post' 
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (cl: clens t1 t2)
  (p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (sl : bytes)
  (res: nat & nat)
: GTot Type0
= 
    let (pos', len') = res in pos' + len' <= Seq.length sl /\
    (gaccessor_pre p1 cl p2 sl ==> gaccessor_post p1 cl p2 sl res)

[@unifier_hint_injective]
let gaccessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (cl: clens t1 t2)
  (p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
: Tot Type
= (sl: bytes) ->
  Ghost (nat & nat)
  (requires True)
  (ensures (fun res ->
    gaccessor_post' p1 cl p2 sl res
  ))

let get_gaccessor_clens
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl: clens t1 t2)
  (#p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl p2)
: Tot (clens t1 t2)
= cl

abstract
let gaccessors_disjoint
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl2: clens t1 t2)
  (#p2: (x: t1 { cl2.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g2: gaccessor p1 cl2 p2)
  (#k3: parser_kind)
  (#t3: t1 -> Type)
  (#cl3: clens t1 t3)
  (#p3: (x: t1 { cl3.clens_cond x } ) -> GTot (parser k3 (t3 x)))
  (g3: gaccessor p1 cl3 p3)
: GTot Type0
= // clens_disjoint cl2 cl3 /\
  (forall (sl: bytes) . (
     match parse p1 sl with
     | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
     | _ -> False
   ) ==> (
   let (pos2, consumed2) = g2 sl in
   let (pos3, consumed3) = g3 sl in
   pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
  ))

(*
abstract
let gaccessors_disjoint_clens_disjoint
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#pre2: t1 -> GTot Type0)
  (#cl2: clens pre2 t2)
  (g2: gaccessor p1 p2 cl2)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#pre3: t1 -> GTot Type0)
  (#cl3: clens pre3 t3)
  (g3: gaccessor p1 p3 cl3)
: Lemma
  (requires (gaccessors_disjoint g2 g3))
  (ensures (clens_disjoint cl2 cl3))
  [SMTPat (gaccessors_disjoint g2 g3)]
= ()
*)

abstract
let gaccessors_disjoint_elim
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl2: clens t1 t2)
  (#p2: (x: t1 { cl2.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g2: gaccessor p1 cl2 p2)
  (#k3: parser_kind)
  (#t3: t1 -> Type)
  (#cl3: clens t1 t3)
  (#p3: (x: t1 { cl3.clens_cond x } ) -> GTot (parser k3 (t3 x)))
  (g3: gaccessor p1 cl3 p3)
  (sl: bytes)
: Lemma
  (requires (gaccessors_disjoint g2 g3 /\ (
     match parse p1 sl with
     | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
     | _ -> False
  )))
  (ensures (
    let (pos2, consumed2) = g2 sl in
    let (pos3, consumed3) = g3 sl in
    pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
  ))
= ()

abstract
let gaccessors_disjoint_intro
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl2: clens t1 t2)
  (#p2: (x: t1 { cl2.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g2: gaccessor p1 cl2 p2)
  (#k3: parser_kind)
  (#t3: t1 -> Type)
  (#cl3: clens t1 t3)
  (#p3: (x: t1 { cl3.clens_cond x } ) -> GTot (parser k3 (t3 x)))
  (g3: gaccessor p1 cl3 p3)
//  (clens_disj: squash (clens_disjoint cl2 cl3))
  (lem: (
    (sl: bytes) ->
    Lemma
    (requires (
      match parse p1 sl with
      | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
      | _ -> False
    ))
    (ensures ((
      match parse p1 sl with
      | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
      | _ -> False) /\ (
      let (pos2, consumed2) = g2 sl in
      let (pos3, consumed3) = g3 sl in
      pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
    )))
  ))
: Lemma
  (gaccessors_disjoint g2 g3)
= let lem'
   (sl: bytes)
 : Lemma
   ((
     match parse p1 sl with
     | Some (x1, consumed1) -> cl2.clens_cond x1 /\ cl3.clens_cond x1 /\ consumed1 == Seq.length sl
     | _ -> False
   ) ==> (
   let (pos2, consumed2) = g2 sl in
   let (pos3, consumed3) = g3 sl in
   pos2 + consumed2 <= pos3 \/ pos3 + consumed3 <= pos2
   ))
 = Classical.move_requires lem sl
 in
 Classical.forall_intro lem'

let gaccessor_id'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Ghost (nat & nat)
  (requires True)
  (ensures (fun res -> gaccessor_post' p (clens_id _) (fun _ -> p) input res))
= (0, Seq.length input)

abstract
let gaccessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (gaccessor p (clens_id _) (fun _ -> p))
= gaccessor_id' p

abstract
let gaccessor_id_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (gaccessor_id p input == gaccessor_id' p input)
= ()

let gaccessor_ext'
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl: clens t1 t2)
  (#p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl p2)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
  (input: bytes)
: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' p1 cl' p2 input res))
= g input

abstract
let gaccessor_ext
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl: clens t1 t2)
  (#p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl p2)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
: Tot (gaccessor p1 cl' p2)
= gaccessor_ext' g cl' sq

abstract
let gaccessor_ext_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl: clens t1 t2)
  (#p2: (x: t1 { cl.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl p2)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl cl'))
  (input: bytes)
: Lemma
  (gaccessor_ext g cl sq input == gaccessor_ext' g cl sq input)
= ()

let gaccessor_compose_parser
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (cl12: clens t1 t2)
  (p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (#k3: parser_kind)
  (#t3: (x: t1) -> t2 x -> Type)
  (cl23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (p3: (x1: t1 { cl12.clens_cond x1 } ) -> (x2: t2 x1 { (cl23 x1).clens_cond x2 }) -> GTot (parser k3 (t3 x1 x2)))
  (x1: t1 { (clens_compose cl12 cl23).clens_cond x1 })
: GTot (parser k3 (clens_compose_type cl12 cl23 x1))
= p3 x1 (cl12.clens_get x1)

let gaccessor_compose'
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (a12: gaccessor p1 cl12 p2)
  (#k3: parser_kind)
  (#t3: (x: t1) -> t2 x -> Type)
  (#cl23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (#p3: (x1: t1 { cl12.clens_cond x1 } ) -> (x2: t2 x1 { (cl23 x1).clens_cond x2 }) -> GTot (parser k3 (t3 x1 x2)))
  (a23: (x: t1 {cl12.clens_cond x}) -> GTot (gaccessor (p2 x) (cl23 x) (p3 x)))
  (input: bytes)
: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' p1 (clens_compose cl12 cl23) (gaccessor_compose_parser p1 cl12 p2 cl23 p3) input res))
= let (pos2, consumed2) = a12 input in
  let input2 = Seq.slice input pos2 (pos2 + consumed2) in
  match parse p1 input with
  | None -> (0, 0) // dummy
  | Some (x, _) ->
    if cl12.clens_cond x
    then
      let (pos3, consumed3) = a23 x input2 in
      (pos2 + pos3, consumed3)
    else (0, 0) // dummy

abstract
let gaccessor_compose
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (a12: gaccessor p1 cl12 p2)
  (#k3: parser_kind)
  (#t3: (x: t1) -> t2 x -> Type)
  (#cl23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (#p3: (x1: t1 { cl12.clens_cond x1 } ) -> (x2: t2 x1 { (cl23 x1).clens_cond x2 }) -> GTot (parser k3 (t3 x1 x2)))
  (a23: (x: t1 {cl12.clens_cond x}) -> GTot (gaccessor (p2 x) (cl23 x) (p3 x)))
: Tot (gaccessor p1 (clens_compose cl12 cl23) (gaccessor_compose_parser p1 cl12 p2 cl23 p3))
= gaccessor_compose' a12 #k3 #t3 #cl23 #p3 a23

abstract
let gaccessor_compose_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (a12: gaccessor p1 cl12 p2)
  (#k3: parser_kind)
  (#t3: (x: t1) -> t2 x -> Type)
  (#cl23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (#p3: (x1: t1 { cl12.clens_cond x1 } ) -> (x2: t2 x1 { (cl23 x1).clens_cond x2 }) -> GTot (parser k3 (t3 x1 x2)))
  (a23: (x: t1 {cl12.clens_cond x}) -> GTot (gaccessor (p2 x) (cl23 x) (p3 x)))
  (input: bytes)
: Lemma
  (gaccessor_compose a12 #_ #_ #cl23 a23 input == gaccessor_compose' a12 #_ #_ #cl23 a23 input)
= ()

let slice_access'
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost U32.t
  (requires (
    valid' p1 h sl pos
  ))
  (ensures (fun pos' -> True))
= 
  let small = bytes_of_slice_from_to h sl pos (pos `U32.add` U32.uint_to_t (content_length' p1 h sl pos)) in
  pos `U32.add` U32.uint_to_t (fst (g small))

[@"opaque_to_smt"]
abstract
let slice_access
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
  (sl: slice rrel rel)
  (pos: U32.t)
: Ghost U32.t
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl12.clens_cond (contents p1 h sl pos)
  ))
  (ensures (fun pos' -> True))
= valid_facts p1 h sl pos;
  slice_access' h g sl pos

abstract
let slice_access_eq
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl12.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    valid' p1 h sl pos /\
    cl12.clens_cond (contents' p1 h sl pos) /\
    slice_access h g sl pos == slice_access' h g sl pos
  ))
= valid_facts p1 h sl pos;
  assert_norm (slice_access h g sl pos == slice_access' h g sl pos)

#push-options "--z3rlimit 32"

abstract
let slice_access_post
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl12.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    let pos' = slice_access h g sl pos in
    let x = contents p1 h sl pos in
    valid (p2 x) h sl pos' /\
    contents (p2 x) h sl pos' == cl12.clens_get x /\
    // useful for framing
    U32.v pos <= U32.v pos' /\
    U32.v pos' + content_length (p2 x) h sl pos' <= U32.v pos + content_length p1 h sl pos
  ))
  [SMTPat (slice_access h g sl pos)]
= slice_access_eq h g sl pos;
  valid_facts p1 h sl pos;
  assert_norm (pow2 32 == 4294967296);
  let res = slice_access' h g sl pos in
  let x = contents p1 h sl pos in
  valid_facts (p2 x) h sl res;
  let input_large = bytes_of_slice_from h sl pos in
  let input_small = bytes_of_slice_from_to h sl pos (pos `U32.add` U32.uint_to_t (content_length' p1 h sl pos)) in
  parse_strong_prefix p1 input_large input_small;
  let output_small = bytes_of_slice_from_to h sl res (res `U32.add` U32.uint_to_t (snd (g input_small))) in
  let output_large = bytes_of_slice_from h sl res in
  parse_strong_prefix (p2 x) output_small output_large

#pop-options

#push-options "--z3rlimit 256 --max_fuel 0 --max_ifuel 6 --initial_ifuel 6"

abstract
let slice_access_eq_inv
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
  (sl: slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl12.clens_cond (contents p1 h sl pos)
  ))
  (ensures (
    let pos2 = slice_access h g sl pos in
    g (bytes_of_slice_from_to h sl pos (pos `U32.add` U32.uint_to_t (content_length p1 h sl pos))) ==
      (U32.v pos2 - U32.v pos, content_length (p2 (contents p1 h sl pos)) h sl pos2)
  ))
= valid_facts p1 h sl pos;
  slice_access_eq h g sl pos;
  let res = slice_access' h g sl pos in
  let x = contents p1 h sl pos in
  valid_facts (p2 x) h sl res;
    let input_large = bytes_of_slice_from h sl pos in
    let input_small = bytes_of_slice_from_to h sl pos (pos `U32.add` U32.uint_to_t (content_length' p1 h sl pos)) in
    parse_strong_prefix p1 input_large input_small;
    let output_small = bytes_of_slice_from_to h sl res (res `U32.add` U32.uint_to_t (snd (g input_small))) in
    let output_large = bytes_of_slice_from h sl res in
    parse_strong_prefix (p2 x) output_small output_large

#pop-options

abstract
let slice_access_frame
  (#rrel #rel: _)
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
  (sl: slice rrel rel)
  (pos: U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h sl pos /\
    cl12.clens_cond (contents p1 h sl pos) /\
    B.modifies l h h' /\
    B.loc_disjoint l (loc_slice_from_to sl pos (get_valid_pos p1 h sl pos))
  ))
  (ensures (
    valid p1 h' sl pos /\
    cl12.clens_cond (contents p1 h' sl pos) /\
    slice_access h' g sl pos == slice_access h g sl pos
  ))
  [SMTPatOr [
    [SMTPat (slice_access h g sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (slice_access h' g sl pos); SMTPat (B.modifies l h h')];
  ]]
= valid_facts p1 h sl pos;
  valid_facts p1 h' sl pos;
  slice_access_eq h g sl pos;
  slice_access_eq h' g sl pos;
  B.modifies_buffer_from_to_elim sl.base pos (get_valid_pos p1 h sl pos) l h h'

[@unifier_hint_injective]
inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (g: gaccessor p1 cl12 p2)
: Tot Type
= (#rrel: _) ->
  (#rel: _) ->
  (sl: slice rrel rel) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> k1.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_subkind == Some ParserStrong /\ valid p1 h sl pos /\ cl12.clens_cond (contents p1 h sl pos))) 
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == slice_access h g sl pos
  ))

inline_for_extraction
let make_accessor_from_pure
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  ($g: gaccessor p1 cl12 p2)
  (f: (
    (input: Ghost.erased bytes) ->
    Pure U32.t
    (requires (Seq.length (Ghost.reveal input) < 4294967296 /\ gaccessor_pre p1 cl12 p2 (Ghost.reveal input)))
    (ensures (fun y -> U32.v y == fst (g (Ghost.reveal input))))
  ))
: Tot (accessor g)
= fun #rrel #rel sl (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ =
    slice_access_eq_inv h g sl pos;
    valid_facts p1 h sl pos;
    parse_strong_prefix p1 (bytes_of_slice_from h sl pos) (bytes_of_slice_from_to h sl pos (get_valid_pos p1 h sl pos))
  in
  pos `U32.add` f (Ghost.hide (bytes_of_slice_from_to h sl pos (get_valid_pos p1 h sl pos)))

inline_for_extraction
let accessor_id
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (accessor (gaccessor_id p))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_id p) input pos in
  pos

inline_for_extraction
let accessor_ext
  (#k1: parser_kind)
  (#t1: Type)
  (#k2: parser_kind)
  (#p1: parser k1 t1)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (#g: gaccessor p1 cl12 p2)
  (a: accessor g)
  (cl': clens t1 t2)
  (sq: squash (clens_eq cl12 cl'))
: Tot (accessor (gaccessor_ext g cl' sq))
= fun #rrel #rel input pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_ext g cl' sq) input pos;
    gaccessor_ext_eq g cl' sq (bytes_of_slice_from_to h input pos (pos `U32.add` U32.uint_to_t (content_length' p1 h input pos)));
    slice_access_eq h g input pos
  in
  a input pos

#push-options "--z3rlimit 256 --initial_ifuel 4 --max_fuel 2 --initial_fuel 2 --max_ifuel 4 --query_stats"

inline_for_extraction
let accessor_compose
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: t1 -> Type)
  (#cl12: clens t1 t2)
  (#p2: (x: t1 { cl12.clens_cond x } ) -> GTot (parser k2 (t2 x)))
  (#g12: gaccessor p1 cl12 p2)
  (a12: accessor g12)
  (#k3: parser_kind)
  (#t3: (x: t1) -> t2 x -> Type)
  (#cl23: (x: t1) -> GTot (clens (t2 x) (t3 x)))
  (#p3: (x1: t1 { cl12.clens_cond x1 } ) -> (x2: t2 x1 { (cl23 x1).clens_cond x2 }) -> GTot (parser k3 (t3 x1 x2)))
  (#g23: (x: t1 {cl12.clens_cond x}) -> GTot (gaccessor (p2 x) (cl23 x) (p3 x)))
  (a23 : ((x: Ghost.erased t1 {cl12.clens_cond (Ghost.reveal x)}) -> accessor #_ #_ #_ #(p2 (Ghost.reveal x)) #_ #(cl23 (Ghost.reveal x)) #(p3 (Ghost.reveal x)) (g23 (Ghost.reveal x))) {
    k2.parser_kind_subkind == Some ParserStrong
  })
: Tot (accessor (gaccessor_compose #k1 #t1 #p1 #k2 #t2 #cl12 #p2 g12 #k3 #t3 #cl23 #p3 g23))
= fun #rrel #rel input pos ->
  assert (k1.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_subkind == Some ParserStrong);
  let h = HST.get () in
  let x = Ghost.hide (contents p1 h input pos) in
  let pos2 = a12 input pos in
  let pos3 = a23 x input pos2 in
  slice_access_eq h g12 input pos;
  slice_access_eq_inv h g12 input pos;
  valid_facts p1 h input pos;
  parse_strong_prefix p1 (bytes_of_slice_from h input pos) (bytes_of_slice_from_to h input pos (pos `U32.add` U32.uint_to_t (content_length' p1 h input pos)));
  slice_access_eq_inv h #_ #_ #_ #(p2 (Ghost.reveal x)) #_ #(cl23 (Ghost.reveal x)) #(p3 (Ghost.reveal x)) (g23 (Ghost.reveal x)) input pos2;
  slice_access_eq_inv h (gaccessor_compose #k1 #t1 #p1 #k2 #t2 #cl12 #p2 g12 #k3 #t3 #cl23 #p3 g23) input pos;
  admit ();
  pos3

#pop-options
