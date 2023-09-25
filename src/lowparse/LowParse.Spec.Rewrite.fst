module LowParse.Spec.Rewrite
include LowParse.Spec.Combinators

module Seq = FStar.Seq

let can_rewrite
  (#t1 #t2: Type)
  (#k1 #k2: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
  (rewrite: t1 -> GTot (option t2))
: Tot prop
= forall (b: bytes) . match parse p1 b with
  | None -> True
  | Some (v1, len) ->
    begin match rewrite v1 with
    | None -> True
    | Some v2 -> parse p2 b == Some (v2, len)
    end

let can_rewrite_intro
  (#t1 #t2: Type)
  (#k1 #k2: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
  (rewrite: t1 -> GTot (option t2))
  (phi: (
    (b: bytes) ->
    (v1: t1) ->
    (len: consumed_length b) ->
    (v2: t2) ->
    Lemma
    (requires (
      parse p1 b == Some (v1, len) /\
      rewrite v1 == Some v2
    ))
    (ensures (
      parse p2 b == Some (v2, len)
    ))
  ))
: Lemma
  (can_rewrite p1 p2 rewrite)
= Classical.forall_intro_4 (fun b v1 len v2 -> Classical.move_requires (phi b v1 len) v2)

let can_rewrite_refl
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
: Lemma
  (can_rewrite p p Some)
= ()

let rewrite_compose
  (#t1 #t2 #t3: Type)
  (f12: (t1 -> GTot (option t2)))
  (f23: (t2 -> GTot (option t3)))
  (x1: t1)
: GTot (option t3)
= match f12 x1 with
  | None -> None
  | Some x2 -> f23 x2

let can_rewrite_trans
  (#t1 #t2 #t3: Type)
  (#k1 #k2 #k3: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
  (f12: (t1 -> GTot (option t2)))
  (p3: parser k3 t3)
  (f23: (t2 -> GTot (option t3)))
: Lemma
  (requires (
    can_rewrite p1 p2 f12 /\
    can_rewrite p2 p3 f23
  ))
  (ensures (
    can_rewrite p1 p3 (rewrite_compose f12 f23)
  ))
= ()

let rewrite_congr
  (#tl1 #tr1 #tl2 #tr2: Type)
  (rewrite_l: (tl1 -> GTot (option tl2)))
  (rewrite_r: (tr1 -> GTot (option tr2)))
  (x1: (tl1 & tr1))
: GTot (option (tl2 & tr2))
= match rewrite_l (fst x1), rewrite_r (snd x1) with
  | Some xl2, Some xr2 -> Some (xl2, xr2)
  | _ -> None

let can_rewrite_congr
  (#tl1 #tr1 #tl2 #tr2: Type)
  (#kl1 #kr1 #kl2 #kr2: parser_kind)
  (pl1: parser kl1 tl1)
  (pl2: parser kl2 tl2)
  (rewrite_l: (tl1 -> GTot (option tl2)))
  (pr1: parser kr1 tr1)
  (pr2: parser kr2 tr2)
  (rewrite_r: (tr1 -> GTot (option tr2)))
: Lemma
  (requires (
    can_rewrite pl1 pl2 rewrite_l /\
    can_rewrite pr1 pr2 rewrite_r
  ))
  (ensures (
    can_rewrite (pl1 `nondep_then` pr1) (pl2 `nondep_then` pr2) (rewrite_congr rewrite_l rewrite_r)
  ))
= can_rewrite_intro
    (pl1 `nondep_then` pr1)
    (pl2 `nondep_then` pr2)
    (rewrite_congr rewrite_l rewrite_r)
    (fun b v1 len v2 ->
      nondep_then_eq pl1 pr1 b;
      nondep_then_eq pl2 pr2 b
    )

let rewrite_assoc_l_to_r
  (#t1 #t2 #t3: Type)
  (x: ((t1 & t2) & t3))
: GTot (option (t1 & (t2 & t3)))
= Some (fst (fst x), (snd (fst x), snd x))

let can_rewrite_assoc_l_to_r
  (#t1 #t2 #t3: Type)
  (#k1 #k2 #k3: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
  (p3: parser k3 t3)
: Lemma
  (can_rewrite ((p1 `nondep_then` p2) `nondep_then` p3) (p1 `nondep_then` (p2 `nondep_then` p3)) rewrite_assoc_l_to_r)
= can_rewrite_intro
    ((p1 `nondep_then` p2) `nondep_then` p3)    
    (p1 `nondep_then` (p2 `nondep_then` p3))
    rewrite_assoc_l_to_r
    (fun b v1 len v2 ->
      nondep_then_eq (p1 `nondep_then` p2) p3 b;
      nondep_then_eq p1 (p2 `nondep_then` p3) b;
      nondep_then_eq p1 p2 b;
      let Some (_, len1) = parse p1 b in
      let b1 = Seq.slice b len1 (Seq.length b) in
      nondep_then_eq p2 p3 b1
    )

let rewrite_assoc_r_to_l
  (#t1 #t2 #t3: Type)
  (x: (t1 & (t2 & t3)))
: GTot (option ((t1 & t2) & t3))
= Some ((fst x, fst (snd x)), snd (snd x))

let can_rewrite_assoc_r_to_l
  (#t1 #t2 #t3: Type)
  (#k1 #k2 #k3: parser_kind)
  (p1: parser k1 t1)
  (p2: parser k2 t2)
  (p3: parser k3 t3)
: Lemma
  (can_rewrite (p1 `nondep_then` (p2 `nondep_then` p3)) ((p1 `nondep_then` p2) `nondep_then` p3) rewrite_assoc_r_to_l)
= can_rewrite_intro
    (p1 `nondep_then` (p2 `nondep_then` p3))
    ((p1 `nondep_then` p2) `nondep_then` p3)    
    rewrite_assoc_r_to_l
    (fun b v1 len v2 ->
      nondep_then_eq (p1 `nondep_then` p2) p3 b;
      nondep_then_eq p1 (p2 `nondep_then` p3) b;
      nondep_then_eq p1 p2 b;
      let Some (_, len1) = parse p1 b in
      let b1 = Seq.slice b len1 (Seq.length b) in
      nondep_then_eq p2 p3 b1
    )

let rewrite_filter_intro
  (#t: Type)
  (cond: (t -> GTot bool))
  (x: t)
: GTot (option (parse_filter_refine cond))
= if cond x
  then Some x
  else None

let can_rewrite_filter_intro
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (cond: (t -> GTot bool))
: Lemma
  (can_rewrite p (parse_filter p cond) (rewrite_filter_intro cond))
= can_rewrite_intro
    p
    (parse_filter p cond)
    (rewrite_filter_intro cond)
    (fun b v1 len v2 ->
      parse_filter_eq p cond b
    )

let can_rewrite_filter_elim
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (cond: (t -> GTot bool))
: Lemma
  (can_rewrite (parse_filter p cond) p Some)
= can_rewrite_intro
    (parse_filter p cond)
    p
    Some
    (fun b v1 len v2 ->
      parse_filter_eq p cond b
    )

let rewrite_synth
  (#t1 #t2: Type)
  (f: (t1 -> GTot t2))
  (x: t1)
: GTot (option t2)
= Some (f x)

let can_rewrite_synth_intro
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (#t': Type)
  (f: (t -> GTot t') { synth_injective f })
: Lemma
  (can_rewrite p (p `parse_synth` f) (rewrite_synth f))
= can_rewrite_intro
    p
    (p `parse_synth` f)
    (rewrite_synth f)
    (fun b v1 len v2 ->
      parse_synth_eq p f b
    )

let can_rewrite_synth_elim
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (#t': Type)
  (f: (t -> GTot t') { synth_injective f })
  (f': (t' -> GTot t) { synth_inverse f f' })
: Lemma
  (can_rewrite (p `parse_synth` f) p (rewrite_synth f'))
= can_rewrite_intro
    (p `parse_synth` f) 
    p
    (rewrite_synth f')
    (fun b v1 len v2 ->
      parse_synth_eq p f b;
      assert (v1 == f v2)
    )
  
let rewrite_dtuple2_intro 
  (#tag_t: Type)
  (#payload_t: (tag_t -> Type))
  (#payload_k: parser_kind)
  (payload_p: ((tag: tag_t) -> parser payload_k (payload_t tag)))
  (#some_payload_t: Type)
  (some_payload_p: parser payload_k some_payload_t)
  (x: (tag_t & some_payload_t))
: GTot (option (dtuple2 tag_t payload_t))
= if FStar.StrongExcludedMiddle.strong_excluded_middle
    (some_payload_t == payload_t (fst x) /\
      some_payload_p == payload_p (fst x)
    )
  then
    Some (| fst x, snd x |)
  else
    None

let can_rewrite_dtuple2_intro 
  (#tag_t: Type)
  (#tag_k: parser_kind)
  (tag_p: parser tag_k tag_t)
  (#payload_t: (tag_t -> Type))
  (#payload_k: parser_kind)
  (payload_p: ((tag: tag_t) -> parser payload_k (payload_t tag)))
  (#some_payload_t: Type)
  (some_payload_p: parser payload_k some_payload_t)
: Lemma
  (can_rewrite (tag_p `nondep_then` some_payload_p) (tag_p `parse_dtuple2` payload_p) (rewrite_dtuple2_intro payload_p some_payload_p))
= can_rewrite_intro
    (tag_p `nondep_then` some_payload_p)
    (tag_p `parse_dtuple2` payload_p)
    (rewrite_dtuple2_intro payload_p some_payload_p)
    (fun b v1 len v2 ->
      nondep_then_eq tag_p some_payload_p b;
      parse_dtuple2_eq tag_p payload_p b
    )
