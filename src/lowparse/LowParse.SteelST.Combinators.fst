module LowParse.SteelST.Combinators
include LowParse.Spec.Combinators
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
include LowParse.SteelST.ValidateAndRead
include LowParse.SteelST.Write
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module R = Steel.ST.Reference
module SZ = FStar.SizeT

#set-options "--ide_id_info_off"

module T = FStar.Tactics

inline_for_extraction
let rewrite_validator
  (#k1: Ghost.erased parser_kind) (#t1: Type) (#p1: parser k1 t1) (v1: validator p1)
  (#k2: Ghost.erased parser_kind) (#t2: Type) (p2: parser k2 t2)
: Pure (validator p2)
  (requires (
    (forall bytes . (
      Some? (parse p1 bytes) == Some? (parse p2 bytes) /\ (
      (Some? (parse p1 bytes) /\ Some? (parse p2 bytes)) ==>
      sndp (Some?.v (parse p1 bytes)) == sndp (Some?.v (parse p2 bytes))
    )))
  ))
  (ensures (fun _ -> True))
= fun #va a len err ->
  let res = v1 a len err in
  let _ = gen_elim () in
  return res

inline_for_extraction
let rewrite_validator'
  (#k1: Ghost.erased parser_kind) (#t1: Type) (#p1: parser k1 t1) (v1: validator p1)
  (#k2: Ghost.erased parser_kind) (#t2: Type) (p2: parser k2 t2)
  (prf: (
    (b: bytes) ->
    Lemma
    (Some? (parse p1 b) == Some? (parse p2 b) /\ (
      (Some? (parse p1 b) /\ Some? (parse p2 b)) ==>
      sndp (Some?.v (parse p1 b)) == sndp (Some?.v (parse p2 b))
    ))
  ))
: Tot (validator p2)
= Classical.forall_intro prf;
  rewrite_validator v1 p2

inline_for_extraction
let validate_weaken
  (k1: Ghost.erased parser_kind) (#k2: Ghost.erased parser_kind) (#t: Type) (#p2: parser k2 t) (v2: validator p2)
  (_: squash (k1 `is_weaker_than` k2))
: Tot (validator (LowParse.Spec.Base.weaken k1 p2))
= rewrite_validator v2 (LowParse.Spec.Base.weaken k1 p2)

inline_for_extraction
let rewrite_validate_and_read
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: validate_and_read p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Pure (validate_and_read p2)
    (requires (
      t1 == t2 /\
      (forall b . parse p1 b == parse p2 b)
    ))
    (ensures (fun _ -> True))
= fun a len pre t' post fsuccess ffailure ->
    v1 a len pre t' post
      (fun lenl w a' ->
        let _ = rewrite_aparse a p2 in
        fsuccess lenl w a'
      )
      (fun e -> ffailure e)

inline_for_extraction
let validate_and_read_weaken
  (k1: Ghost.erased parser_kind)
  (#k2: Ghost.erased parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (v2: validate_and_read p2)
  (_: squash (k1 `is_weaker_than` k2))
: Tot (validate_and_read (LowParse.Spec.Base.weaken k1 p2))
= rewrite_validate_and_read v2 (LowParse.Spec.Base.weaken k1 p2)

inline_for_extraction
let rewrite_jumper
  (#k1: Ghost.erased parser_kind) (#t1: Type) (#p1: parser k1 t1) (v1: jumper p1)
  (#k2: Ghost.erased parser_kind) (#t2: Type) (p2: parser k2 t2)
: Pure (jumper p2)
  (requires (
    (forall bytes . (
      Some? (parse p2 bytes) ==> (
        Some? (parse p1 bytes) /\
        sndp (Some?.v (parse p1 bytes)) == sndp (Some?.v (parse p2 bytes))
    )))
  ))
  (ensures (fun _ -> True))
= fun #va a ->
  let res = v1 a in
  let _ = gen_elim () in
  return res

inline_for_extraction
let rewrite_jumper'
  (#k1: Ghost.erased parser_kind) (#t1: Type) (#p1: parser k1 t1) (v1: jumper p1)
  (#k2: Ghost.erased parser_kind) (#t2: Type) (p2: parser k2 t2)
  (prf: (
    (b: bytes) ->
    Lemma
    (Some? (parse p2 b) ==> (
      Some? (parse p1 b) /\
      sndp (Some?.v (parse p1 b)) == sndp (Some?.v (parse p2 b))
    ))
  ))
: Tot (jumper p2)
= Classical.forall_intro prf;
  rewrite_jumper v1 p2

inline_for_extraction
let jump_weaken
  (k1: Ghost.erased parser_kind) (#k2: Ghost.erased parser_kind) (#t: Type) (#p2: parser k2 t) (v2: jumper p2)
  (_: squash (k1 `is_weaker_than` k2))
: Tot (jumper (LowParse.Spec.Base.weaken k1 p2))
= rewrite_jumper v2 (LowParse.Spec.Base.weaken k1 p2)

inline_for_extraction
let rewrite_read_and_jump
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: read_and_jump p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Pure (read_and_jump p2)
    (requires (
      t1 == t2 /\
      (forall b . parse p1 b == parse p2 b)
    ))
    (ensures (fun _ -> True))
= fun #va a pre t' post f ->
    let _ = rewrite_aparse a p1 in
    v1 a pre t' post
      (fun lenl w ->
        let _ = rewrite_aparse a p2 in
        vpattern_rewrite (aparse p2 a) va;
        f lenl w
      )

inline_for_extraction
let read_and_jump_weaken
  (k1: Ghost.erased parser_kind)
  (#k2: Ghost.erased parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (v2: read_and_jump p2)
  (_: squash (k1 `is_weaker_than` k2))
: Tot (read_and_jump (LowParse.Spec.Base.weaken k1 p2))
= rewrite_read_and_jump v2 (LowParse.Spec.Base.weaken k1 p2)

inline_for_extraction
let cps_read_weaken
  (#k: Ghost.erased parser_kind)
  (k': Ghost.erased parser_kind { k' `is_weaker_than` k })
  (#t: Type)
  (#p: parser k t)
  (r: cps_reader p)
: Tot (cps_reader (LowParse.Spec.Base.weaken k' p))
= fun #va a pre t' post f ->
  let _ = rewrite_aparse a p in
  r a pre t' post (fun v ->
    let _ = rewrite_aparse a (LowParse.Spec.Base.weaken k' p) in
    vpattern_rewrite (aparse (LowParse.Spec.Base.weaken k' p) a) va;
    f v
  )

inline_for_extraction
let read_weaken
  (#k: Ghost.erased parser_kind)
  (k': Ghost.erased parser_kind { k' `is_weaker_than` k })
  (#t: Type)
  (#p: parser k t)
  (r: leaf_reader p)
: Tot (leaf_reader (LowParse.Spec.Base.weaken k' p))
= fun #va a ->
  let _ = rewrite_aparse a p in
  let res = r a in
  let _ = rewrite_aparse a (LowParse.Spec.Base.weaken k' p) in
  vpattern_rewrite (aparse (LowParse.Spec.Base.weaken k' p) a) va;
  return res

inline_for_extraction
let rewrite_reader
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (r1: leaf_reader p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Pure (leaf_reader p2)
    (requires (
      t1 == t2 /\
      (forall (b: bytes) . parse p1 b == parse p2 b)
    ))
    (ensures (fun _ -> True))
= fun #va a ->
    let _ = rewrite_aparse a p1 in
    let res = r1 a in
    let _ = rewrite_aparse a p2 in
    vpattern_rewrite (aparse p2 a) va;
    return res

inline_for_extraction
let validate_empty : validator parse_empty =
  validate_total_constant_size parse_empty 0sz

inline_for_extraction
let jump_empty : jumper parse_empty
= jump_constant_size parse_empty 0sz

inline_for_extraction
let read_empty : leaf_reader parse_empty = fun _ -> return ()

#push-options "--z3rlimit 24"
#restart-solver

inline_for_extraction
let validate_pair
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v1: validator p1)
  (#k2: Ghost.erased parser_kind) #t2 (#p2: parser k2 t2) (v2: validator p2)
: Tot (validator (p1 `nondep_then` p2))
=
  fun #va a len err ->
    nondep_then_eq p1 p2 (AP.contents_of' va);
    let s1 = v1 a len err in
    let _ = gen_elim () in
    let verr = R.read err in
    if verr = 0ul
    then begin
      let ar = AP.split a s1 in
      let _ = gen_elim () in
      let len2 = len `SZ.sub` s1 in
      let s2 = v2 ar len2 err in
      let _ = gen_elim () in
      let aj = AP.join a ar in
      let sz = s1 `SZ.add` s2 in
      noop ();
      return sz
    end
    else
    begin
      noop ();
      return s1
    end

inline_for_extraction
let jump_pair
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v1: jumper p1)
  (#k2: Ghost.erased parser_kind) #t2 (#p2: parser k2 t2) (v2: jumper p2)
: Tot (jumper (p1 `nondep_then` p2))
=
  fun #va a ->
    nondep_then_eq p1 p2 (AP.contents_of' va);
    let s1 = v1 a in
    let _ = gen_elim () in
    let ar = AP.split a s1 in
    let _ = gen_elim () in
    let s2 = v2 ar in
    let _ = gen_elim () in
    let _ = AP.join a ar in
    return (s1 `SZ.add` s2)

#pop-options

let g_split_pair
  #opened
  #k1 (#t1: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p1: parser k1 t1)
  #k2 #t2 (p2: parser k2 t2)
  #y (a: byte_array)
: STGhost (Ghost.erased (byte_array)) opened
    (aparse (p1 `nondep_then` p2) a y)
    (fun a2 -> exists_ (fun y1 -> exists_ (fun y2 ->
      aparse p1 a y1 `star`
      aparse p2 a2 y2 `star`
      pure (
        AP.merge_into (array_of y1) (array_of y2) (array_of y) /\
        y.contents == (y1.contents, y2.contents)
    ))))
    (k1.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let b = elim_aparse _ a in
  nondep_then_eq p1 p2 (AP.contents_of' b);
  let res = ghost_peek_strong p1 a in
  let _ = gen_elim () in
  let _ = intro_aparse p2 res in
  res

inline_for_extraction
let split_pair'
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (j1: jumper p1)
  (#k2: Ghost.erased parser_kind) #t2 (p2: parser k2 t2)
  #y1 #y2 (a1: byte_array) (a2: Ghost.erased (byte_array))
: ST (byte_array)
    (aparse p1 a1 y1 `star` aparse p2 a2 y2)
    (fun res -> aparse p1 a1 y1 `star` aparse p2 res y2)
    (AP.adjacent (array_of y1) (array_of y2))
    (fun res -> res == Ghost.reveal a2)
= let sz = get_parsed_size j1 a1 in
  let _ = elim_aparse p1 a1 in
  let _ = elim_aparse p2 a2 in
  let res = AP.split' a1 sz a2 in
  let _ = gen_elim () in
  let _ = intro_aparse p1 a1 in
  let _ = intro_aparse p2 res in
  rewrite
    (aparse p1 a1 _)
    (aparse p1 a1 y1);
  return res

inline_for_extraction
let split_pair
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (j1: jumper p1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p2: parser k2 t2)
  #y (a: byte_array)
: ST (byte_array)
    (aparse (p1 `nondep_then` p2) a y)
    (fun a2 -> exists_ (fun y1 -> exists_ (fun y2 ->
      aparse p1 a y1 `star`
      aparse p2 a2 y2 `star`
      pure (
        AP.merge_into (array_of y1) (array_of y2) (array_of y) /\
        y.contents == (y1.contents, y2.contents)
    ))))
    (k1.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let a2 = g_split_pair p1 p2 a in
  let _ = gen_elim () in
  let res = split_pair' j1 p2 a a2 in
  res

let merge_pair
  #opened
  #k1 #t1 (p1: parser k1 t1)
  #k2 #t2 (p2: parser k2 t2)
  #y1 #y2 (a1 a2: byte_array)
: STGhost (v (and_then_kind k1 k2) (t1 & t2)) opened
    (aparse p1 a1 y1 `star` aparse p2 a2 y2)
    (fun y ->
      aparse (p1 `nondep_then` p2) a1 y)
    (k1.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of y1) (array_of y2))
    (fun y ->
      AP.merge_into (array_of y1) (array_of y2) (array_of y) /\
      y.contents == (y1.contents, y2.contents)
    )
= let va1 = elim_aparse p1 a1 in
  let va2 = elim_aparse p2 a2 in
  let va = AP.join a1 a2 in
  let _ = gen_elim () in
  nondep_then_eq p1 p2 (AP.contents_of' va);
  parse_strong_prefix p1 (AP.contents_of' va1) (AP.contents_of' va);
  assert (AP.contents_of' va2 `Seq.equal` Seq.slice (AP.contents_of' va) (AP.length (AP.array_of va1)) (AP.length (AP.array_of va)));
  intro_aparse (p1 `nondep_then` p2) a1

let clens_fst
  (t1: Type)
  (t2: Type)
: Tot (clens (t1 & t2) t1)
= {
  clens_cond = (fun (x: (t1 & t2)) -> True);
  clens_get = fst;
(*  
  clens_put = (fun x y -> (y, snd x));
  clens_get_put = (fun x y -> ());
  clens_put_put = (fun x y y' -> ());
  clens_put_get = (fun x -> ());
*)
}

inline_for_extraction
let with_pair_fst
  (#k1: Ghost.erased parser_kind) #t1 (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind) (#t2: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p2: parser k2 t2)
: Pure (accessor (p1 `nondep_then` p2) p1 (clens_fst _ _))
    (k1.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= fun #va a body ->
  let pi = AP.array_perm (array_of' va) in
  let _ = share_aparse (nondep_then p1 p2) a (half_perm pi) (half_perm pi) in
  let ar = g_split_pair p1 p2 a in
  let _ = gen_elim () in
  let res = body a in
  let va1 = merge_pair p1 p2 a ar in
  let _ = gather_aparse (nondep_then p1 p2) #va1 a in
  rewrite (aparse (nondep_then p1 p2) a _) (aparse (nondep_then p1 p2) a va);
  return res

let clens_snd
  (t1: Type)
  (t2: Type)
: Tot (clens (t1 & t2) t2)
= {
  clens_cond = (fun (x: (t1 & t2)) -> True);
  clens_get = snd;
(*  
  clens_put = (fun x y -> (fst x, y));
  clens_get_put = (fun x y -> ());
  clens_put_put = (fun x y y' -> ());
  clens_put_get = (fun x -> ());
*)
}

inline_for_extraction
let with_pair_snd
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (j1: jumper p1)
  (#k2: Ghost.erased parser_kind) #t2 (p2: parser k2 t2)
: Pure (accessor (p1 `nondep_then` p2) p2 (clens_snd _ _))
    (k1.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= fun #va a body ->
  let pi = AP.array_perm (array_of' va) in
  let _ = share_aparse (nondep_then p1 p2) a (half_perm pi) (half_perm pi) in
  let ar = split_pair j1 p2 a in
  let _ = gen_elim () in
  let res = body ar in
  let va1 = merge_pair p1 p2 a ar in
  let _ = gather_aparse (nondep_then p1 p2) #va1 a in
  rewrite (aparse (nondep_then p1 p2) a _) (aparse (nondep_then p1 p2) a va);
  return res

inline_for_extraction
let validate_synth
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v1: validator p1)
  #t2 (f2: t1 -> GTot t2)
  (sq: squash (synth_injective f2))
: Tot (validator (p1 `parse_synth` f2))
=
  fun #va a len err ->
  parse_synth_eq p1 f2 (AP.contents_of' va);
  let res = v1 a len err in
  let _ = gen_elim () in
  return res

inline_for_extraction
let jump_synth
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v1: jumper p1)
  #t2 (f2: t1 -> GTot t2)
  (sq: squash (synth_injective f2))
: Tot (jumper (p1 `parse_synth` f2))
=
  fun #va a ->
  parse_synth_eq p1 f2 (AP.contents_of' va);
  let res = v1 a in
  let _ = gen_elim () in
  return res

let intro_synth
  #opened
  #k1 #t1 (p1: parser k1 t1)
  #t2 (f2: t1 -> GTot t2)
  #va (a: byte_array)
  (sq: squash (synth_injective f2))
: STGhost (v k1 t2) opened
    (aparse p1 a va)
    (fun va2 -> aparse (p1 `parse_synth` f2) a va2)
    True
    (fun va2 ->
      array_of va2 == array_of va /\
      va2.contents == f2 (va.contents)
    )
= let va' = elim_aparse p1 a in
  parse_synth_eq p1 f2 (AP.contents_of' va');
  intro_aparse (p1 `parse_synth` f2) a

let elim_synth
  #opened
  #k1 #t1 (p1: parser k1 t1)
  #t2 (f2: t1 -> GTot t2)
  #va2 (a: byte_array)
  (sq: squash (synth_injective f2))
: STGhost (v k1 t1) opened
    (aparse (p1 `parse_synth` f2) a va2)
    (fun va -> aparse p1 a va)
    True
    (fun va ->
      array_of va2 == array_of va /\
      va2.contents == f2 (va.contents)
    )
= let va' = elim_aparse (p1 `parse_synth` f2) a in
  parse_synth_eq p1 f2 (AP.contents_of' va');
  intro_aparse p1 a

inline_for_extraction
let cps_read_synth_cont
  (#t: Type)
  (y: t)
: Tot Type
= (pre: vprop) -> (t': Type) -> (post: (t' -> vprop)) -> (phi: ((y': t { y' == y }) -> STT t' pre post)) -> STT t' pre post

inline_for_extraction
let validate_and_read_synth
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v: validate_and_read p1)
  #t2 (f2: t1 -> GTot t2)
  (f2': (x: t1) -> cps_read_synth_cont (f2 x))
  (sq: squash (synth_injective f2))
: Tot (validate_and_read (p1 `parse_synth` f2))
= fun #va a len pre t' post fsuccess ffailure ->
    parse_synth_eq p1 f2 (AP.contents_of' va);
    v a len pre t' post
      (fun sz v #b' ar ->
        let va' = elim_aparse p1 a in
        parse_synth_eq p1 f2 (AP.contents_of va');
        parse_injective p1 (AP.contents_of va) (AP.contents_of' va');
        let va' = intro_aparse (p1 `parse_synth` f2) a in
        f2' v (aparse (p1 `parse_synth` f2) a va' `star` AP.arrayptr ar b' `star` pre) t' post (fun v' -> fsuccess sz v' ar)
      )
      (fun e -> ffailure e)

inline_for_extraction
let validate_and_read_synth'
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v: validate_and_read p1)
  #t2 (f2: t1 -> Tot t2)

  (sq: squash (synth_injective f2))
: Tot (validate_and_read (p1 `parse_synth` f2))
= validate_and_read_synth
    v
    f2
    (fun x pre t' post phi -> phi (f2 x))
    ()

inline_for_extraction
let read_and_jump_synth
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v: read_and_jump p1)
  #t2 (f2: t1 -> GTot t2)
  (f2': (x: t1) -> cps_read_synth_cont (f2 x))
  (sq: squash (synth_injective f2))
: Tot (read_and_jump (p1 `parse_synth` f2))
= fun #va a pre t' post f ->
    let _ = elim_synth p1 f2 a () in
    v a pre t' post
      (fun sz v ->
        let _ = intro_synth p1 f2 a () in
        f2' v (aparse (p1 `parse_synth` f2) a va `star` pre) t' post (fun v' -> f sz v')
      )

inline_for_extraction
let read_and_jump_synth'
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v: read_and_jump p1)
  #t2 (f2: t1 -> Tot t2)
  (sq: squash (synth_injective f2))
: Tot (read_and_jump (p1 `parse_synth` f2))
= read_and_jump_synth
    v
    f2
    (fun x pre t' post phi -> phi (f2 x))
    ()

inline_for_extraction
let cps_read_synth
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (r: cps_reader p1)
  #t2 (f2: t1 -> GTot t2)
  (f2': (x: t1) -> cps_read_synth_cont (f2 x))
  (sq: squash (synth_injective f2))
: Tot (cps_reader (p1 `parse_synth` f2))
= fun #va a pre t' post f ->
  let _ = elim_synth p1 f2 a () in
  r a pre t' post (fun r1 ->
    let _ = intro_synth p1 f2 a () in
    vpattern_rewrite (aparse (p1 `parse_synth` f2) a) va;
    f2' r1 (aparse (p1 `parse_synth` f2) a va `star` pre) _ post (fun y -> f y)
  )

inline_for_extraction
let cps_read_synth'
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (r: cps_reader p1)
  #t2 (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x }))
  (sq: squash (synth_injective f2))
: Tot (cps_reader (p1 `parse_synth` f2))
= cps_read_synth r f2 (fun x pre t' post phi -> phi (f2' x)) ()

inline_for_extraction
let read_synth
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (r: leaf_reader p1)
  #t2 (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x }))
  (sq: squash (synth_injective f2))
: Tot (leaf_reader (p1 `parse_synth` f2))
= fun #va a ->
  let _ = elim_synth p1 f2 a () in
  let r1 = r a in
  let r2 : t2 = f2' r1 in
  let va' = intro_synth p1 f2 a () in
  rewrite (aparse (p1 `parse_synth` f2) a va') (aparse (p1 `parse_synth` f2) a va);
  return r2

inline_for_extraction
let read_synth'
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (r: leaf_reader p1)
  #t2 (f2: t1 -> Tot t2)
  (sq: squash (synth_injective f2))
: Tot (leaf_reader (p1 `parse_synth` f2))
= read_synth r f2 (fun x -> f2 x) sq

inline_for_extraction
let write_synth
  (#k: parser_kind)
  (#t1: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#p: parser k t1)
  (#s: serializer p)
  (w: writer s)
  #t2 (f12: t1 -> GTot t2)
  (f21: (t2 -> GTot t1))
  (f21': ((x: t2) -> Tot (y: t1 { y == f21 x })))
  (sq: squash (
    synth_injective f12 /\
    synth_inverse f12 f21
  ))
: Tot (writer (serialize_synth p f12 s f21 ()))
= fun x a ->
  serialize_synth_eq p f12 s f21 () x;
  let y = f21' x in
  let sz = w y a in
  let _ = gen_elim () in
  let _ = intro_synth p f12 a () in
  return sz

inline_for_extraction
let write_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#p: parser k t1)
  (#s: serializer p)
  (w: writer s)
  #t2 (f12: t1 -> GTot t2)
  (f21: (t2 -> Tot t1))
  (sq: squash (
    synth_injective f12 /\
    synth_inverse f12 f21
  ))
: Tot (writer (serialize_synth p f12 s f21 ()))
= write_synth w f12 f21 (fun x -> f21 x) ()

inline_for_extraction
let exact_write_synth
  (#k: parser_kind)
  (#t1: Type)
  (#p: parser k t1)
  (#s: serializer p)
  (w: exact_writer s)
  #t2 (f12: t1 -> GTot t2)
  (f21: (t2 -> GTot t1))
  (f21': ((x: t2) -> Tot (y: t1 { y == f21 x })))
  (sq: squash (
    synth_injective f12 /\
    synth_inverse f12 f21
  ))
: Tot (exact_writer (serialize_synth p f12 s f21 ()))
= fun x a ->
  serialize_synth_eq p f12 s f21 () x;
  let y = f21' x in
  let _ = w y a in
  intro_synth p f12 a ()

inline_for_extraction
let exact_write_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#p: parser k t1)
  (#s: serializer p)
  (w: exact_writer s)
  #t2 (f12: t1 -> GTot t2)
  (f21: (t2 -> Tot t1))
  (sq: squash (
    synth_injective f12 /\
    synth_inverse f12 f21
  ))
: Tot (exact_writer (serialize_synth p f12 s f21 ()))
= exact_write_synth w f12 f21 (fun x -> f21 x) ()

[@CMacro]
let validator_error_constraint_failed  = 2ul

inline_for_extraction
let validate_fail
  (k: parser_kind)
  (t: Type)
  (sq: squash (fail_parser_kind_precond k))
: Tot (validator (fail_parser k t))
= fun _ _ err ->
    R.write err validator_error_constraint_failed;
    return 0sz

inline_for_extraction
let jump_fail
  (k: parser_kind)
  (t: Type)
  (sq: squash (fail_parser_kind_precond k))
: Tot (jumper (fail_parser k t))
= fun a ->
    return 0sz // by contradiction

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let validate_filter_and_read
  (#k: Ghost.erased parser_kind) (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#p: parser k t) (v: validate_and_read p)
  (f: t -> GTot bool)
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Pure (validate_and_read (p  `parse_filter` f))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
=
  fun #va a len pre t' post fsuccess ffailure ->
    parse_filter_eq p f (AP.contents_of' va);
    v a len pre t' post
      (fun sz v ar ->
        if not (f' v)
        then begin
          unpeek_strong a va ar;
          ffailure validator_error_constraint_failed
        end else begin
          let va' = elim_aparse p a in
          parse_filter_eq p f (AP.contents_of va');
          parse_injective p (AP.contents_of va) (AP.contents_of' va');
          let _ = intro_aparse (p `parse_filter` f) a in
          fsuccess sz v ar
        end
      )
      (fun e -> ffailure e)

inline_for_extraction
let validate_filter_with_cps_reader
  (#k: Ghost.erased parser_kind) (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#p: parser k t) (v: validator p) (r: cps_reader p)
  (f: t -> GTot bool)
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Pure (validator (p  `parse_filter` f))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validator_of_validate_and_read
    (validate_filter_and_read
      (mk_validate_and_read v r)
      f
      f'
    )

#pop-options

inline_for_extraction
let validate_filter
  (#k: Ghost.erased parser_kind) (#t: Type)
  (#p: parser k t) (v: validator p) (r: leaf_reader p)
  (f: t -> GTot bool)
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Pure (validator (p  `parse_filter` f))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validate_filter_with_cps_reader v (cps_reader_of_leaf_reader r) f f'

inline_for_extraction
let jump_filter
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v1: jumper p1)
  (f2: t1 -> GTot bool)
: Tot (jumper (p1 `parse_filter` f2))
=
  fun #va a ->
  parse_filter_eq p1 f2 (AP.contents_of' va);
  let res = v1 a in
  let _ = gen_elim () in
  return res

let intro_filter
  #opened
  #k1 #t1 (p1: parser k1 t1)
  (f2: t1 -> GTot bool)
  #va (a: byte_array)
: STGhost (v (parse_filter_kind k1) (parse_filter_refine f2)) opened
    (aparse p1 a va)
    (fun va2 -> aparse (p1 `parse_filter` f2) a va2)
    (f2 va.contents)
    (fun va2 ->
      (array_of va2 <: AP.array byte) == array_of va /\
      (va2.contents <: t1) == va.contents
    )
= let va' = elim_aparse p1 a in
  parse_filter_eq p1 f2 (AP.contents_of' va');
  intro_aparse (p1 `parse_filter` f2) a

let elim_filter
  #opened
  #k1 #t1 (p1: parser k1 t1)
  (f2: t1 -> GTot bool)
  (#va2: v (parse_filter_kind k1) (parse_filter_refine f2)) (a: byte_array)
: STGhost (v k1 t1) opened
    (aparse (p1 `parse_filter` f2) a va2)
    (fun va -> aparse p1 a va)
    True
    (fun va ->
      (array_of va2 <: AP.array byte) == (array_of va <: AP.array byte) /\
      (va2.contents <: t1) == (va.contents <: t1) /\
      f2 va.contents
    )
= let va' = elim_aparse (p1 `parse_filter` f2) a in
  parse_filter_eq p1 f2 (AP.contents_of' va');
  intro_aparse p1 a

inline_for_extraction
let validate_filter_gen
  (#k: Ghost.erased parser_kind) (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#p: parser k t) (w: validator p)
  (f: t -> GTot bool)
  (f' : (
    (#va: v k t) ->
    (a: byte_array) ->
    ST bool
      (aparse p a va)
      (fun _ -> aparse p a va)
      True
      (fun res -> res == f va.contents)
  ))
: Pure (validator (p  `parse_filter` f))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va a len perr ->
    parse_filter_eq p f (AP.contents_of va);
    let consumed = w a len perr in
    let _ = gen_elim () in
    let err = R.read perr in
    if err <> 0ul
    then begin
      noop ();
      noop ();
      return consumed
    end else begin
      noop ();
      let ar = ghost_peek_strong p a in
      let _ = gen_elim () in
      let vl = elim_aparse p a in
      parse_injective p (AP.contents_of va) (AP.contents_of vl);
      parse_filter_eq p f (AP.contents_of vl);
      let _ = intro_aparse p a in
      let cond = f' a in
      unpeek_strong a va _;
      r_write_if (not cond) perr validator_error_constraint_failed;
      return consumed
    end

inline_for_extraction
let read_and_jump_filter
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (v1: read_and_jump p1)
  (f2: t1 -> GTot bool)
: Tot (read_and_jump (p1 `parse_filter` f2))
= fun #va a pre t post f ->
    let _ = elim_filter p1 f2 a in
    v1 a pre t post (fun res w ->
      let _ = intro_filter p1 f2 a in
      f res w
    )

inline_for_extraction
let cps_read_filter
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (r: cps_reader p1)
  (f2: (t1 -> GTot bool))
: Tot (cps_reader (parse_filter p1 f2))
= fun #va a pre t' post f ->
  let _ = elim_filter p1 f2 a in
  r a pre t' post (fun res ->
    let _ = intro_filter p1 f2 a in
    vpattern_rewrite (aparse (parse_filter p1 f2) a) va;
    f res
  )

inline_for_extraction
let read_filter
  (#k1: Ghost.erased parser_kind) #t1 (#p1: parser k1 t1) (r: leaf_reader p1)
  (f2: (t1 -> GTot bool))
: Tot (leaf_reader (parse_filter p1 f2))
= fun #va a ->
  let _ = elim_filter p1 f2 a in
  let res = r a in
  let va' = intro_filter p1 f2 a in
  rewrite (aparse (parse_filter p1 f2) a va') (aparse (parse_filter p1 f2) a va);
  return res

inline_for_extraction
let write_filter
  (#k: parser_kind)
  (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#p: parser k t)
  (#s: serializer p)
  (w: writer s)
  (f: (t -> GTot bool))
: Tot (writer (serialize_filter s f))
= fun x a ->
  let sz = w x a in
  let _ = gen_elim () in
  let _ = intro_filter p f a in
  return sz

inline_for_extraction
let exact_write_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: exact_writer s)
  (f: (t -> GTot bool))
: Tot (exact_writer (serialize_filter s f))
= fun x a ->
  let _ = w x a in
  intro_filter p f a

#push-options "--z3rlimit 32 --query_stats"
#restart-solver

inline_for_extraction
let validate_filter_and_then_with_cps_reader
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (p1': cps_reader p1)
  (f: (t1 -> GTot bool))
  (f' : ((x: t1) -> Tot (y: bool { y == f x } )))
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> validator (p2 x1)))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
: Tot (validator (parse_filter p1 f `and_then` p2))
= fun #va a len err ->
  and_then_eq (parse_filter p1 f) p2 (AP.contents_of' va);
  parse_filter_eq p1 f (AP.contents_of' va);
  let len1 = v1 a len err in
  let _ = gen_elim () in
  let verr = R.read err in
  if verr = 0ul
  then begin
    noop ();
    let a2 = peek_strong_with_size p1 a len1 in
    let _ = gen_elim () in
    unframe_cps_reader p1' a _ _ _ (fun x ->
      if not (f' x)
      then begin
        noop ();
        unpeek_strong a va a2;
        R.write err validator_error_constraint_failed;
        return len1
      end else begin
        noop ();
        let len2 = v2 x a2 (len `SZ.sub` len1) err in
        let _ = gen_elim () in
        unpeek_strong a va a2;
        let len' = len1 `SZ.add` len2 in
        noop ();
        return len'
      end
    )
  end else begin
    noop ();
    return len1
  end

inline_for_extraction
let validate_filter_and_then
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: validator p1)
  (p1': leaf_reader p1)
  (f: (t1 -> GTot bool))
  (f' : ((x: t1) -> Tot (y: bool { y == f x } )))
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> validator (p2 x1)))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
: Tot (validator (parse_filter p1 f `and_then` p2))
= validate_filter_and_then_with_cps_reader v1 (cps_reader_of_leaf_reader p1') f f' v2 u

#restart-solver

inline_for_extraction
let jump_filter_and_then_with_cps_reader
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (p1': cps_reader p1)
  (f: (t1 -> GTot bool))
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> jumper (p2 x1)))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
: Tot (jumper (parse_filter p1 f `and_then` p2))
= fun #va a ->
  and_then_eq (parse_filter p1 f) p2 (AP.contents_of' va);
  parse_filter_eq p1 f (AP.contents_of' va);
  let len1 = v1 a in
  let _ = gen_elim () in
  let a2 = peek_strong_with_size p1 a len1 in
  let _ = gen_elim () in
  let res = unframe_cps_reader p1' a _ _
    (fun res ->
      AP.arrayptr a va `star`
      pure (jumper_post (parse_filter p1 f `and_then` p2) va res)
    )
    (fun x ->
      let len2 = v2 x a2 in
      let _ = gen_elim () in
      unpeek_strong a va a2;
      return (len1 `SZ.add` len2)
    )
  in
  elim_pure _;
  return res

inline_for_extraction
let jump_filter_and_then
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (v1: jumper p1)
  (p1': leaf_reader p1)
  (f: (t1 -> GTot bool))
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> jumper (p2 x1)))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
: Tot (jumper (parse_filter p1 f `and_then` p2))
= jump_filter_and_then_with_cps_reader v1 (cps_reader_of_leaf_reader p1') f v2 u

[@@__reduce__]
let exists_and_then_payload0
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: (t1 -> parser k2 t2))
  (y: v (and_then_kind k1 k2) t2)
  (u1: AP.array byte)
  (tag: t1)
  (a1 a2: byte_array)
: Tot vprop
= exists_ (fun y2 ->
    aparse (p2 tag) a2 y2 `star`
    pure (
      AP.merge_into u1 (array_of' y2) (array_of' y) /\
      y.contents == y2.contents
    )
  )

let exists_and_then_payload
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: (t1 -> parser k2 t2))
  (y: v (and_then_kind k1 k2) t2)
  (u1: AP.array byte)
  (tag: t1)
  (a1 a2: byte_array)
: Tot vprop
= exists_and_then_payload0 p1 p2 y u1 tag a1 a2

let ghost_split_and_then
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: (t1 -> parser k2 t2))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
  (#va: _)
  (a1: byte_array)
: STGhostT (Ghost.erased byte_array) opened
    (aparse (p1 `and_then` p2) a1 va)
    (fun a2 -> exists_ (fun y1 -> aparse p1 a1 y1 `star` exists_and_then_payload p1 p2 va (array_of' y1) y1.contents a1 a2))
= let b = elim_aparse _ a1 in
  and_then_eq p1 p2 (AP.contents_of' b);
  let a2 = ghost_peek_strong p1 a1 in
  let _ = gen_elim () in
  let y1 = vpattern_replace (fun y1 -> aparse p1 a1 y1) in
  let _ = intro_aparse (p2 y1.contents) a2 in
  rewrite
    (exists_and_then_payload0 p1 p2 va (array_of' y1) y1.contents a1 a2)
    (exists_and_then_payload p1 p2 va (array_of' y1) y1.contents a1 a2);
  a2

inline_for_extraction
let split_and_then
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p2: (t1 -> parser k2 t2))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
  (#va: _)
  (a1: byte_array)
: STT byte_array
    (aparse (p1 `and_then` p2) a1 va)
    (fun a2 -> exists_ (fun y1 -> aparse p1 a1 y1 `star` exists_and_then_payload p1 p2 va (array_of' y1) y1.contents a1 a2))
= let ga2 = ghost_split_and_then p1 p2 u a1 in
  let _ = gen_elim () in
  let y1 = vpattern_replace (fun y1 -> aparse p1 a1 y1) in
  rewrite
    (exists_and_then_payload p1 p2 va (array_of' _) _ a1 ga2)
    (exists_and_then_payload0 p1 p2 va (array_of' y1) y1.contents a1 ga2);
  let _ = gen_elim () in
  let a2 = hop_aparse_aparse j1 (p2 y1.contents) a1 ga2 in
  rewrite
    (exists_and_then_payload0 p1 p2 va (array_of' y1) y1.contents a1 a2)
    (exists_and_then_payload p1 p2 va (array_of' y1) y1.contents a1 a2);
  return a2

let ghost_and_then_tag
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p2: (t1 -> parser k2 t2))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
  #y #y1 (a1: byte_array) (a2: byte_array)
: STGhostT (Ghost.erased t1) opened
    (aparse p1 a1 y1 `star` exists_and_then_payload p1 p2 y (array_of' y1) y1.contents a1 a2)
    (fun tag -> aparse p1 a1 y1 `star` exists_ (fun y2 -> aparse (p2 tag) a2 y2 `star` pure (
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y1.contents == Ghost.reveal tag /\
      y.contents == y2.contents
    )))
= let tag = Ghost.hide y1.contents in
  rewrite
    (exists_and_then_payload p1 p2 y (array_of' _) _ a1 a2)
    (exists_and_then_payload0 p1 p2 y (array_of' y1) (Ghost.reveal tag) a1 a2);
  let _ = gen_elim () in
  tag

inline_for_extraction
let read_and_then_tag
  (#opened: _)
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (rt: leaf_reader p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (p2: (t1 -> parser k2 t2))
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
  #y #y1 (a1: byte_array) (a2: byte_array)
: STT t1
    (aparse p1 a1 y1 `star` exists_and_then_payload p1 p2 y (array_of' y1) y1.contents a1 a2)
    (fun tag -> aparse p1 a1 y1 `star` exists_ (fun y2 -> aparse (p2 tag) a2 y2 `star` pure (
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y1.contents == tag /\
      y.contents == y2.contents
    )))
= let _ = ghost_and_then_tag p1 p2 u a1 a2 in
  let _ = gen_elim () in
  let tag = rt a1 in
  let _ = rewrite_aparse a2 (p2 tag) in
  return tag

let intro_and_then
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: (t1 -> parser k2 t2))
  (#k2': parser_kind)
  (p2': parser k2' t2)
  (u: squash (and_then_cases_injective p2 /\ k1.parser_kind_subkind == Some ParserStrong))
  #y1 #y2 (a1: byte_array) (a2: byte_array)
: STGhost (v (and_then_kind k1 k2) t2) opened
    (aparse p1 a1 y1 `star` aparse p2' a2 y2)
    (fun y -> aparse (and_then p1 p2) a1 y)
    (AP.adjacent (array_of' y1) (array_of' y2) /\
      (forall bytes . parse p2' bytes == parse (p2 y1.contents) bytes))
    (fun y ->
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y.contents == y2.contents
    )
= let va1 = elim_aparse _ a1 in
  let va2 = elim_aparse _ a2 in
  let va = AP.join a1 a2 in
  let _ = gen_elim () in
  and_then_eq p1 p2 (AP.contents_of' va);
  parse_strong_prefix p1 (AP.contents_of' va1) (AP.contents_of' va);
  assert (AP.contents_of' va2 `Seq.equal` Seq.slice (AP.contents_of' va) (AP.length (AP.array_of va1)) (AP.length (AP.array_of va)));
  intro_aparse (and_then p1 p2) a1

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
let validate_tagged_union_and_read_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#pt: parser kt tag_t)
  (vt: validate_and_read pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (validator (p t)))
: Pure (validator (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va a len err ->
    parse_tagged_union_eq pt tag_of_data p (AP.contents_of' va);
    vt a len
      (R.pts_to err full_perm 0ul)
      SZ.t
      (fun res -> AP.arrayptr a va `star` exists_ (fun v_err ->
        R.pts_to err full_perm v_err `star`
        pure (validator_prop (parse_tagged_union pt tag_of_data p) va v_err res)
      ))
      (fun s1 tag ar ->
        unpeek_strong a va ar;
        let ar = AP.split a s1 in
        let _ = gen_elim () in
        let len2 = len `SZ.sub` s1 in
        let s2 = v tag ar (len `SZ.sub` s1) err in
        let _ = gen_elim () in
        let _ = AP.join a ar in
        let len' = s1 `SZ.add` s2 in
        noop ();
        return len'
      )
      (fun e ->
        R.write err e;
        return 0sz
      )

inline_for_extraction
let validate_tagged_union_with_cps_reader
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#pt: parser kt tag_t)
  (vt: validator pt)
  (rt: cps_reader pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (validator (p t)))
: Pure (validator (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validate_tagged_union_and_read_tag (mk_validate_and_read vt rt) tag_of_data p v 

inline_for_extraction
let validate_tagged_union
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: validator pt)
  (rt: leaf_reader pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (validator (p t)))
: Pure (validator (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validate_tagged_union_with_cps_reader vt (cps_reader_of_leaf_reader rt) tag_of_data p v

inline_for_extraction
let jump_tagged_union_and_read_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#pt: parser kt tag_t)
  (vt: read_and_jump pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (jumper (p t)))
: Pure (jumper (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va a ->
    parse_tagged_union_eq pt tag_of_data p (AP.contents_of' va);
    let ar = ghost_peek_strong pt a in
    let _ = gen_elim () in
    let res = vt a (AP.arrayptr ar _) SZ.t
      (fun res ->
        AP.arrayptr a va `star`
        pure (jumper_post (parse_tagged_union pt tag_of_data p) va res)
      )
      (fun s1 tag ->
        unpeek_strong a va ar;
        let ar = AP.split a s1 in
        let _ = gen_elim () in
        let s2 = v tag ar in
        let _ = gen_elim () in
        let _ = AP.join a ar in
        return (s1 `SZ.add` s2)
      )
    in
    elim_pure _;
    return res

inline_for_extraction
let jump_tagged_union_with_cps_reader
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#pt: parser kt tag_t)
  (vt: jumper pt)
  (rt: cps_reader pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (jumper (p t)))
: Pure (jumper (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= jump_tagged_union_and_read_tag (mk_read_and_jump rt vt) tag_of_data p v

inline_for_extraction
let jump_tagged_union
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: jumper pt)
  (rt: leaf_reader pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (jumper (p t)))
: Pure (jumper (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= jump_tagged_union_with_cps_reader vt (cps_reader_of_leaf_reader rt) tag_of_data p v

#pop-options

#pop-options

[@@__reduce__]
let exists_tagged_union_payload0
  (kt: parser_kind)
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (y: v (and_then_kind kt k) data_t)
  (u1: AP.array byte)
  (tag: tag_t)
  (a1 a2: byte_array)
: Tot vprop
= exists_ (fun y2 ->
    aparse (p tag) a2 y2 `star`
    pure (
      AP.merge_into u1 (array_of' y2) (array_of' y) /\
      y.contents == y2.contents
    )
  )

let exists_tagged_union_payload
  (kt: parser_kind)
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (y: v (and_then_kind kt k) data_t)
  (u1: AP.array byte)
  (tag: tag_t)
  (a1 a2: byte_array)
: Tot vprop
= exists_tagged_union_payload0 kt tag_of_data p y u1 tag a1 a2

let ghost_split_tagged_union
  (#opened: _)
  (#kt: parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  #y (a1: byte_array)
: STGhost (Ghost.erased (byte_array)) opened
    (aparse (parse_tagged_union pt tag_of_data p) a1 y)
    (fun a2 -> exists_ (fun y1 -> aparse pt a1 y1 `star` exists_tagged_union_payload kt tag_of_data p y (array_of' y1) y1.contents a1 a2))
    (kt.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let b = elim_aparse _ a1 in
  parse_tagged_union_eq pt tag_of_data p (AP.contents_of' b);
  let a2 = ghost_peek_strong pt a1 in
  let _ = gen_elim () in
  let y1 = vpattern_replace (fun y1 -> aparse pt a1 y1) in
  let _ = intro_aparse (p y1.contents) a2 in
  rewrite
    (exists_tagged_union_payload0 kt tag_of_data p y (array_of' y1) y1.contents a1 a2)
    (exists_tagged_union_payload kt tag_of_data p y (array_of' y1) y1.contents a1 a2);
  a2

inline_for_extraction
let split_tagged_union
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (jt: jumper pt)
  (#data_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  #y (a1: byte_array)
: ST (byte_array)
    (aparse (parse_tagged_union pt tag_of_data p) a1 y)
    (fun a2 -> exists_ (fun y1 -> aparse pt a1 y1 `star` exists_tagged_union_payload kt tag_of_data p y (array_of' y1) y1.contents a1 a2))
    (kt.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let ga2 = ghost_split_tagged_union pt tag_of_data p a1 in
  let _ = gen_elim () in
  let y1 = vpattern_replace (fun y1 -> aparse pt a1 y1) in
  rewrite
    (exists_tagged_union_payload kt tag_of_data p y (array_of' _) _ a1 ga2)
    (exists_tagged_union_payload0 kt tag_of_data p y (array_of' y1) y1.contents a1 ga2);
  let _ = gen_elim () in
  let a2 = hop_aparse_aparse jt (p y1.contents) a1 ga2 in
  rewrite
    (exists_tagged_union_payload0 kt tag_of_data p y (array_of' y1) y1.contents a1 a2)
    (exists_tagged_union_payload kt tag_of_data p y (array_of' y1) y1.contents a1 a2);
  return a2

let ghost_tagged_union_tag
  (#opened: _)
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  #y #y1 (a1: byte_array) (a2: byte_array)
: STGhostT (Ghost.erased tag_t) opened
    (aparse pt a1 y1 `star` exists_tagged_union_payload kt tag_of_data p y (array_of' y1) y1.contents a1 a2)
    (fun tag -> aparse pt a1 y1 `star` exists_ (fun y2 -> aparse (p tag) a2 y2 `star` pure (
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y1.contents == Ghost.reveal tag /\
      (y.contents <: data_t) == y2.contents
    )))
= let tag = Ghost.hide y1.contents in
  rewrite
    (exists_tagged_union_payload kt tag_of_data p y (array_of' _) _ a1 a2)
    (exists_tagged_union_payload0 kt tag_of_data p y (array_of' y1) (Ghost.reveal tag) a1 a2);
  let _ = gen_elim () in
  tag

inline_for_extraction
let read_tagged_union_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (rt: leaf_reader pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  #y #y1 (a1: byte_array) (a2: byte_array)
: STT tag_t
    (aparse pt a1 y1 `star` exists_tagged_union_payload kt tag_of_data p y (array_of' y1) y1.contents a1 a2)
    (fun tag -> aparse pt a1 y1 `star` exists_ (fun y2 -> aparse (p tag) a2 y2 `star` pure (
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y1.contents == tag /\
      (y.contents <: data_t) == y2.contents
    )))
= let _ = ghost_tagged_union_tag pt tag_of_data p a1 a2 in
  let _ = gen_elim () in
  let tag = rt a1 in
  let _ = rewrite_aparse a2 (p tag) in
  return tag

let intro_tagged_union
  (#opened: _)
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  #y1 #k2 #t2 (#p2: parser k2 t2) (#y2: v k2 t2) (a1: byte_array) (a2: byte_array)
: STGhost (v (and_then_kind kt k) data_t) opened
    (aparse pt a1 y1 `star` aparse p2 a2 y2)
    (fun y -> aparse (parse_tagged_union pt tag_of_data p) a1 y)
    (kt.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' y1) (array_of' y2) /\
      t2 == refine_with_tag tag_of_data y1.contents /\
      (forall bytes . parse p2 bytes == parse (p y1.contents) bytes))
    (fun y ->
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      t2 == refine_with_tag tag_of_data y1.contents /\
      y.contents == (coerce (refine_with_tag tag_of_data y1.contents) y2.contents <: data_t)
    )
=
  let va1 = elim_aparse pt a1 in
  let va2 = elim_aparse p2 a2 in
  let va = AP.join a1 a2 in
  let _ = gen_elim () in
  parse_tagged_union_eq pt tag_of_data p (AP.contents_of' va);
  parse_strong_prefix pt (AP.contents_of' va1) (AP.contents_of' va);
  assert (AP.contents_of' va2 `Seq.equal` Seq.slice (AP.contents_of' va) (AP.length (AP.array_of va1)) (AP.length (AP.array_of va)));
  intro_aparse (parse_tagged_union pt tag_of_data p) a1

inline_for_extraction
let validate_and_read_tagged_union
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#pt: parser kt tag_t)
  (vt: validate_and_read pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (validate_and_read (p t)))
: Pure (validate_and_read (parse_tagged_union pt tag_of_data p))
    (requires (
      kt.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_subkind == Some ParserStrong
    ))
    (ensures (fun _ -> True))
= fun #va a len pre t' post fsuccess ffailure ->
    parse_tagged_union_eq pt tag_of_data p (AP.contents_of' va);
    vt a len pre t' post
      (fun s1 tag #vr ar ->
        let ar = hop_aparse_arrayptr_with_size _ a s1 ar in
        let len2 = len `SZ.sub` s1 in
        v tag ar len2 (aparse _ a _ `star` pre) t' post
          (fun s2 pl ar' ->
            let _ = intro_tagged_union pt tag_of_data p a ar in
            let vl = elim_aparse (parse_tagged_union pt tag_of_data p) a in
            let _ = intro_aparse (parse_tagged_union pt tag_of_data p) a in
            parse_injective (parse_tagged_union pt tag_of_data p) (AP.contents_of' va) (AP.contents_of' vl);
            let len = s1 `SZ.add` s2 in
            fsuccess len pl ar'
          )
          (fun e ->
            unpeek_strong a va ar;
            ffailure e
          )
      )
      (fun e ->
        ffailure e
      )

inline_for_extraction
let read_and_jump_tagged_union
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#pt: parser kt tag_t)
  (vt: read_and_jump pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: Ghost.erased parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (v: (t: tag_t) -> Tot (read_and_jump (p t)))
: Pure (read_and_jump (parse_tagged_union pt tag_of_data p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va a pre t' post f ->
    let ar = ghost_split_tagged_union pt tag_of_data p a in
    let _ = gen_elim () in
    let _ = ghost_tagged_union_tag pt tag_of_data p a ar in
    let _ = gen_elim () in
    vt a (aparse _ ar _ `star` pre) t' post (fun lenl tag ->
      let ar = hop_aparse_aparse_with_size _ _ a lenl ar in
      let _ = rewrite_aparse ar (p tag) in
      v tag ar (aparse _ a _ `star` pre) t' post (fun lenr pl ->
        let _ = intro_tagged_union pt tag_of_data p a ar in
        let len = lenl `SZ.add` lenr in
        f len pl
    ))

inline_for_extraction
let validate_dtuple2_and_read_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: validate_and_read pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (validator (p t)))
: Pure (validator (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validate_tagged_union_and_read_tag
    vt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> validate_synth (v x) (synth_dtuple2 x) ())

inline_for_extraction
let validate_dtuple2_with_cps_reader
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: validator pt)
  (rt: cps_reader pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (validator (p t)))
: Pure (validator (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validate_tagged_union_with_cps_reader
    vt
    rt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> validate_synth (v x) (synth_dtuple2 x) ())

inline_for_extraction
let validate_dtuple2
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: validator pt)
  (rt: leaf_reader pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (validator (p t)))
: Pure (validator (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= validate_tagged_union
    vt
    rt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> validate_synth (v x) (synth_dtuple2 x) ())

inline_for_extraction
let jump_dtuple2_and_read_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: read_and_jump pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (jumper (p t)))
: Pure (jumper (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= jump_tagged_union_and_read_tag
    vt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> jump_synth (v x) (synth_dtuple2 x) ())

inline_for_extraction
let jump_dtuple2_with_cps_reader
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: jumper pt)
  (rt: cps_reader pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (jumper (p t)))
: Pure (jumper (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= jump_tagged_union_with_cps_reader
    vt
    rt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> jump_synth (v x) (synth_dtuple2 x) ())

inline_for_extraction
let jump_dtuple2
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: jumper pt)
  (rt: leaf_reader pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (jumper (p t)))
: Pure (jumper (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= jump_tagged_union
    vt
    rt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> jump_synth (v x) (synth_dtuple2 x) ())

[@@__reduce__]
let exists_dtuple2_payload0
  (kt: parser_kind)
  (#tag_t: Type)
  (#k: parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (y: v (and_then_kind kt k) (dtuple2 tag_t data_t))
  (u1: AP.array byte)
  (tag: tag_t)
  (a1 a2: byte_array)
: Tot vprop
= exists_tagged_union_payload kt dfst (fun x -> parse_synth (p x) (synth_dtuple2 x)) y u1 tag a1 a2

let exists_dtuple2_payload
  (kt: parser_kind)
  (#tag_t: Type)
  (#k: parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (y: v (and_then_kind kt k) (dtuple2 tag_t data_t))
  (u1: AP.array byte)
  (tag: tag_t)
  (a1 a2: byte_array)
: Tot vprop
= exists_dtuple2_payload0 kt p y u1 tag a1 a2

inline_for_extraction
let ghost_split_dtuple2
  (#opened: _)
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#k: parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  #y (a1: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse (parse_dtuple2 pt p) a1 y)
    (fun a2 -> exists_ (fun y1 -> aparse pt a1 y1 `star` exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2))
    (kt.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let a2 = ghost_split_tagged_union pt _ _ a1 in
  let _ = gen_elim () in
  let y1 = vpattern_replace (fun y1 -> aparse pt a1 y1) in
  rewrite
    (exists_dtuple2_payload0 kt p y _ _ a1 a2)
    (exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2);
  a2

inline_for_extraction
let hop_dtuple2_tag_with_size
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  #y #y1 (a1: byte_array) (sz1: SZ.t) (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse pt a1 y1 `star` exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2)
    (fun a2' -> aparse pt a1 y1 `star` exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2')
    (kt.parser_kind_subkind == Some ParserStrong /\
      SZ.v sz1 == AP.length (array_of' y1))
    (fun _ -> True)
= assert (
    (exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2) ==
    (exists_tagged_union_payload0 kt dfst (fun x -> parse_synth (p x) (synth_dtuple2 x)) y (array_of' y1) y1.contents a1 a2)
  ) by (FStar.Tactics.trefl ());
  rewrite
    (exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2)
    (exists_tagged_union_payload0 kt dfst (fun x -> parse_synth (p x) (synth_dtuple2 x)) y (array_of' y1) y1.contents a1 a2);
  let _ = gen_elim () in
  let a2' = hop_aparse_aparse_with_size _ _ a1 sz1 a2 in
  rewrite
    (exists_tagged_union_payload0 kt dfst (fun x -> parse_synth (p x) (synth_dtuple2 x)) y (array_of' y1) y1.contents a1 a2')
    (exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2');
  return a2'

inline_for_extraction
let split_dtuple2
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: jumper pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  #y (a1: byte_array)
: ST (byte_array)
    (aparse (parse_dtuple2 pt p) a1 y)
    (fun a2 -> exists_ (fun y1 -> aparse pt a1 y1 `star` exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2))
    (kt.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let _ = ghost_split_dtuple2 _ _ _ in
  let _ = gen_elim () in
  let sz1 = get_parsed_size vt _ in
  let a2 = hop_dtuple2_tag_with_size _ _ _ sz1 _ in
  return a2

let ghost_dtuple2_tag
  (#opened: _)
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#k: parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  #y #y1 (a1: byte_array) (a2: byte_array)
: STGhostT (Ghost.erased tag_t) opened
    (aparse pt a1 y1 `star` exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2)
    (fun tag -> aparse pt a1 y1 `star` exists_ (fun y2 -> aparse (p tag) a2 y2 `star` pure (
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y1.contents == Ghost.reveal tag /\
      y.contents == (| Ghost.reveal tag, y2.contents |)
    )))
=
  rewrite
    (exists_dtuple2_payload kt p y _ _ a1 a2)
    (exists_dtuple2_payload0 kt p y (array_of' y1) y1.contents a1 a2);
  let gtag = ghost_tagged_union_tag _ _ _ a1 a2 in
  let tag = Ghost.reveal gtag in // "GHOST and STGhostBase cannot be composed", so I need an explicit bind here
  let _ = gen_elim () in
  let _ = rewrite_aparse a2 (parse_synth (p tag) (synth_dtuple2 tag)) in
  let _ = elim_synth _ _ a2 () in
  let _ = rewrite_aparse a2 (p gtag) in
  gtag

inline_for_extraction
let read_dtuple2_tag
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (rt: leaf_reader pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  #y #y1 (a1: byte_array) (a2: Ghost.erased byte_array)
: STT tag_t
    (aparse pt a1 y1 `star` exists_dtuple2_payload kt p y (array_of' y1) y1.contents a1 a2)
    (fun tag -> aparse pt a1 y1 `star` exists_ (fun y2 -> aparse (p tag) a2 y2 `star` pure (
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      y1.contents == tag /\
      y.contents == (| tag, y2.contents |)
    )))
= let _ = ghost_dtuple2_tag pt p a1 a2 in
  let _ = gen_elim () in
  let tag = rt a1 in
  let _ = rewrite_aparse a2 (p tag) in
  return tag

let intro_dtuple2
  (#opened: _)
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#k: parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  #y1 #k2 #t2 (#p2: parser k2 t2) (#y2: v k2 t2) (a1: byte_array) (a2: byte_array)
: STGhost (v (and_then_kind kt k) (dtuple2 tag_t data_t)) opened
    (aparse pt a1 y1 `star` aparse p2 a2 y2)
    (fun y -> aparse (parse_dtuple2 pt p) a1 y)
    (kt.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' y1) (array_of' y2) /\
      t2 == data_t y1.contents /\
      (forall bytes . parse p2 bytes == parse (p y1.contents) bytes))
    (fun y ->
      AP.merge_into (array_of' y1) (array_of' y2) (array_of' y) /\
      t2 == data_t y1.contents /\
      y.contents == (| y1.contents, y2.contents |)
    )
= let tag = y1.contents in // "GHOST and STGhostBase cannot be composed", so I need an explicit bind here, same as above
  let _ = rewrite_aparse a2 (p tag) in
  let _ = intro_synth (p tag) (synth_dtuple2 tag) a2 () in
  let _ = intro_tagged_union pt dfst (fun x -> parse_synth (p x) (synth_dtuple2 x)) a1 a2 in
  rewrite_aparse a1 (parse_dtuple2 pt p)

inline_for_extraction
let validate_and_read_dtuple2
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: validate_and_read pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (validate_and_read (p t)))
: Pure (validate_and_read (parse_dtuple2 pt p))
    (requires (
      kt.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_subkind == Some ParserStrong
    ))
    (ensures (fun _ -> True))
= validate_and_read_tagged_union
    vt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> 
      validate_and_read_synth
        (v x)
        (synth_dtuple2 x)
        (fun x' pre t post phi -> phi (synth_dtuple2 x x'))
        ()
    )

inline_for_extraction
let read_and_jump_dtuple2
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (vt: read_and_jump pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (read_and_jump (p t)))
: Pure (read_and_jump (parse_dtuple2 pt p))
    (requires (
      kt.parser_kind_subkind == Some ParserStrong
    ))
    (ensures (fun _ -> True))
= read_and_jump_tagged_union
    vt
    dfst
    (fun x -> parse_synth (p x) (synth_dtuple2 x))
    (fun x -> 
      read_and_jump_synth
        (v x)
        (synth_dtuple2 x)
        (fun x' pre t post phi -> phi (synth_dtuple2 x x'))
        ()
    )

inline_for_extraction
let cps_read_dtuple2
  (#kt: Ghost.erased parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (rt: cps_reader pt)
  (j: jumper pt)
  (#k: Ghost.erased parser_kind)
  (#data_t: tag_t -> Type)
  (p: (t: tag_t) -> Tot (parser k (data_t t)))
  (v: (t: tag_t) -> Tot (cps_reader (p t)))
: Pure (cps_reader (parse_dtuple2 pt p))
    (requires (kt.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun #va a pre t post phi ->
    let ar = split_dtuple2 j p a in
    let _ = gen_elim () in
    let _ = ghost_dtuple2_tag pt p a ar in
    let _ = gen_elim () in
    unframe_cps_reader rt a _ _ _ (fun tag ->
      let _ = rewrite_aparse ar (p tag) in
      unframe_cps_reader (v tag) ar _ _ _ (fun v ->
        let _ = intro_dtuple2 pt p a ar in
        vpattern_rewrite (aparse _ a) va;
        phi (| tag, v |)
      )
    )

let intro_parse_strict
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#vb: v k t)
  (b: byte_array)
: STGhost (v k (parser_range p)) opened
    (aparse p b vb)
    (fun vb' -> aparse (parse_strict p) b vb')
    True
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      vb.contents == vb'.contents
    )
= let _ = elim_aparse p b in
  intro_aparse (parse_strict p) b

let elim_parse_strict
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#vb: v k (parser_range p))
  (b: byte_array)
: STGhost (v k t) opened
    (aparse (parse_strict p) b vb)
    (fun vb' -> aparse p b vb')
    True
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      vb'.contents == vb.contents
    )
= let _ = elim_aparse (parse_strict p) b in
  intro_aparse p b

inline_for_extraction
let validate_strict
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (w: validator p)
: Tot (validator (parse_strict p))
= rewrite_validator w _

inline_for_extraction
let jump_strict
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (w: jumper p)
: Tot (jumper (parse_strict p))
= rewrite_jumper w _
