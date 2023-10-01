module LowParse.SteelST.Access
include LowParse.SteelST.Parse

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.GenElim

let jumper_post
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va: AP.v byte)
  (res: SZ.t)
: GTot prop
=
      match parse p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) ->
        SZ.v res == consumed

inline_for_extraction
let jumper
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (#va: AP.v byte) ->
  (a: byte_array) ->
  ST SZ.t
    (AP.arrayptr a va)
    (fun res -> AP.arrayptr a va)
    (Some? (parse p (AP.contents_of va)))
    (fun res -> jumper_post p va res)

inline_for_extraction
let ifthenelse_jump
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (cond: bool)
  (vtrue: (squash (cond == true) -> Tot (jumper p)))
  (vfalse: (squash (cond == false) -> Tot (jumper p)))
: Tot (jumper p)
= fun a ->
  if cond
  then vtrue () a
  else vfalse () a

inline_for_extraction
let hop_arrayptr_aparse
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (sz: SZ.t)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (AP.arrayptr a1 va1 `star` aparse p a2 va2)
    (fun res -> AP.arrayptr a1 va1 `star` aparse p res va2)
    (AP.adjacent (AP.array_of va1) (array_of va2) /\ SZ.v sz == AP.length (AP.array_of va1))
    (fun res -> res == Ghost.reveal a2)
= let _ = elim_aparse p a2 in
  let res = AP.split' a1 sz a2 in
  let _ = gen_elim () in
  let va2' = intro_aparse p res in
  rewrite (aparse p res va2') (aparse p res va2);
  return res

inline_for_extraction
let hop_aparse_arrayptr_with_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (sz: SZ.t)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p a1 va1 `star` AP.arrayptr a2 va2)
    (fun res -> aparse p a1 va1 `star` AP.arrayptr res va2)
    (AP.adjacent (array_of va1) (AP.array_of va2) /\
      SZ.v sz == AP.length (array_of va1))
    (fun res -> res == Ghost.reveal a2)
= let _ = elim_aparse p a1 in
  let res = AP.split' a1 sz a2 in
  let _ = gen_elim () in
  let va1' = intro_aparse p a1 in
  rewrite (aparse p a1 va1') (aparse p a1 va1);
  return res

inline_for_extraction
let hop_aparse_aparse_with_size
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#t2: _)
  (p2: parser k2 t2)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (sz: SZ.t)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p1 a1 va1 `star` aparse p2 a2 va2)
    (fun res -> aparse p1 a1 va1 `star` aparse p2 res va2)
    (AP.adjacent (array_of va1) (array_of va2) /\
      SZ.v sz == AP.length (array_of va1))
    (fun res -> res == Ghost.reveal a2)
= let _ = elim_aparse p2 a2 in
  let res = hop_aparse_arrayptr_with_size p1 a1 sz a2 in
  let va2' = intro_aparse p2 res in
  rewrite (aparse p2 res va2') (aparse p2 res va2);
  return res

inline_for_extraction
let jump_constant_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.t)
: Pure (jumper p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      SZ.v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun #va a ->
  parser_kind_prop_equiv k p;
  noop ();
  return sz

inline_for_extraction
let get_parsed_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v k t)
  (j: jumper p)
  (a: byte_array)
: ST SZ.t
    (aparse p a vp)
    (fun res -> aparse p a vp)
    True
    (fun res -> SZ.v res == AP.length (array_of vp))
=
  let _ = elim_aparse p a in
  let res = j a in
  let _ = intro_aparse p a in
  return res

inline_for_extraction
let hop_aparse_arrayptr
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p a1 va1 `star` AP.arrayptr a2 va2)
    (fun res -> aparse p a1 va1 `star` AP.arrayptr res va2)
    (AP.adjacent (array_of va1) (AP.array_of va2))
    (fun res -> res == Ghost.reveal a2)
= let sz = get_parsed_size j a1 in
  hop_aparse_arrayptr_with_size p a1 sz a2

inline_for_extraction
let hop_aparse_aparse
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: _)
  (p2: parser k2 t2)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p1 a1 va1 `star` aparse p2 a2 va2)
    (fun res -> aparse p1 a1 va1 `star` aparse p2 res va2)
    (AP.adjacent (array_of va1) (array_of va2))
    (fun res -> res == Ghost.reveal a2)
= let _ = elim_aparse p2 a2 in
  let res = hop_aparse_arrayptr j1 a1 a2 in
  let va2' = intro_aparse p2 res in
  rewrite (aparse p2 res va2') (aparse p2 res va2);
  return res

inline_for_extraction
let hop_aparse_aparse_with_implies
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: Ghost.erased parser_kind)
  (#t2: _)
  (p2: parser k2 t2)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p1 a1 va1 `star` aparse p2 a2 va2)
    (fun res -> aparse p1 a1 va1 `star` aparse p2 res va2 `star` (aparse p2 res va2 `implies_` aparse p2 a2 va2))
    (AP.adjacent (array_of va1) (array_of va2))
    (fun res -> res == Ghost.reveal a2)
= let res = hop_aparse_aparse j1 p2 a1 a2 in
  intro_implies
    (aparse p2 res va2)
    (aparse p2 a2 va2)
    emp
    (fun _ -> vpattern_rewrite (fun res -> aparse _ res _) a2);
  return res

let parse'
  (#a: Type)
  (#k: parser_kind)
  (p: parser k a)
  (b: bytes)
: GTot (option (a & nat))
= match parse p b with
  | None -> None
  | Some (v, c) -> Some (v, c)

#set-options "--ide_id_info_off"

let ghost_peek_strong_post
  (#k: parser_kind)
  (#t: Type)
  (va: AP.v byte)
  (p: parser k t)
  (res: Ghost.erased byte_array)
  (vp: v k t)
  (vres: AP.v byte)
: GTot prop
=
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)

let ghost_peek_strong
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#va: AP.v byte)
  (p: parser k t)
  (a: byte_array)
: STGhost (Ghost.erased (byte_array)) opened
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      ghost_peek_strong_post va p res vp vres
    )) )  )
    (k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse' p (AP.contents_of' va))
    )
    (fun _ -> True)
=
  let sz = SZ.uint_to_t (snd (Some?.v (parse' p (AP.contents_of' va))) <: nat) in
  parse_strong_prefix p (AP.contents_of' va) (AP.seq_slice (AP.contents_of' va) 0 (SZ.v sz));
  let res = AP.gsplit a sz in
  let _ = gen_elim () in
  let _ = intro_aparse p a in
  res

inline_for_extraction
let peek_strong_with_size
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (#va: AP.v byte)
  (p: parser k t)
  (a: byte_array)
  (sz: SZ.t)
: ST (byte_array)
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      consumed == SZ.v sz /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    )) )  )
    (k.parser_kind_subkind == Some ParserStrong /\
      begin match parse' p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) -> (consumed <: nat) == SZ.v sz
      end
    )
    (fun _ -> True)
= let gres = ghost_peek_strong p a in
  let _ = gen_elim () in
  let _ = elim_aparse _ a in
  let res = AP.split' a sz gres in
  let _ = intro_aparse _ a in
  return res

inline_for_extraction
let peek_strong
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#va: AP.v byte)
  (j: jumper p)
  (a: byte_array)
: ST (byte_array)
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    ))))
    (k.parser_kind_subkind == Some ParserStrong /\
      Some? (parse p (AP.contents_of' va)))
    (fun _ -> True)
=
  let sz = j a in
  let res = peek_strong_with_size p a sz in
  let _ = gen_elim () in
  return res

/// useful for validators, which need to roll back peek after reading some contents
let unpeek_strong'
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v k t)
  (#vres: AP.v byte)
  (a: byte_array)
  (res: byte_array)
: STGhost (AP.v byte) opened
    (aparse p a vp `star` AP.arrayptr res vres)
    (fun va -> AP.arrayptr a va)
    (AP.adjacent (array_of vp) (AP.array_of vres) /\
    k.parser_kind_subkind == Some ParserStrong)
    (fun va ->
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed)
    )
= let va' = elim_aparse p a in
  let va = AP.join a res in
  let consumed = AP.length (array_of vp) in
  assert (AP.contents_of' vres `Seq.equal` AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)));
  assert (AP.contents_of' va' `Seq.equal` AP.seq_slice (AP.contents_of' va) 0 consumed);
  parse_strong_prefix p (AP.contents_of' va') (AP.contents_of' va);
  noop ();
  va

let unpeek_strong_pre
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (vp: v k t)
  (vres: AP.v byte)
  (va: AP.v byte)
: GTot prop
=
      let consumed = AP.length (array_of vp) in
      k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va))

let unpeek_strong
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v k t)
  (#vres: AP.v byte)
  (a: byte_array)
  (va: AP.v byte)
  (res: byte_array)
: STGhost unit opened
    (aparse p a vp `star` AP.arrayptr res vres)
    (fun _ -> AP.arrayptr a va)
    (unpeek_strong_pre p vp vres va)
    (fun _ -> True)
= let va' = unpeek_strong' a res in
  parse_injective p (AP.contents_of' va) (AP.contents_of' va');
  Seq.lemma_split (AP.contents_of' va) (AP.length (array_of vp));
  Seq.lemma_split (AP.contents_of' va') (AP.length (array_of vp));
  rewrite
    (AP.arrayptr a va')
    (AP.arrayptr a va)

let peek_consumes_all
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: AP.v byte)
  (a: byte_array)
: STGhost (v k t) opened
    (AP.arrayptr a va)
    (fun vp -> aparse p a vp)
    (k.parser_kind_subkind == Some ParserConsumesAll /\
      Some? (parse p (AP.contents_of' va)))
    (fun vp ->
      array_of vp == AP.array_of va /\
      parse' p (AP.contents_of' va) == Some (vp.contents, AP.length (AP.array_of va))
    )
=
  parser_kind_prop_equiv k p;
  intro_aparse p a

inline_for_extraction
let leaf_reader
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (#va: _) ->
  (a: byte_array) ->
  ST t
    (aparse p a va)
    (fun _ -> aparse p a va)
    True
    (fun res -> res == va.contents)

inline_for_extraction
let ifthenelse_read
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (cond: bool)
  (iftrue: (squash (cond == true) -> Tot (leaf_reader p)))
  (iffalse: (squash (cond == false) -> Tot (leaf_reader p)))
: Tot (leaf_reader p)
= fun a ->
    if cond
    then iftrue () a
    else iffalse () a

inline_for_extraction
let cps_reader
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (#va: _) ->
  (a: byte_array) ->
  (pre: vprop) ->
  (t': Type) ->
  (post: (t' -> vprop)) ->
  (f: (
    (v: t) ->
    ST t'
      (aparse p a va `star` pre)
      post
      (v == va.contents)
      (fun _ -> True)
  )) ->
  STT t'
    (aparse p a va `star` pre)
    post

inline_for_extraction
let ifthenelse_cps_read
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (cond: bool)
  (iftrue: (squash (cond == true) -> Tot (cps_reader p)))
  (iffalse: (squash (cond == false) -> Tot (cps_reader p)))
: Tot (cps_reader p)
= fun a pre t post ->
    if cond
    then iftrue () a pre t post
    else iffalse () a pre t post

inline_for_extraction
let cps_reader_of_leaf_reader
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (r: leaf_reader p)
: Tot (cps_reader p)
= fun #va a pre t' post f ->
    let v = r #va a in
    f v

inline_for_extraction
let unframe_cps_reader
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (r: cps_reader p)
  (#va: _)
  (a: byte_array)
  (pre: vprop)
  (t': Type)
  (post: (t' -> vprop))
  (f: (
    (v: t) ->
    ST t'
      (aparse p a va `star` pre)
      post
      (v == va.contents)
      (fun _ -> True)
  ))
: STF t'
    (aparse p a va `star` pre)
    post
    True
    (fun _ -> True)
= r a pre t' post f

(* Accessors *)

include LowParse.CLens

inline_for_extraction
let accessor
  (#kfrom: parser_kind)
  (#tfrom: Type)
  (pfrom: parser kfrom tfrom)
  (#kto: parser_kind)
  (#tto: Type)
  (pto: parser kto tto)
  (l: clens tfrom tto)
: Tot Type
= (#va: v kfrom tfrom) ->
  (a: byte_array) ->
  (#kpre: vprop) ->
  (#tret: Type) ->
  (#kpost: (tret -> vprop)) ->
  (body: (
    (#va': v kfrom tfrom) ->
    (#vb': v kto tto) ->
    (b: byte_array) ->
    ST tret
      (kpre `star` aparse pfrom a va' `star` aparse pto b vb')
      (fun r -> kpost r `star` aparse pfrom a va' `star` aparse pto b vb')
      (va'.contents == va.contents /\
        l.clens_cond va.contents /\
        vb'.contents == l.clens_get va.contents)
      (fun _ -> True)
  )) ->
  STF tret
    (kpre `star` aparse pfrom a va)
    (fun r -> kpost r `star` aparse pfrom a va)
    (l.clens_cond va.contents)
    (fun _ -> True)

inline_for_extraction
let accessor_id
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (accessor p p (clens_id _))
= fun #vb b body ->
    let pi = AP.array_perm (array_of' vb) in
    let r = share_aparse p b (half_perm pi) (half_perm pi) in
    let res = body #(fstp r) b in
    let _ = gather_aparse p #(fstp r) b in
    rewrite (aparse p b _) (aparse p b vb);
    return res

inline_for_extraction
let accessor_compose
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (a12: accessor p1 p2 cl12)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#cl23: clens t2 t3)
  (a23: accessor p2 p3 cl23)
: Tot (accessor p1 p3 (clens_compose cl12 cl23))
= fun b1 body ->
  a12 b1 (fun b2 ->
    a23 b2 (fun b3 ->
      body b3
    )
  )

inline_for_extraction
let accessor_ext
  (#k1: Ghost.erased parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: Ghost.erased parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl12: clens t1 t2)
  (acc: accessor p1 p2 cl12)
  (cl12': clens t1 t2)
: Pure (accessor p1 p2 cl12')
    (clens_eq cl12 cl12')
    (fun _ -> True)
= acc
