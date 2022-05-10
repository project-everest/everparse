module LowParse.SteelST.Access
include LowParse.SteelST.Parse

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt

open Steel.ST.Util

let jumper
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (#va: AP.v byte) ->
  (a: byte_array) ->
  ST SZ.size_t
    (AP.arrayptr a va)
    (fun res -> AP.arrayptr a va)
    (Some? (parse p (AP.contents_of va)))
    (fun res -> 
      match parse p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) ->
        SZ.size_v res == consumed
)

let hop_arrayptr_aparse
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a1: byte_array)
  (sz: SZ.size_t)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (AP.arrayptr a1 va1 `star` aparse p a2 va2)
    (fun res -> AP.arrayptr a1 va1 `star` aparse p res va2)
    (AP.adjacent (AP.array_of va1) (array_of va2) /\ SZ.size_v sz == AP.length (AP.array_of va1))
    (fun res -> res == Ghost.reveal a2)
= let _ = elim_aparse p a2 in
  let res = AP.split' a1 sz a2 in
  let _ = gen_elim () in
  let va2' = intro_aparse p res in
  rewrite (aparse p res va2') (aparse p res va2);
  return res

let hop_aparse_arrayptr
  (#k: parser_kind)
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
= let _ = elim_aparse p a1 in
  let sz = j a1 in
  let res = AP.split' a1 sz a2 in
  let _ = gen_elim () in
  let va1' = intro_aparse p a1 in
  rewrite (aparse p a1 va1') (aparse p a1 va1);
  return res

let hop_aparse_aparse
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: _)
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

let jump_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (jumper p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      SZ.size_v sz == k.parser_kind_low
    ))
    (ensures (fun _ -> True))
=
  fun #va a ->
  parser_kind_prop_equiv k p;
  noop ();
  return sz

let get_parsed_size
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#vp: v k t)
  (j: jumper p)
  (a: byte_array)
: ST SZ.size_t
    (aparse p a vp)
    (fun res -> aparse p a vp)
    True
    (fun res -> SZ.size_v res == AP.length (array_of vp))
=
  let _ = elim_aparse p a in
  let res = j a in
  let _ = intro_aparse p a in
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
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    )) )  )
    (k.parser_kind_subkind == Some ParserStrong /\
    Some? (parse' p (AP.contents_of' va))
    )
    (fun _ -> True)
=
  let sz = SZ.int_to_size_t (snd (Some?.v (parse' p (AP.contents_of' va))) <: nat) in
  parse_strong_prefix p (AP.contents_of' va) (AP.seq_slice (AP.contents_of' va) 0 (SZ.size_v sz));
  let res = AP.gsplit a sz in
  let _ = gen_elim () in
  let _ = intro_aparse p a in
  res

let peek_strong_with_size
  (#k: parser_kind)
  (#t: Type)
  (#va: AP.v byte)
  (p: parser k t)
  (a: byte_array)
  (sz: SZ.size_t)
: ST (byte_array)
    (AP.arrayptr a va)
    (fun res -> exists_ (fun vp -> aparse p a vp `star` exists_ (fun vres -> AP.arrayptr res vres `star` pure (
      let consumed = AP.length (array_of vp) in
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      consumed == SZ.size_v sz /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va)) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      parse' p (AP.seq_slice (AP.contents_of' va) 0 consumed) == Some (vp.contents, consumed)
    )) )  )
    (k.parser_kind_subkind == Some ParserStrong /\
      begin match parse' p (AP.contents_of' va) with
      | None -> False
      | Some (_, consumed) -> (consumed <: nat) == SZ.size_v sz
      end
    )
    (fun _ -> True)
= let gres = ghost_peek_strong p a in
  let _ = gen_elim () in
  let _ = elim_aparse _ a in
  let res = AP.split' a sz gres in
  let _ = intro_aparse _ a in
  return res

let peek_strong
  (#k: parser_kind)
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
    (
      let consumed = AP.length (array_of vp) in
      k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of vp) (AP.array_of vres) (AP.array_of va) /\
      consumed <= AP.length (AP.array_of va) /\
      parse' p (AP.contents_of' va) == Some (vp.contents, consumed) /\
      AP.contents_of' vres == AP.seq_slice (AP.contents_of' va) consumed (AP.length (AP.array_of va))
    )
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
