module LowParse.SteelSel.Combinators
include LowParse.SteelSel.Validate
include LowParse.SteelSel.Access
include LowParse.Spec.Combinators

module S = Steel.Memory
module SE = Steel.SelEffect
module SEA = Steel.SelEffect.Atomic
module A = Steel.SelArray
module AP = Steel.SelArrayPtr

module U32 = FStar.UInt32
module U64 = FStar.UInt64

unfold
let uint64_to_uint32
  (r1: U64.t)
  (sq: squash (is_success r1))
: Tot U32.t
= uint64_to_uint32 r1

#push-options "--z3rlimit 16"
let validate_pair
  #k1 #t1 (#p1: parser k1 t1) (v1: wvalidator p1)
  #k2 #t2 (#p2: parser k2 t2) (v2: wvalidator p2)
: Pure (wvalidator (p1 `nondep_then` p2))
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= fun a len ->
  let ga : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  let g : Ghost.erased _ = ga.AP.contents in
  nondep_then_eq p1 p2 g;
  let r1 = v1 a len in
  if is_error r1
  then begin
    SEA.return r1
  end
  else begin
    let sq : squash (is_success r1) = () in // FIXME: WHY WHY WHY does refinement or requires not work?
    let consumed = uint64_to_uint32 r1 sq in
    Seq.lemma_split g (U32.v consumed);
    let a2 = AP.split a consumed in
    SEA.reveal_star (AP.varrayptr a) (AP.varrayptr a2); // FIXME: WHY WHY WHY is this needed?
    let ga1 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
    let g1 : Ghost.erased _ = ga1.AP.contents in
    parse_strong_prefix p1 g1 g;
    let len2 = len `U32.sub` consumed in
    let r2 = v2 a2 len2 in
    AP.join a a2;
    if is_error r2
    then SEA.return r2
    else begin
      let res = r1 `U64.add` r2 in
      parse_strong_prefix p1 g (Seq.slice g 0 (U64.v res));
      nondep_then_eq p1 p2 (Seq.slice g 0 (U64.v res));
      SEA.return res
    end
  end
#pop-options

val destruct_pair
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: strong_parsed_size p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (a: byte_array)
: SE.SteelSel byte_array
    (vparse (p1 `nondep_then` p2) a)
    (fun res -> vparse p1 a `SE.star` vparse p2 res)
    (fun _ ->
      k1.parser_kind_subkind == Some ParserStrong
    )
    (fun h res h' ->
      let c = h (vparse (p1 `nondep_then` p2) a) in
      let c1 = h' (vparse p1 a) in
      let c2 = h' (vparse p2 res) in
      A.merge_into c1.array c2.array c.array /\
      c.contents == (c1.contents, c2.contents)
    )

let destruct_pair
  #k1 #t1 #p1 j1 p2 a
=
  elim_vparse (p1 `nondep_then` p2) a;
  let b : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  nondep_then_eq p1 p2 b.AP.contents;
  let res = peek_strong j1 a in
  SEA.reveal_star (vparse p1 a) (AP.varrayptr res);
  let c1 : Ghost.erased (v t1) = SEA.gget (vparse p1 a) in
  parse_strong_prefix p1 (Seq.slice b.AP.contents 0 (A.length c1.array)) b.AP.contents;
  intro_vparse p2 res;
  SEA.return res
