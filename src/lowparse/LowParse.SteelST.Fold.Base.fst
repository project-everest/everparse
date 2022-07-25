module LowParse.SteelST.Fold.Base

open Steel.ST.GenElim

[@@erasable]
noeq
type chunk_desc
= {
    chunk_p: bytes -> prop;
    chunk_len: (input: bytes) -> Ghost nat (requires (chunk_p input)) (ensures (fun res -> res <= Seq.length input));
    chunk_prefix: (input: bytes) -> (prefix: nat) -> Lemma
      (requires (
        chunk_p input /\
        chunk_len input <= prefix /\
        prefix <= Seq.length input
      ))
      (ensures (
        chunk_p (Seq.slice input 0 prefix) /\
        chunk_len (Seq.slice input 0 prefix) == chunk_len input
      ));
    chunk_append: (input: bytes) -> (input': bytes) -> Lemma
      (requires (
        chunk_p input
      ))
      (ensures (
        chunk_p (input `Seq.append` input') /\
        chunk_len (input `Seq.append` input') == chunk_len input
      ));
  }

let chunk_desc_is_empty
  (c: chunk_desc)
: Tot prop
= c.chunk_p Seq.empty

let parse_chunk
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (input: bytes)
  (chunk: nat)
: Tot prop
= chunk <= Seq.length input /\ parse p (Seq.slice input 0 chunk) == Some (v, chunk)

let parse_chunk_unique
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (input: bytes)
  (chunk1 chunk2: nat)
: Lemma
  (requires (
    parse_chunk p v input chunk1 /\
    parse_chunk p v input chunk2
  ))
  (ensures (chunk1 == chunk2))
  [SMTPat (parse_chunk p v input chunk1); SMTPat (parse_chunk p v input chunk2)]
= parse_injective p (Seq.slice input 0 chunk1) (Seq.slice input 0 chunk2)

let parse_some_chunk_f
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (input: bytes)
: Tot prop
= exists (chunk: nat) . parse_chunk p v input chunk

let get_chunk_length_f
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (input: bytes)
: Ghost nat
    (requires parse_some_chunk_f p v input)
    (ensures (fun chunk -> parse_chunk p v input chunk))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (parse_chunk p v input)

let parse_some_chunk
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
: Tot chunk_desc
= {
    chunk_p = parse_some_chunk_f p v;
    chunk_len = get_chunk_length_f p v;
    chunk_prefix = begin fun input prefix ->
      let cl = get_chunk_length_f p v input in
      let input' = Seq.slice input 0 prefix in
      assert (parse_chunk p v input' cl)
    end;
    chunk_append = begin fun input input' ->
      let cl = get_chunk_length_f p v input in
      assert (Seq.slice (input `Seq.append` input') 0 cl `Seq.equal` Seq.slice input 0 cl);
      assert (parse_chunk p v (input `Seq.append` input') cl)      
    end;
  }

let concat_chunks_p
  (f1 f2: chunk_desc)
  (input: bytes)
: Tot prop
= f1.chunk_p input /\
  f2.chunk_p (Seq.slice input (f1.chunk_len input) (Seq.length input))

let concat_chunks_len
  (f1 f2: chunk_desc)
  (input: bytes)
: Ghost nat
    (requires (concat_chunks_p f1 f2 input))
    (ensures (fun res -> res <= Seq.length input))
= let cl = f1.chunk_len input in
  cl + f2.chunk_len (Seq.slice input cl (Seq.length input))

let concat_chunks
  (f1 f2: chunk_desc)
: Tot chunk_desc
= {
    chunk_p = concat_chunks_p f1 f2;
    chunk_len = concat_chunks_len f1 f2;
    chunk_prefix = begin fun input prefix ->
      f1.chunk_prefix input prefix;
      let cl = f1.chunk_len input in
      assert (Seq.slice (Seq.slice input cl (Seq.length input)) 0 (prefix - cl) `Seq.equal` Seq.slice (Seq.slice input 0 prefix) cl (Seq.length (Seq.slice input 0 prefix)));
      f2.chunk_prefix (Seq.slice input cl (Seq.length input)) (prefix - cl)
    end;
    chunk_append = begin fun input input' ->
      f1.chunk_append input input';
      let cl = f1.chunk_len input in
      assert ((Seq.slice input cl (Seq.length input) `Seq.append` input') `Seq.equal` Seq.slice (input `Seq.append` input') cl (Seq.length (input `Seq.append` input')));
      f2.chunk_append (Seq.slice input cl (Seq.length input)) input'
    end;
  }

let exact_chunk
  (f: chunk_desc)
  (input: bytes)
: Tot prop
= f.chunk_p input /\
  f.chunk_len input == Seq.length input

let exact_chunk_parse_some_chunk'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (b: bytes)
: Lemma
  (requires (parse p b == Some (v, Seq.length b)))
  (ensures (exact_chunk (parse_some_chunk p v) b))
= assert (parse_chunk p v b (Seq.length b))

let exact_chunk_parse_some_chunk
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (b: bytes)
: Lemma
  (parse p b == Some (v, Seq.length b) <==> exact_chunk (parse_some_chunk p v) b)
= Classical.move_requires (exact_chunk_parse_some_chunk' p v) b

let exact_chunk_empty f = ()

let exact_chunk_empty_unique f input =
  Seq.append_empty_l input;
  f.chunk_append Seq.empty input;
  assert (exact_chunk f input ==> input `Seq.equal` Seq.empty)

let exact_chunk_concat_chunks_intro
  (f12 f23: chunk_desc)
  (input12 input23: bytes)
: Lemma
  (requires (
    exact_chunk f12 input12 /\
    exact_chunk f23 input23
  ))
  (ensures (
    exact_chunk (f12 `concat_chunks` f23) (input12 `Seq.append` input23)
  ))
= f12.chunk_append input12 input23;
  assert (Seq.slice (input12 `Seq.append` input23) (Seq.length input12) (Seq.length (input12 `Seq.append` input23)) `Seq.equal` input23)

let exact_chunk_intro
  (f: chunk_desc)
  (input: bytes)
: Lemma
  (requires (f.chunk_p input))
  (ensures (exact_chunk f (Seq.slice input 0 (f.chunk_len input))))
= f.chunk_prefix input (f.chunk_len input)

let exact_chunk_concat_chunks_elim
  f12 f23 input
=
  exact_chunk_intro f12 input;
  let cl = f12.chunk_len input in
  Seq.lemma_split input cl;
  Seq.split input cl

let array_chunk_prop
  (f: chunk_desc)
  (a: byte_array)
  (va: AP.array byte)
  (va0: AP.v byte)
: Tot prop
=
    va == AP.array_of va0 /\
    exact_chunk f (AP.contents_of' va0)

[@@__reduce__]
let array_chunk'
  (f: chunk_desc)
  (a: byte_array)
  (va: AP.array byte)
: Tot vprop
= exists_ (fun va0 -> AP.arrayptr a va0 `star` pure (array_chunk_prop f a va va0))

let array_chunk
  (f: chunk_desc)
  (a: byte_array)
  (va: AP.array byte)
: Tot vprop
= array_chunk' f a va

let intro_concat_chunks
  (#opened: _)
  (#va1: _)
  (#va2: _)
  (f1 f2: chunk_desc)
  (a1 a2: byte_array)
: STGhost (AP.array byte) opened
    (array_chunk f1 a1 va1 `star` array_chunk f2 a2 va2)
    (fun va -> array_chunk (f1 `concat_chunks` f2) a1 va)
    (AP.adjacent va1 va2)
    (fun va -> AP.merge_into va1 va2 va)
= rewrite (array_chunk f1 a1 va1) (array_chunk' f1 a1 va1);
  rewrite (array_chunk f2 a2 va2) (array_chunk' f2 a2 va2);
  let _ = gen_elim () in
  let va1' = vpattern_replace (AP.arrayptr a1) in
  let va2' = vpattern_replace (AP.arrayptr a2) in
  exact_chunk_concat_chunks_intro f1 f2 (AP.contents_of va1') (AP.contents_of va2');
  let va0 = AP.join a1 a2 in
  let va = AP.array_of va0 in
  noop ();
  rewrite (array_chunk' (f1 `concat_chunks` f2) a1 va) (array_chunk (f1 `concat_chunks` f2) a1 va);
  va

let intro_concat_chunks_nil_l
  (#opened: _)
  (#va2: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a2: byte_array)
: STGhost unit opened
    (array_chunk f2 a2 va2)
    (fun _ -> array_chunk (f1 `concat_chunks` f2) a2 va2)
    (f1.chunk_p Seq.empty)
    (fun _ -> True)
= rewrite (array_chunk f2 a2 va2) (array_chunk' f2 a2 va2);
  let _ = gen_elim () in
  let va2' = vpattern_replace (AP.arrayptr a2) in
  exact_chunk_concat_chunks_empty_l_intro f1 f2 (AP.contents_of' va2');
  noop ();
  rewrite (array_chunk' (f1 `concat_chunks` f2) a2 va2) (array_chunk (f1 `concat_chunks` f2) a2 va2)

let intro_concat_chunks_nil_r
  (#opened: _)
  (#va1: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a1: byte_array)
: STGhost unit opened
    (array_chunk f1 a1 va1)
    (fun _ -> array_chunk (f1 `concat_chunks` f2) a1 va1)
    (f2.chunk_p Seq.empty)
    (fun _ -> True)
= rewrite (array_chunk f1 a1 va1) (array_chunk' f1 a1 va1);
  let _ = gen_elim () in
  let va1' = vpattern_replace (AP.arrayptr a1) in
  exact_chunk_concat_chunks_empty_r_intro f1 f2 (AP.contents_of' va1');
  noop ();
  rewrite (array_chunk' (f1 `concat_chunks` f2) a1 va1) (array_chunk (f1 `concat_chunks` f2) a1 va1)

module SZ = LowParse.Steel.StdInt

let ghost_elim_concat_chunks
  (#opened: _)
  (#va: _)
  (f1 f2: chunk_desc)
  (a: byte_array)
: STGhostT (Ghost.erased byte_array) opened
    (array_chunk (f1 `concat_chunks` f2) a va)
    (fun ar -> exists_ (fun v1 -> exists_ (fun v2 ->
      array_chunk f1 a v1 `star`
      array_chunk f2 ar v2 `star` pure (
      AP.merge_into v1 v2 va
    ))))
= rewrite (array_chunk (f1 `concat_chunks` f2) a va) (array_chunk' (f1 `concat_chunks` f2) a va);
  let _ = gen_elim () in
  let va0 = vpattern_replace (AP.arrayptr a) in
  exact_chunk_intro f1 (AP.contents_of' va0);
  let cl = f1.chunk_len (AP.contents_of' va0) in
  let cl' = SZ.int_to_size_t cl in
  let ar = AP.gsplit a cl' in
  let _ = gen_elim () in
  let va1 = vpattern_replace (AP.arrayptr a) in
  let va2 = vpattern_replace (AP.arrayptr ar) in
  let v1 = AP.array_of va1 in
  let v2 = AP.array_of va2 in
  noop ();
  rewrite (array_chunk' f1 a v1) (array_chunk f1 a v1);
  rewrite (array_chunk' f2 ar v2) (array_chunk f2 ar v2);
  ar

let elim_concat_chunks_nil_l
  (#opened: _)
  (#va2: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a2: byte_array)
: STGhost unit opened
    (array_chunk (f1 `concat_chunks` f2) a2 va2)
    (fun _ -> array_chunk f2 a2 va2)
    (f1.chunk_p Seq.empty)
    (fun _ -> True)
= rewrite (array_chunk (f1 `concat_chunks` f2) a2 va2) (array_chunk' (f1 `concat_chunks` f2) a2 va2);
  let _ = gen_elim () in
  let va2' = vpattern_replace (AP.arrayptr a2) in
  exact_chunk_concat_chunks_empty_l_elim f1 f2 (AP.contents_of' va2');
  noop ();
  rewrite (array_chunk' f2 a2 va2) (array_chunk f2 a2 va2)

let elim_concat_chunks_nil_r
  (#opened: _)
  (#va1: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a1: byte_array)
: STGhost unit opened
    (array_chunk (f1 `concat_chunks` f2) a1 va1)
    (fun _ -> array_chunk f1 a1 va1)
    (f2.chunk_p Seq.empty)
    (fun _ -> True)
= rewrite (array_chunk (f1 `concat_chunks` f2) a1 va1) (array_chunk' (f1 `concat_chunks` f2) a1 va1);
  let _ = gen_elim () in
  let va1' = vpattern_replace (AP.arrayptr a1) in
  exact_chunk_concat_chunks_empty_r_elim f1 f2 (AP.contents_of' va1');
  noop ();
  rewrite (array_chunk' f1 a1 va1) (array_chunk f1 a1 va1)

let intro_parse_some_chunk
  (#opened: _)
  (#k: _)
  (#t: _)
  (#va: _)
  (p: parser k t)
  (v: t)
  (a: byte_array)
: STGhost (AP.array byte) opened
    (aparse p a va)
    (fun va' -> array_chunk (parse_some_chunk p v) a va')
    (v == va.contents)
    (fun va' -> va' == array_of va)
= let va0 = elim_aparse p a in
  assert (parse_chunk p v (AP.contents_of va0) (Seq.length (AP.contents_of va0)));
  let va' = array_of va in
  noop ();
  rewrite (array_chunk' (parse_some_chunk p v) a va') (array_chunk (parse_some_chunk p v) a va');
  va'

let elim_parse_some_chunk
  (#opened: _)
  (#k: _)
  (#t: _)
  (#va: _)
  (p: parser k t)
  (w: t)
  (a: byte_array)
: STGhost (v k t) opened
    (array_chunk (parse_some_chunk p w) a va)
    (fun va' -> aparse p a va')
    True
    (fun va' ->
      va == array_of' va' /\
      va'.contents == w
    )
= rewrite (array_chunk (parse_some_chunk p w) a va) (array_chunk' (parse_some_chunk p w) a va);
  let _ = gen_elim () in
  intro_aparse p a

let rewrite_parse_some_chunk
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#v1: t1)
  (#va: AP.array byte)
  (a: byte_array)
  (#k2: parser_kind)
  (p2: parser k2 t1)
: STGhost unit opened
    (array_chunk (parse_some_chunk p1 v1) a va)
    (fun y2 -> array_chunk (parse_some_chunk p2 v1) a va)
    (forall bytes . parse p1 bytes == parse p2 bytes)
    (fun _ -> True)
= let _ = elim_parse_some_chunk p1 v1 a in
  let _ = rewrite_aparse a p2 in
  let _ = intro_parse_some_chunk p2 v1 a in
  rewrite
    (array_chunk _ a _)
    (array_chunk (parse_some_chunk p2 v1) a va)

let empty_chunk : chunk_desc =
{
  chunk_p = (fun _ -> True);
  chunk_len = (fun _ -> 0);
  chunk_prefix = (fun _ _ -> ());
  chunk_append = (fun _ _ -> ());
}

let empty_chunk_empty = ()

let intro_empty_chunk
  (#opened: _)
  (#va: AP.v byte)
  (f: chunk_desc)
  (a: byte_array)
: STGhost (AP.array byte) opened
    (AP.arrayptr a va)
    (fun va' -> array_chunk f a va')
    (AP.length (AP.array_of va) == 0 /\
      f.chunk_p Seq.empty)
    (fun va' -> va' == AP.array_of va)
=
  let va' = AP.array_of va in
  assert (AP.contents_of' va `Seq.equal` Seq.empty);
  exact_chunk_intro f (AP.contents_of' va);
  noop ();
  rewrite
    (array_chunk' f a va')
    (array_chunk f a va');
  va'

let elim_empty_chunk
  (#opened: _)
  (#va: AP.array byte)
  (f: chunk_desc)
  (a: byte_array)
: STGhost (AP.v byte) opened
    (array_chunk f a va)
    (fun va' -> AP.arrayptr a va')
    (f.chunk_p Seq.empty)
    (fun va' -> 
      AP.array_of va' == va /\
      AP.contents_of' va' `Seq.equal` Seq.empty)
=
  rewrite (array_chunk f a va) (array_chunk' f a va);
  let _ = gen_elim () in
  let va' = vpattern_replace (AP.arrayptr a) in
  f.chunk_append Seq.empty (AP.contents_of' va');
  assert (AP.contents_of' va' `Seq.equal` (Seq.empty `Seq.append` AP.contents_of' va'));
  noop ();
  va'

(* The failing case: what if the output buffer is too small to accommodate the output? *)

let chunk_desc_ge (larger smaller: chunk_desc) : Tot prop =
  forall (b: bytes) . exact_chunk larger b ==> (exists (n: nat) . n <= Seq.length b /\ exact_chunk smaller (Seq.slice b n (Seq.length b)))

let chunk_exceeds_limit
  (c: chunk_desc)
  (limit: nat)
: Tot prop
= forall b0 . exact_chunk c b0 ==> Seq.length b0 > limit

let reveal_chunk_exceeds_limit c limit = ()

let chunk_desc_ge_implies'
  (larger smaller: chunk_desc)
  (b: bytes)
  (limit: nat)
: Lemma
  (requires (
    chunk_desc_ge larger smaller /\
    chunk_exceeds_limit smaller limit /\
    exact_chunk larger b
  ))
  (ensures (
    Seq.length b > limit
  ))
= ()

let chunk_desc_ge_implies
  (larger smaller: chunk_desc)
  (limit: nat)
: Lemma
  (requires (
    chunk_desc_ge larger smaller /\
    chunk_exceeds_limit smaller limit
  ))
  (ensures (
    chunk_exceeds_limit larger limit
  ))
= ()

let chunk_desc_ge_elim (larger smaller: chunk_desc)
  (b: bytes)
: Ghost nat
    (requires (
      chunk_desc_ge larger smaller /\
      exact_chunk larger b
    ))
    (ensures (fun n ->
      n <= Seq.length b /\
      exact_chunk smaller (Seq.slice b n (Seq.length b))
    ))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun n -> n <= Seq.length b /\ exact_chunk smaller (Seq.slice b n (Seq.length b))) 

let chunk_desc_ge_intro (larger smaller: chunk_desc)
  (f: (
    (b: bytes) -> Lemma
    (requires (
      exact_chunk larger b
    ))
    (ensures (exists (n: nat) .
      n <= Seq.length b /\
      exact_chunk smaller (Seq.slice b n (Seq.length b))
    ))
  ))
: Lemma
  (chunk_desc_ge larger smaller)
= Classical.forall_intro (Classical.move_requires f)

let chunk_desc_ge_intro_exact (larger smaller: chunk_desc)
  (f: (
    (b: bytes) -> Lemma
    (requires (
      exact_chunk larger b
    ))
    (ensures (exists (n: nat) .
      exact_chunk smaller b
    ))
  ))
: Lemma
  (chunk_desc_ge larger smaller)
= chunk_desc_ge_intro larger smaller (fun b -> f b)

let chunk_desc_ge_intro' (larger smaller: chunk_desc)
  (f: (
    (b: bytes) -> Ghost nat
    (requires (
      exact_chunk larger b
    ))
    (ensures (fun n ->
      n <= Seq.length b /\
      exact_chunk smaller (Seq.slice b n (Seq.length b))
    ))
  ))
: Lemma
  (chunk_desc_ge larger smaller)
= chunk_desc_ge_intro larger smaller (fun b -> let _ = f b in ())

let chunk_desc_ge_refl (l: chunk_desc) : Lemma
  (chunk_desc_ge l l)
= ()

let chunk_desc_ge_trans (l1 l2 l3: chunk_desc) : Lemma
  ((chunk_desc_ge l1 l2 /\ chunk_desc_ge l2 l3) ==> chunk_desc_ge l1 l3)
= ()

let chunk_desc_ge_zero (l1 l2: chunk_desc) : Lemma
  (requires (
    l2.chunk_p Seq.empty
  ))
  (ensures (
    chunk_desc_ge l1 l2
  ))
= ()

let chunk_desc_ge_concat_chunk_intro (l1 l2: chunk_desc) : Lemma
  (chunk_desc_ge (l1 `concat_chunks` l2) l2)
= ()

let chunk_desc_ge_concat_chunk_compat (l1 l2 l: chunk_desc) : Lemma
  (requires (chunk_desc_ge l1 l2))
  (ensures (chunk_desc_ge (l1 `concat_chunks` l) (l2 `concat_chunks` l)))
= chunk_desc_ge_intro (l1 `concat_chunks` l) (l2 `concat_chunks` l) (fun b ->
    let cl = l1.chunk_len b in
    exact_chunk_intro l1 b;
    let br = Seq.slice b cl (Seq.length b) in
    assert (exact_chunk l br);
    let bl = Seq.slice b 0 cl in
    let n = chunk_desc_ge_elim l1 l2 bl in
    let suff = Seq.slice bl n (Seq.length bl) in
    exact_chunk_concat_chunks_intro l2 l suff br;
    assert (Seq.slice b n (Seq.length b) `Seq.equal` (suff `Seq.append` br))
  )

let chunk_desc_ge_zero_l (l0 l1: chunk_desc) : Lemma
  (requires (
    l0.chunk_p Seq.empty
  ))
  (ensures (
    chunk_desc_ge l1 (l0 `concat_chunks` l1)
  ))
= chunk_desc_ge_intro_exact l1 (l0 `concat_chunks` l1) (fun b ->
    exact_chunk_concat_chunks_empty_l_intro l0 l1 b
  )

let chunk_desc_ge_zero_r (l1 l0: chunk_desc) : Lemma
  (requires (
    l0.chunk_p Seq.empty
  ))
  (ensures (
    chunk_desc_ge l1 (l1 `concat_chunks` l0)
  ))
= chunk_desc_ge_intro_exact l1 (l1 `concat_chunks` l0) (fun b ->
    exact_chunk_concat_chunks_empty_r_intro l1 l0 b
  )

let chunk_desc_ge_assoc_l_r (l1 l2 l3: chunk_desc) : Lemma
  (chunk_desc_ge ((l1 `concat_chunks` l2) `concat_chunks` l3) (l1 `concat_chunks` (l2 `concat_chunks` l3)))
= ()

let chunk_desc_ge_assoc_r_l (l1 l2 l3: chunk_desc) : Lemma
  (chunk_desc_ge (l1 `concat_chunks` (l2 `concat_chunks` l3)) ((l1 `concat_chunks` l2) `concat_chunks` l3))
= ()

let chunk_exceeds_limit_intro_serialize
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (limit: nat)
: Lemma
  (requires (Seq.length (serialize s x) > limit))
  (ensures (chunk_exceeds_limit (parse_some_chunk p x) limit))
= let prf
    (b0: bytes)
  : Lemma
    (requires (exact_chunk (parse_some_chunk p x) b0))
    (ensures (Seq.length b0 > limit))
    [SMTPat (exact_chunk (parse_some_chunk p x) b0)]
  = parse_injective p b0 (serialize s x)
  in
  ()
