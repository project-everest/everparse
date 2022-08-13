module LowParse.SteelST.Fold.Base
open Steel.ST.Util
include LowParse.SteelST.Parse
include LowParse.Spec.Base
include LowParse.Spec.Fold

module AP = LowParse.SteelST.ArrayPtr
module LP = LowParse.Spec.Base

[@@erasable]
val chunk_desc: Type u#1

val chunk_desc_is_empty
  (d: chunk_desc)
: GTot prop

val parse_some_chunk
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
: Tot chunk_desc

val concat_chunks
  (f1 f2: chunk_desc)
: Tot chunk_desc

val exact_chunk
  (f: chunk_desc)
  (input: bytes)
: Tot prop

val exact_chunk_parse_some_chunk
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (b: bytes)
: Lemma
  (parse p b == Some (v, Seq.length b) <==> exact_chunk (parse_some_chunk p v) b)

val exact_chunk_empty
  (f: chunk_desc)
: Lemma
  (chunk_desc_is_empty f <==> exact_chunk f Seq.empty)

val exact_chunk_empty_unique
  (f: chunk_desc)
  (input: bytes)
: Lemma
  (requires (chunk_desc_is_empty f))
  (ensures (exact_chunk f input <==> input == Seq.empty))

val exact_chunk_concat_chunks_intro
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

val exact_chunk_concat_chunks_elim
  (f12 f23: chunk_desc)
  (input: bytes)
: Ghost (bytes & bytes)
  (requires (
    exact_chunk (f12 `concat_chunks` f23) input
  ))
  (ensures (fun (input12, input23) ->
    exact_chunk f12 input12 /\
    exact_chunk f23 input23 /\
    input == input12 `Seq.append` input23
  ))

let exact_chunk_concat_chunks_empty_l_intro
  (f12 f23: chunk_desc)
  (input23: bytes)
: Lemma
  (requires (
    chunk_desc_is_empty f12 /\
    exact_chunk f23 input23
  ))
  (ensures (
    exact_chunk (f12 `concat_chunks` f23) input23
  ))
= exact_chunk_empty f12;
  Seq.append_empty_l input23;
  exact_chunk_concat_chunks_intro f12 f23 Seq.empty input23

let exact_chunk_concat_chunks_empty_l_elim
  (f12 f23: chunk_desc)
  (input23: bytes)
: Lemma
  (requires (
    chunk_desc_is_empty f12 /\
    exact_chunk (f12 `concat_chunks` f23) input23
  ))
  (ensures (
    exact_chunk f23 input23
  ))
= let (input12, input23') = exact_chunk_concat_chunks_elim f12 f23 input23 in
  exact_chunk_empty_unique f12 input12;
  Seq.append_empty_l input23'

let exact_chunk_concat_chunks_empty_r_intro
  (f12 f23: chunk_desc)
  (input12: bytes)
: Lemma
  (requires (
    exact_chunk f12 input12 /\
    chunk_desc_is_empty f23
  ))
  (ensures (
    exact_chunk (f12 `concat_chunks` f23) input12
  ))
= exact_chunk_empty f23;
  exact_chunk_concat_chunks_intro f12 f23 input12 Seq.empty;
  Seq.append_empty_r input12

let exact_chunk_concat_chunks_empty_r_elim
  (f12 f23: chunk_desc)
  (input12: bytes)
: Lemma
  (requires (
    exact_chunk (f12 `concat_chunks` f23) input12 /\
    chunk_desc_is_empty f23
  ))
  (ensures (
    exact_chunk f12 input12
  ))
= let (input12', input23) = exact_chunk_concat_chunks_elim f12 f23 input12 in
  exact_chunk_empty_unique f23 input23;
  Seq.append_empty_r input12'

val array_chunk
  (f: chunk_desc)
  (a: byte_array)
  (va: AP.array byte)
: Tot vprop

val elim_array_chunk
  (#opened: _)
  (f: chunk_desc)
  (a: byte_array)
  (va: AP.array byte)
: STGhost (AP.v byte) opened
    (array_chunk f a va)
    (fun va' -> AP.arrayptr a va')
    True
    (fun va' ->
      AP.array_of va' == va /\
      exact_chunk f (AP.contents_of va'))

val intro_concat_chunks
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

val intro_concat_chunks_nil_l
  (#opened: _)
  (#va2: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a2: byte_array)
: STGhost unit opened
    (array_chunk f2 a2 va2)
    (fun _ -> array_chunk (f1 `concat_chunks` f2) a2 va2)
    (chunk_desc_is_empty f1)
    (fun _ -> True)

val intro_concat_chunks_nil_r
  (#opened: _)
  (#va1: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a1: byte_array)
: STGhost unit opened
    (array_chunk f1 a1 va1)
    (fun _ -> array_chunk (f1 `concat_chunks` f2) a1 va1)
    (chunk_desc_is_empty f2)
    (fun _ -> True)

val ghost_elim_concat_chunks
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

val elim_concat_chunks_nil_l
  (#opened: _)
  (#va2: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a2: byte_array)
: STGhost unit opened
    (array_chunk (f1 `concat_chunks` f2) a2 va2)
    (fun _ -> array_chunk f2 a2 va2)
    (chunk_desc_is_empty f1)
    (fun _ -> True)

val elim_concat_chunks_nil_r
  (#opened: _)
  (#va1: _)
  (f1: chunk_desc)
  (f2: chunk_desc)
  (a1: byte_array)
: STGhost unit opened
    (array_chunk (f1 `concat_chunks` f2) a1 va1)
    (fun _ -> array_chunk f1 a1 va1)
    (chunk_desc_is_empty f2)
    (fun _ -> True)

val intro_parse_some_chunk
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

let intro_parse_some_chunk_auto
  (#opened: _)
  (#k: _)
  (#t: _)
  (#va: _)
  (p: parser k t)
  (a: byte_array)
: STGhostT unit opened
    (aparse p a va)
    (fun va' -> array_chunk (parse_some_chunk p va.contents) a (array_of' va))
= let _ = intro_parse_some_chunk p va.contents a in
  rewrite (array_chunk _ a _) (array_chunk _ a _)

val elim_parse_some_chunk
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

val rewrite_parse_some_chunk
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

let intro_weaken_parse_some_chunk
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#v1: t1)
  (#va: AP.array byte)
  (k2: parser_kind { k2 `is_weaker_than` k1 })
  (a: byte_array)
: STGhostT unit opened
    (array_chunk (parse_some_chunk p1 v1) a va)
    (fun y2 -> array_chunk (parse_some_chunk (LP.weaken k2 p1) v1) a va)
= rewrite_parse_some_chunk a (LP.weaken k2 p1)

let elim_weaken_parse_some_chunk
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#v1: t1)
  (#va: AP.array byte)
  (#k2: parser_kind)
  (a: byte_array)
  (_: squash (k2 `is_weaker_than` k1))
: STGhostT unit opened
    (array_chunk (parse_some_chunk (LP.weaken k2 p1) v1) a va)
    (fun y2 -> array_chunk (parse_some_chunk p1 v1) a va)
= rewrite_parse_some_chunk a p1

val empty_chunk: chunk_desc

val empty_chunk_empty: squash (chunk_desc_is_empty empty_chunk)

val intro_empty_chunk
  (#opened: _)
  (#va: AP.v byte)
  (f: chunk_desc)
  (a: byte_array)
: STGhost (AP.array byte) opened
    (AP.arrayptr a va)
    (fun va' -> array_chunk f a va')
    (AP.length (AP.array_of va) == 0 /\
      chunk_desc_is_empty f)
    (fun va' -> va' == AP.array_of va)

val elim_empty_chunk
  (#opened: _)
  (#va: AP.array byte)
  (f: chunk_desc)
  (a: byte_array)
: STGhost (AP.v byte) opened
    (array_chunk f a va)
    (fun va' -> AP.arrayptr a va')
    (chunk_desc_is_empty f)
    (fun va' -> 
      AP.array_of va' == va /\
      AP.contents_of' va' `Seq.equal` Seq.empty)

(* The failing case: what if the output buffer is too small to accommodate the output? *)

val chunk_desc_ge (larger smaller: chunk_desc) : Tot prop

val chunk_exceeds_limit
  (c: chunk_desc)
  (limit: nat)
: Tot prop

val reveal_chunk_exceeds_limit
  (c: chunk_desc)
  (limit: nat)
: Lemma
  (chunk_exceeds_limit c limit <==> (forall b0 . exact_chunk c b0 ==> Seq.length b0 > limit))

val chunk_exceeds_limit_concat_r
  (c: chunk_desc)
  (limit: nat)
  (c': chunk_desc)
  (b: bytes)
: Lemma
  (requires (
    chunk_exceeds_limit c limit /\
    exact_chunk c' b
  ))
  (ensures (
    chunk_exceeds_limit (c `concat_chunks` c') (limit + Seq.length b)
  ))

val chunk_desc_ge_implies
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

val chunk_desc_ge_intro_exact (larger smaller: chunk_desc)
  (f: (
    (b: bytes) -> Lemma
    (requires (
      exact_chunk larger b
    ))
    (ensures (
      exact_chunk smaller b
    ))
  ))
: Lemma
  (chunk_desc_ge larger smaller)

let chunk_desc_ge_intro_exact_parse_some_chunk
  (#k1: _)
  (#t: _)
  (p1: parser k1 t)
  (#k2: _)
  (p2: parser k2 t)
  (v: t)
: Lemma
  (requires (
    forall b . parse p1 b == parse p2 b
  ))
  (ensures (
    chunk_desc_ge (parse_some_chunk p1 v) (parse_some_chunk p2 v)
  ))
= chunk_desc_ge_intro_exact
    (parse_some_chunk p1 v)
    (parse_some_chunk p2 v)
    (fun b ->
      exact_chunk_parse_some_chunk p1 v b;
      exact_chunk_parse_some_chunk p2 v b
    )

val chunk_desc_ge_refl (l: chunk_desc) : Lemma
  (chunk_desc_ge l l)
  [SMTPat (chunk_desc_ge l l)]

val chunk_desc_ge_trans (l1 l2 l3: chunk_desc) : Lemma
  ((chunk_desc_ge l1 l2 /\ chunk_desc_ge l2 l3) ==> chunk_desc_ge l1 l3)
  [SMTPatOr [
    [SMTPat (chunk_desc_ge l1 l2); SMTPat (chunk_desc_ge l2 l3)];
    [SMTPat (chunk_desc_ge l1 l2); SMTPat (chunk_desc_ge l1 l3)];
    [SMTPat (chunk_desc_ge l2 l3); SMTPat (chunk_desc_ge l1 l3)];
 ]]

val chunk_desc_ge_zero (l1 l2: chunk_desc) : Lemma
  (requires (
    chunk_desc_is_empty l2
  ))
  (ensures (
    chunk_desc_ge l1 l2
  ))

val chunk_desc_ge_concat_chunk_intro_l (l1 l2: chunk_desc) : Lemma
  (chunk_desc_ge (l1 `concat_chunks` l2) l2)

val chunk_desc_ge_concat_chunk_intro_r (l1 l2: chunk_desc) : Lemma
  (chunk_desc_ge (l1 `concat_chunks` l2) l1)

val chunk_desc_ge_concat_chunk_compat_r (l1 l2 l: chunk_desc) : Lemma
  (requires (chunk_desc_ge l1 l2))
  (ensures (chunk_desc_ge (l1 `concat_chunks` l) (l2 `concat_chunks` l)))

val chunk_desc_ge_concat_chunk_compat_l (l1 l2 l: chunk_desc) : Lemma
  (requires (chunk_desc_ge l1 l2))
  (ensures (chunk_desc_ge (l `concat_chunks` l1) (l `concat_chunks` l2)))

val chunk_desc_ge_zero_l (l0 l1: chunk_desc) : Lemma
  (requires (
    chunk_desc_is_empty l0
  ))
  (ensures (
    chunk_desc_ge l1 (l0 `concat_chunks` l1)
  ))

val chunk_desc_ge_zero_r (l1 l0: chunk_desc) : Lemma
  (requires (
    chunk_desc_is_empty l0
  ))
  (ensures (
    chunk_desc_ge l1 (l1 `concat_chunks` l0)
  ))

val chunk_desc_ge_assoc_l_r (l1 l2 l3: chunk_desc) : Lemma
  (chunk_desc_ge ((l1 `concat_chunks` l2) `concat_chunks` l3) (l1 `concat_chunks` (l2 `concat_chunks` l3)))

val chunk_desc_ge_assoc_r_l (l1 l2 l3: chunk_desc) : Lemma
  (chunk_desc_ge (l1 `concat_chunks` (l2 `concat_chunks` l3)) ((l1 `concat_chunks` l2) `concat_chunks` l3))

val chunk_exceeds_limit_intro_serialize
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (limit: nat)
: Lemma
  (requires (Seq.length (serialize s x) > limit))
  (ensures (chunk_exceeds_limit (parse_some_chunk p x) limit))
