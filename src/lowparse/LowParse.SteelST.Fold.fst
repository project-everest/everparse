module LowParse.SteelST.Fold
include LowParse.Spec.Fold

open LowParse.Spec.Int
open LowParse.Spec.List
open LowParse.Spec.VLData

let pkind = {
  parser_kind_low = 1;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bool : parser _ bool =
  LowParse.Spec.Enum.parse_enum_key parse_u8 [(true, 1uy); (false, 0uy)]
  `parse_synth`
  (fun x -> x <: bool)

let rec parser_of_typ (t: typ) : Tot (parser pkind (type_of_typ t)) =
  match t returns parser pkind (type_of_typ t) with
  | TU8 -> weaken _ parse_u8
  | TPair t1 t2 -> weaken _ (nondep_then (parser_of_typ t1) (parser_of_typ t2))
  | TList t' ->
    weaken _ (parse_vldata 4 (parse_list (parser_of_typ t')))
  | TChoice f -> weaken _ (parse_dtuple2 parse_bool (fun x -> parser_of_typ (f x)))

let type_of_base_context
  (#erase_values: bool)
  (#t1 #t2: typ)
  (c: base_context_t erase_values t1 t2)
: Tot Type0
= match c with
  | CPairL _ r _ -> type_of_typ r
  | CListCons t _ -> list (type_of_typ t)
  | _ -> unit

let value_of_base_context
  (#t1 #t2: typ)
  (c: base_context_t false t1 t2)
: Tot (type_of_base_context c)
= match c with
  | CPairL _ _ vr -> vr
  | CListCons _ l -> l
  | _ -> ()

let parser_of_base_context
  (#erase_values: bool)
  (#t1 #t2: typ)
  (c: base_context_t erase_values t1 t2)
: Tot (parser default_parser_kind (type_of_base_context c))
= match c with
  | CPairL _ r _ -> weaken _ (parser_of_typ r)
  | CListCons t _ -> weaken _ (parse_list (parser_of_typ t))
  | _ -> weaken _ parse_empty

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

let true_chunk : chunk_desc =
  {
    chunk_p = (fun _ -> True);
    chunk_len = (fun _ -> 0);
    chunk_prefix = (fun _ _ -> ());
    chunk_append = (fun _ _ -> ());
  }

let exact_chunk
  (f: chunk_desc)
  (input: bytes)
: Tot prop
= f.chunk_p input /\
  f.chunk_len input == Seq.length input

let exact_chunk_concat_chunks
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

let exact_chunk_concat_chunks_empty_l
  (f12 f23: chunk_desc)
  (input23: bytes)
: Lemma
  (requires (
    f12.chunk_p Seq.empty /\
    exact_chunk f23 input23
  ))
  (ensures (
    exact_chunk (f12 `concat_chunks` f23) input23
  ))
= let input12' : bytes = Seq.empty in
  exact_chunk_intro f12 input12';
  let input12 = Seq.slice input12' 0 (f12.chunk_len input12') in
  assert (input12 `Seq.equal` input12');
  exact_chunk_concat_chunks f12 f23 input12 input23;
  assert ((input12 `Seq.append` input23) `Seq.equal` input23)

let exact_chunk_concat_chunks_empty_r
  (f12 f23: chunk_desc)
  (input12: bytes)
: Lemma
  (requires (
    exact_chunk f12 input12 /\
    f23.chunk_p Seq.empty
  ))
  (ensures (
    exact_chunk (f12 `concat_chunks` f23) input12
  ))
= let input23' : bytes = Seq.empty in
  exact_chunk_intro f23 input23';
  let input23 = Seq.slice input23' 0 (f23.chunk_len input23') in
  assert (input23 `Seq.equal` input23');
  exact_chunk_concat_chunks f12 f23 input12 input23;
  assert ((input12 `Seq.append` input23) `Seq.equal` input12)

let rec parse_context
  (#t1 #t2: typ)
  (c: context_t false t1 t2)
: Tot chunk_desc
  (decreases c)
= match c with
  | CNil -> true_chunk
  | CCons bc c' ->
    parse_some_chunk (parser_of_base_context bc) (value_of_base_context bc) `concat_chunks`
    parse_context c'

let parse_exact_context_cons_empty
  (#t1 #t2 #t3: typ)
  (b12: base_context_t false t1 t2)
  (c23: context_t false t2 t3)
  (input23: bytes)
: Lemma
  (requires (
    (~ (CPairL? b12 \/ CListCons? b12)) /\
    exact_chunk (parse_context c23) input23 
  ))
  (ensures (
    exact_chunk (parse_context (CCons b12 c23)) input23
  ))
= assert (parse_chunk parse_empty () Seq.empty 0);
  exact_chunk_concat_chunks (parse_some_chunk parse_empty ()) (parse_context c23) Seq.empty input23

let type_of_hole_or_value
  (#erase_values: bool)
  (#t: typ)
  (h: hole_or_value_t erase_values t)
: Tot Type0
= match h with
  | HVHole _ -> unit
  | HVIncompleteList t _ -> list (type_of_typ t)
  | HVChoicePayload _ t' _ -> type_of_typ t'
  | HVValue t _ -> type_of_typ t

let parser_of_hole_or_value
  (#erase_values: bool)
  (#t: typ)
  (h: hole_or_value_t erase_values t)
: Tot (parser default_parser_kind (type_of_hole_or_value h))
= match h with
  | HVHole _ -> weaken _ parse_empty
  | HVIncompleteList t _ -> weaken _ (parse_list (parser_of_typ t))
  | HVChoicePayload _ t' _ -> weaken _ (parser_of_typ t')
  | HVValue t _ -> weaken _ (parser_of_typ t)

let value_of_hole_or_value
  (#t: typ)
  (h: hole_or_value_t false t)
: Tot (type_of_hole_or_value h)
= match h with
  | HVHole _ -> ()
  | HVIncompleteList _ l -> l
  | HVChoicePayload _ _ pl -> pl
  | HVValue _ v -> v

let parse_hole
  (h: hole_t false)
: Tot chunk_desc
= parse_some_chunk (parser_of_hole_or_value h.hole) (value_of_hole_or_value h.hole) `concat_chunks`
  parse_context h.context

open LowParse.SteelST.Parse
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr

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

let array_chunk_concat_chunks
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
  exact_chunk_concat_chunks f1 f2 (AP.contents_of va1') (AP.contents_of va2');
  let va0 = AP.join a1 a2 in
  let va = AP.array_of va0 in
  noop ();
  rewrite (array_chunk' (f1 `concat_chunks` f2) a1 va) (array_chunk (f1 `concat_chunks` f2) a1 va);
  va

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
