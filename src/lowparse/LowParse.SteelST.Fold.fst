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

let parse_some_chunk_empty
: squash
  ((parse_some_chunk parse_empty ()).chunk_p Seq.empty)
= ()

let parse_some_chunk_empty_weaken
  (k: parser_kind)
: Lemma
  (requires (k `is_weaker_than` parse_ret_kind))
  (ensures (parse_some_chunk (weaken k parse_empty) ()).chunk_p Seq.empty)
= ()

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

let exact_chunk_concat_chunks_empty_l_intro
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

let exact_chunk_concat_chunks_empty_l_elim
  (f12 f23: chunk_desc)
  (input23: bytes)
: Lemma
  (requires (
    f12.chunk_p Seq.empty /\
    exact_chunk (f12 `concat_chunks` f23) input23
  ))
  (ensures (
    exact_chunk f23 input23
  ))
= f12.chunk_append Seq.empty input23;
  assert ((Seq.empty `Seq.append` input23) `Seq.equal` input23)

let exact_chunk_concat_chunks_empty_r_intro
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

let exact_chunk_concat_chunks_empty_r_elim
  (f12 f23: chunk_desc)
  (input12: bytes)
: Lemma
  (requires (
    exact_chunk (f12 `concat_chunks` f23) input12 /\
    f23.chunk_p Seq.empty
  ))
  (ensures (
    exact_chunk f12 input12
  ))
= let cl = f12.chunk_len input12 in
  let input23 = Seq.slice input12 cl (Seq.length input12) in
  f23.chunk_append Seq.empty input23;
  assert (input23 `Seq.equal` (Seq.empty `Seq.append` input23))

let rec parse_context
  (#t1 #t2: typ)
  (c: context_t false t1 t2)
: Tot chunk_desc
  (decreases c)
= match c with
  | CNil -> parse_some_chunk parse_empty ()
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
  exact_chunk_concat_chunks f1 f2 (AP.contents_of va1') (AP.contents_of va2');
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

module LP = LowParse.Spec.Base

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

let impl_close_hole_CPairR
  (#opened: _)
  (#va: _)
  (x: hole_t false)
  (sq: squash (
    CCons? x.context /\
    HVValue? x.hole
  ))
  (out: byte_array)
: STGhost unit opened
    (array_chunk (parse_hole x) out va)
    (fun _ -> array_chunk (parse_hole (close_hole x)) out va)
    (let CCons c c' = x.context in CPairR? c)
    (fun _ -> True)
= let CCons c c' = x.context in
  let HVValue r v = x.hole in
  rewrite
    (array_chunk (parse_hole x) out va)
    (array_chunk
      (parse_some_chunk (LP.weaken default_parser_kind (parser_of_typ r)) v `concat_chunks`
        (parse_some_chunk (LP.weaken default_parser_kind parse_empty) () `concat_chunks` parse_context c')
      )
      out va);
  let ar = ghost_elim_concat_chunks _ _ out in
  let _ = gen_elim () in
  elim_concat_chunks_nil_l _ _ ar;
  let _ = intro_concat_chunks _ _ out ar in
  intro_concat_chunks_nil_l (parse_some_chunk (LP.weaken default_parser_kind parse_empty) ()) _ out;
  rewrite
    (array_chunk _ out _)
    (array_chunk (parse_hole (close_hole x)) out va)

open LowParse.SteelST.Combinators

let impl_close_hole_CPairL
  (#opened: _)
  (#va: _)
  (x: hole_t false)
  (sq: squash (
    CCons? x.context /\
    HVValue? x.hole
  ))
  (out: byte_array)
: STGhost unit opened
    (array_chunk (parse_hole x) out va)
    (fun _ -> array_chunk (parse_hole (close_hole x)) out va)
    (let CCons c c' = x.context in CPairL? c)
    (fun _ -> True)
= let CCons c c' = x.context in
  let CPairL _ r vr = c in
  let HVValue l vl = x.hole in
  rewrite
    (array_chunk (parse_hole x) out va)
    (array_chunk
      (parse_some_chunk (LP.weaken default_parser_kind (parser_of_typ l)) vl `concat_chunks`
        (parse_some_chunk (LP.weaken default_parser_kind (parser_of_typ r)) vr `concat_chunks` parse_context c')
      )
      out va);
  let a2 = ghost_elim_concat_chunks _ _ out in
  let _ = gen_elim () in
  let a3 = ghost_elim_concat_chunks _ _ a2 in
  let _ = gen_elim () in
  elim_weaken_parse_some_chunk out ();
  elim_weaken_parse_some_chunk a2 ();
  let _ = elim_parse_some_chunk _ _ out in
  let _ = elim_parse_some_chunk _ _ a2 in
  let _ = merge_pair _ _ out a2 in
  let _ = intro_parse_some_chunk_auto _ out in
  intro_weaken_parse_some_chunk default_parser_kind out;
  let _ = intro_concat_chunks _ _ out a3 in
  rewrite
    (array_chunk _ out _)
    (array_chunk (parse_hole (close_hole x)) out va)

open LowParse.SteelST.List

let impl_close_hole_CListCons
  (#opened: _)
  (#va: _)
  (x: hole_t false)
  (sq: squash (
    CCons? x.context /\
    HVValue? x.hole
  ))
  (out: byte_array)
: STGhost unit opened
    (array_chunk (parse_hole x) out va)
    (fun _ -> array_chunk (parse_hole (close_hole x)) out va)
    (let CCons c c' = x.context in CListCons? c)
    (fun _ -> True)
= let CCons c c' = x.context in
  let CListCons t l = c in
  let HVValue t' v' = x.hole in
  let v : type_of_typ t = coerce (type_of_typ t) v' in
  rewrite
    (array_chunk (parse_hole x) out va)
    (array_chunk
      (parse_some_chunk (LP.weaken default_parser_kind (parser_of_typ t)) v `concat_chunks`
        (parse_some_chunk (LP.weaken default_parser_kind (parse_list (parser_of_typ t))) l `concat_chunks` parse_context c')
      )
      out va);
  let a2 = ghost_elim_concat_chunks _ _ out in
  let _ = gen_elim () in
  let a3 = ghost_elim_concat_chunks _ _ a2 in
  let _ = gen_elim () in
  elim_weaken_parse_some_chunk out ();
  elim_weaken_parse_some_chunk a2 ();
  let _ = elim_parse_some_chunk _ _ out in
  let _ = elim_parse_some_chunk _ _ a2 in
  let _ = intro_cons _ out a2 in
  let _ = intro_parse_some_chunk_auto _ out in
  intro_weaken_parse_some_chunk default_parser_kind out;
  let _ = intro_concat_chunks _ _ out a3 in
  rewrite
    (array_chunk _ out _)
    (array_chunk (parse_hole (close_hole x)) out va)

let impl_close_hole_CChoicePayload
  (#opened: _)
  (#va: _)
  (x: hole_t false)
  (sq: squash (
    CCons? x.context /\
    HVValue? x.hole
  ))
  (out: byte_array)
: STGhost unit opened
    (array_chunk (parse_hole x) out va)
    (fun _ -> array_chunk (parse_hole (close_hole x)) out va)
    (let CCons c c' = x.context in CChoicePayload? c)
    (fun _ -> True)
= let CCons c c' = x.context in
  let HVValue t v = x.hole in
  rewrite
    (array_chunk (parse_hole x) out va)
    (array_chunk (parse_some_chunk (LP.weaken default_parser_kind (parser_of_typ t)) v `concat_chunks`
        (parse_some_chunk (LP.weaken default_parser_kind parse_empty) () `concat_chunks` parse_context c')
    )
      out va);
  let a2 = ghost_elim_concat_chunks _ _ out in
  let _ = gen_elim () in
  elim_concat_chunks_nil_l _ _ a2;
  let _ = intro_concat_chunks _ _ out a2 in
  rewrite
    (array_chunk _ out _)
    (array_chunk (parse_hole (close_hole x)) out va)

let impl_close_hole
  (#opened: _)
  (#va: _)
  (x: hole_t false)
  (sq: squash (
    CCons? x.context /\
    HVValue? x.hole
  ))
  (out: byte_array)
: STGhostT unit opened
    (array_chunk (parse_hole x) out va)
    (fun _ -> array_chunk (parse_hole (close_hole x)) out va)
= let CCons c c' = x.context in
  if CPairL? c
  then impl_close_hole_CPairL x sq out
  else if CPairR? c
  then impl_close_hole_CPairR x sq out
  else if CListCons? c
  then impl_close_hole_CListCons x sq out
  else impl_close_hole_CChoicePayload x sq out
