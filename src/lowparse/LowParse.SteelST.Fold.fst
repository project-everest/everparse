module LowParse.SteelST.Fold
include LowParse.SteelST.Fold.Base
include LowParse.Spec.SerializationState

open Steel.ST.GenElim
open LowParse.SteelST.Combinators
open LowParse.SteelST.List
open LowParse.SteelST.Int
open LowParse.SteelST.VLData

module AP = LowParse.SteelST.ArrayPtr
module LP = LowParse.Spec.Base
module SZ = LowParse.Steel.StdInt

let pkind = {
  parser_kind_low = 1;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bool : parser (parse_filter_kind parse_u8_kind) bool =
  parse_u8
    `parse_filter`
    (fun x -> (x = 1uy || x = 0uy))
    `parse_synth`
    (fun x -> (x = 1uy))

let serialize_bool : serializer parse_bool =
  serialize_synth
    (parse_u8 `parse_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    (serialize_u8 `serialize_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun y -> if y then 1uy else 0uy)
    ()

inline_for_extraction
let read_bool : leaf_reader parse_bool =
  read_synth'
    (read_filter read_u8 (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    ()

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

let rec parse_context
  (#t1 #t2: typ)
  (c: context_t false t1 t2)
: Tot chunk_desc
  (decreases c)
= match c with
  | CNil -> empty_chunk
  | CCons bc c' ->
    parse_some_chunk (parser_of_base_context bc) (value_of_base_context bc) `concat_chunks`
    parse_context c'

let parse_some_chunk_empty
: squash
  (chunk_desc_is_empty (parse_some_chunk parse_empty ()))
= exact_chunk_parse_some_chunk parse_empty () Seq.empty;
  exact_chunk_empty (parse_some_chunk parse_empty ())

let parse_some_chunk_empty_weaken
  (k: parser_kind)
: Lemma
  (requires (k `is_weaker_than` parse_ret_kind))
  (ensures (chunk_desc_is_empty (parse_some_chunk (weaken k parse_empty) ())))
  [SMTPat (parse_some_chunk (weaken k parse_empty) ())]
= let p = weaken k parse_empty in
  exact_chunk_parse_some_chunk p () Seq.empty;
  exact_chunk_empty (parse_some_chunk p ())

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
= exact_chunk_concat_chunks_empty_l_intro (parse_some_chunk (weaken default_parser_kind parse_empty) ()) (parse_context c23) input23

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

inline_for_extraction
noeq
type context_arrays : AP.array byte -> Type0 =
| CANil: (a: AP.array byte) -> context_arrays a
| CACons: (b: byte_array) -> (a0: AP.array byte) -> (al: AP.array byte) -> (sz: SZ.size_t) -> (ar: AP.array byte) -> squash (AP.merge_into al ar a0 /\ SZ.size_v sz == AP.length al) -> (c: context_arrays ar) -> context_arrays a0

let rec parse_context_arrays
  (#tfrom: typ)
  (#tto: typ)
  (c: context_t false tfrom tto)
  (b: byte_array)
  (#a: AP.array byte)
  (ca: context_arrays a)
: Tot vprop
  (decreases c)
= if CNil? c
  then
    if CANil? ca
    then array_chunk empty_chunk b a
    else pure False
  else
    if CACons? ca
    then array_chunk (parse_some_chunk (parser_of_base_context (CCons?.bc c)) (value_of_base_context (CCons?.bc c))) b (CACons?.al ca) `star` parse_context_arrays (CCons?.c c) (CACons?.b ca) (CACons?.c ca)
    else pure False

let intro_parse_context_arrays_nil
  (#opened: _)
  (ty: typ)
  (b: byte_array)
  (a: AP.array byte)
: STGhostT unit opened
    (array_chunk empty_chunk b a)
    (fun _ -> parse_context_arrays (CNil #_ #ty) b (CANil a))
= rewrite
    (array_chunk empty_chunk b a)
    (parse_context_arrays (CNil #_ #ty) b (CANil a))

let elim_parse_context_arrays_nil
  (#opened: _)
  (#tfrom #tto: typ)
  (c0: context_t false tfrom tto)
  (b: byte_array)
  (#a: AP.array byte)
  (c: context_arrays a)
: STGhost unit opened
    (parse_context_arrays c0 b c)
    (fun _ -> array_chunk empty_chunk b a)
    (CNil? c0)
    (fun _ -> CANil? c)
= if CANil? c
  then
    rewrite
      (parse_context_arrays c0 b c)
      (array_chunk empty_chunk b a)
  else begin
    rewrite
      (parse_context_arrays c0 b c)
      (pure False);
    let _ = gen_elim () in
    rewrite
      emp
      (array_chunk empty_chunk b a)
  end

let intro_parse_context_arrays_cons
  (#opened: _)
  (#t1: typ)
  (#t2: typ)
  (#t3: typ)
  (bc: base_context_t false t1 t2)
  (c0: context_t false t2 t3)
  (bl: byte_array)
  (br: byte_array)
  (al: AP.array byte)
  (sz: SZ.size_t)
  (ar: AP.array byte)
  (c: context_arrays ar)
  (sq: squash (AP.adjacent al ar /\ SZ.size_v sz == AP.length al))
: STGhostT unit opened
    (array_chunk (parse_some_chunk (parser_of_base_context bc) (value_of_base_context bc)) bl al `star` parse_context_arrays c0 br c)
    (fun _ -> parse_context_arrays (CCons bc c0) bl (CACons br (AP.merge al ar) al sz ar () c))
=
  assert_norm (
    (parse_context_arrays (CCons bc c0) bl (CACons br (AP.merge al ar) al sz ar () c)) == (array_chunk (parse_some_chunk (parser_of_base_context bc) (value_of_base_context bc)) bl al `star` parse_context_arrays c0 br c)  
  );
  rewrite
    (array_chunk (parse_some_chunk (parser_of_base_context bc) (value_of_base_context bc)) bl al `star` parse_context_arrays c0 br c)
    (parse_context_arrays (CCons bc c0) bl (CACons br (AP.merge al ar) al sz ar () c))

let elim_parse_context_arrays_cons
  (#opened: _)
  (#tfrom #tto: typ)
  (c0: context_t false tfrom tto)
  (b: byte_array)
  (#a: AP.array byte)
  (c: context_arrays a)
  (sq: squash (CCons? c0))
: STGhostT (squash (CACons? c)) opened
    (parse_context_arrays c0 b c)
    (fun _ ->
      array_chunk (parse_some_chunk (parser_of_base_context (CCons?.bc c0)) (value_of_base_context (CCons?.bc c0))) b (CACons?.al c) `star`
      parse_context_arrays (CCons?.c c0) (CACons?.b c) (CACons?.c c)
    )
= let CCons bc c0' = c0 in
  if CACons? c
  then begin
    let CACons br' a' al' sz' ar' sq' c' = c in
    assert_norm (
      parse_context_arrays (CCons bc c0') b (CACons br' a' al' sz' ar' sq' c') ==
        array_chunk (parse_some_chunk (parser_of_base_context bc) (value_of_base_context bc)) b al' `star`
        parse_context_arrays c0' br' c'
    );
  rewrite
    (parse_context_arrays c0 b c)
    (array_chunk (parse_some_chunk (parser_of_base_context (CCons?.bc c0)) (value_of_base_context (CCons?.bc c0))) b (CACons?.al c) `star`
      parse_context_arrays (CCons?.c c0) (CACons?.b c) (CACons?.c c)
    )
  end else begin
    rewrite
      (parse_context_arrays c0 b c)
      (pure False);
    let _ = gen_elim () in
    rewrite
      emp
      (array_chunk (parse_some_chunk (parser_of_base_context (CCons?.bc c0)) (value_of_base_context (CCons?.bc c0))) b (CACons?.al c) `star`
      parse_context_arrays (CCons?.c c0) (CACons?.b c) (CACons?.c c))
  end

let rec parse_context_arrays_parse_context
  (#opened: _)
  (#tfrom #tto: typ)
  (c0: context_t false tfrom tto)
  (b: byte_array)
  (#a: AP.array byte)
  (c: context_arrays a)
: STGhostT unit opened
    (parse_context_arrays c0 b c)
    (fun _ -> array_chunk (parse_context c0) b a)
    (decreases c0)
= if CNil? c0
  then begin
    elim_parse_context_arrays_nil c0 b c;
    rewrite
      (array_chunk _ _ _)
      (array_chunk (parse_context c0) b a)
  end else begin
    let _ = elim_parse_context_arrays_cons c0 b c () in
    parse_context_arrays_parse_context (CCons?.c c0) (CACons?.b c) (CACons?.c c);
    let _ = intro_concat_chunks _ _ b _ in
    rewrite
      (array_chunk _ _ _)
      (array_chunk (parse_context c0) b a)
  end

inline_for_extraction
noeq
type hole_arrays =
{
  ha_hole_a: AP.array byte;
  ha_hole_b: byte_array;
  ha_hole_sz: SZ.size_t;
  ha_context_a: AP.array byte;
  ha_context_b: byte_array;
  ha_context: context_arrays ha_context_a;
  ha_prf: squash (AP.adjacent ha_hole_a ha_context_a /\ SZ.size_v ha_hole_sz == AP.length ha_hole_a);
}

let array_of_hole
  (h: hole_arrays)
: Tot (AP.array byte)
= AP.merge h.ha_hole_a h.ha_context_a

[@@__reduce__]
let parse_hole_arrays'
  (h: hole_t false)
  (ha: hole_arrays)
: Tot vprop
= array_chunk (parse_some_chunk (parser_of_hole_or_value h.hole) (value_of_hole_or_value h.hole)) ha.ha_hole_b ha.ha_hole_a `star`
  parse_context_arrays h.context ha.ha_context_b ha.ha_context

let parse_hole_arrays
  (h: hole_t false)
  (ha: hole_arrays)
: Tot vprop
= parse_hole_arrays' h ha

let parse_hole_arrays_empty_context
  (#opened: _)
  (h: hole_t false)
  (ha: hole_arrays)
: STGhost unit opened
    (parse_hole_arrays h ha)
    (fun _ -> parse_hole_arrays h ha)
    (CNil? h.context)
    (fun _ -> CANil? ha.ha_context)
= rewrite
    (parse_hole_arrays h ha)
    (parse_hole_arrays' h ha);
  elim_parse_context_arrays_nil h.context ha.ha_context_b ha.ha_context;
  intro_parse_context_arrays_nil h.root ha.ha_context_b ha.ha_context_a;
  rewrite
    (parse_context_arrays _ _ _)
    (parse_context_arrays h.context ha.ha_context_b ha.ha_context);
  rewrite
    (parse_hole_arrays' h ha)
    (parse_hole_arrays h ha)
  
#push-options "--z3rlimit 32"

inline_for_extraction
let mk_initial_hole_array
  (#vb: AP.v byte)
  (ty: typ)
  (b: byte_array)
  (sz: SZ.size_t)
  (kpre: vprop)
  (kpost: vprop)
  (k: (
    (sz': SZ.size_t) ->
    (ha: hole_arrays) ->
    STT unit
      (kpre `star` parse_hole_arrays (initial_ser_state ty) ha `star`
        exists_ (fun vl -> AP.arrayptr b vl `star` pure (
          AP.merge_into (AP.array_of vl) (array_of_hole ha) (AP.array_of vb) /\
          AP.length (AP.array_of vl) == SZ.size_v sz'
      )))
      (fun _ -> kpost)
  ))
: ST unit
    (kpre `star` AP.arrayptr b vb)
    (fun _ -> kpost)
    (SZ.size_v sz == AP.length (AP.array_of vb))
    (fun _ -> True)
= let bh = AP.split b sz in
  let _ = gen_elim () in
  let bc = AP.split bh SZ.zero_size in
  let _ = gen_elim () in
  let ah = intro_empty_chunk (parse_some_chunk (weaken default_parser_kind parse_empty) ()) bh in
  let ac = intro_empty_chunk empty_chunk bc in
  intro_parse_context_arrays_nil ty bc _;
  [@@inline_let]
  let ha = {
    ha_hole_a = ah;
    ha_hole_b = bh;
    ha_hole_sz = SZ.zero_size;
    ha_context_a = ac;
    ha_context_b = bc;
    ha_context = CANil _;
    ha_prf = ();
  }
  in
  rewrite
    (array_chunk _ bh _ `star` parse_context_arrays _ bc _)
    (parse_hole_arrays (initial_ser_state ty) ha);
  k sz ha

#pop-options

let chunk_desc_ge_parse_pair
  (#k1: _)
  (#t1: _)
  (p1: parser k1 t1)
  (#k2: _)
  (#t2: _)
  (p2: parser k2 t2)
  (v1: _)
  (v2: _)
: Lemma
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (
    chunk_desc_ge (parse_some_chunk (p1 `nondep_then` p2) (v1, v2)) (parse_some_chunk p1 v1 `concat_chunks` parse_some_chunk p2 v2)
  ))
= chunk_desc_ge_intro_exact (parse_some_chunk (p1 `nondep_then` p2) (v1, v2)) (parse_some_chunk p1 v1 `concat_chunks` parse_some_chunk p2 v2) (fun b ->
    exact_chunk_parse_some_chunk (p1 `nondep_then` p2) (v1, v2) b;
    nondep_then_eq p1 p2 b;
    let Some (_, consumed) = parse p1 b in
    Seq.lemma_split b consumed;
    let bl = Seq.slice b 0 consumed in
    parse_strong_prefix p1 b bl;
    let br = Seq.slice b consumed (Seq.length b) in
    exact_chunk_parse_some_chunk p1 v1 bl;
    exact_chunk_parse_some_chunk p2 v2 br;
    exact_chunk_concat_chunks_intro (parse_some_chunk p1 v1) (parse_some_chunk p2 v2) bl br;
    assert (exact_chunk (parse_some_chunk p1 v1 `concat_chunks`parse_some_chunk p2 v2) b)
  )

let chunk_desc_ge_parse_pair_test
  (#k1: _)
  (#t1: _)
  (p1: parser k1 t1)
  (#k2: _)
  (#t2: _)
  (p2: parser k2 t2)
  (v1: _)
  (v2: _)
: Lemma
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (
    chunk_desc_ge (parse_some_chunk (p1 `nondep_then` p2) (v1, v2)) (parse_some_chunk p1 v1 `concat_chunks` (parse_some_chunk parse_empty () `concat_chunks` parse_some_chunk p2 v2))
  ))
=
  chunk_desc_ge_parse_pair p1 p2 v1 v2;
  chunk_desc_ge_zero_r (parse_some_chunk p1 v1) (parse_some_chunk parse_empty ());
  chunk_desc_ge_concat_chunk_compat_r (parse_some_chunk p1 v1) (parse_some_chunk p1 v1 `concat_chunks` parse_some_chunk parse_empty ()) (parse_some_chunk p2 v2);
  chunk_desc_ge_assoc_l_r (parse_some_chunk p1 v1) (parse_some_chunk parse_empty ()) (parse_some_chunk p2 v2)

module U8 = FStar.UInt8

inline_for_extraction
[@@noextract_to "krml"]
let impl_ser_u8'
  (#vb: AP.v byte)
  (x: U8.t)
  (b: byte_array)
  (sz: SZ.size_t)
  (kpre: vprop)
  (kpost: vprop)
  (k_success: (
    (vl: AP.v byte) ->
    (vr: AP.array byte) ->
    (br: byte_array) ->
    (sz': SZ.size_t) ->
    ST unit
      (kpre `star` AP.arrayptr b vl `star` array_chunk (parse_some_chunk parse_u8 x) br vr)
      (fun _ -> kpost)
      (AP.merge_into (AP.array_of vl) vr (AP.array_of vb) /\
        SZ.size_v sz' == AP.length (AP.array_of vl))
      (fun _ -> True)
  ))
  (k_failure: (
    (vb': AP.v byte) ->
    ST unit
      (kpre `star` AP.arrayptr b vb')
      (fun _ -> kpost)
      (AP.array_of vb' == AP.array_of vb /\
        chunk_exceeds_limit (parse_some_chunk parse_u8 x) (AP.length (AP.array_of vb)))
      (fun _ -> True)
  ))
: ST unit
    (kpre `star` AP.arrayptr b vb)
    (fun _ -> kpost)
    (SZ.size_v sz == AP.length (AP.array_of vb) /\
      AP.array_perm (AP.array_of vb) == full_perm)
    (fun _ -> True)
= if sz `SZ.size_lt` SZ.mk_size_t 1ul
  then begin
    chunk_exceeds_limit_intro_serialize serialize_u8 x (SZ.size_v sz);
    k_failure vb
  end else begin
    let sz' = SZ.size_sub sz (SZ.mk_size_t 1ul) in
    let br = AP.split b sz' in
    let _ = gen_elim () in
    let _ = write_u8 x br in
    let _ = intro_parse_some_chunk _ _ _ in
    k_success _ _ _ sz'
  end

inline_for_extraction
[@@noextract_to "krml"]
let action_impl_t
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (p: ser_action ret_t pre post)
: Tot Type
= (#vl: AP.v byte) ->
  (bout: byte_array) ->
  (sz: SZ.size_t) ->
  (out: hole_arrays) ->
  (h: Ghost.erased (ser_state pre)) ->
  (kpre: vprop) ->
  (kpost: vprop) ->
  (k_success: (
    (vl': AP.v byte) ->
    (sz': SZ.size_t) ->
    (out': hole_arrays) ->
    (h': Ghost.erased (ser_state post)) ->
    (v: ret_t) ->
    ST unit
      (kpre `star`
        AP.arrayptr bout vl' `star` parse_hole_arrays h' out')
      (fun _ -> kpost)
      (
        AP.adjacent (AP.array_of vl) (array_of_hole out) /\
        AP.merge_into (AP.array_of vl') (array_of_hole out') (AP.merge (AP.array_of vl) (array_of_hole out)) /\
        ser_action_sem p h == (v, Ghost.reveal h') /\
        SZ.size_v sz' == AP.length (AP.array_of vl')
      )
      (fun _ -> True)
  )) ->
  (k_failure: (
    (vb': AP.v byte) ->
    ST unit
      (kpre `star` AP.arrayptr bout vb')
      (fun _ -> kpost)
      (
        let (_, h') = ser_action_sem p h in
        AP.merge_into (AP.array_of vl) (array_of_hole out) (AP.array_of vb') /\
        chunk_exceeds_limit (parse_hole h') (AP.length (AP.array_of vb'))
      )
      (fun _ -> True)
  )) ->
  ST unit
    (kpre `star`
      AP.arrayptr bout vl `star` parse_hole_arrays h out)
    (fun _ -> kpost)
    (SZ.size_v sz == AP.length (AP.array_of vl) /\
      AP.array_perm (AP.array_of vl) == full_perm /\
      AP.adjacent (AP.array_of vl) (array_of_hole out)
    )
    (fun _ -> True)

inline_for_extraction
[@@noextract_to "krml"]
let impl_ser_u8
  (#root: _)
  (#pre: ser_index root)
  (w: U8.t)
  (sq: squash (pre.leaf == TU8 /\ HVHole? pre.hole))
: Tot (action_impl_t (SU8 #_ #pre w ()))
= fun #vl bout sz out h kpre kpost k_success k_failure ->
  rewrite
    (parse_hole_arrays h out)
    (parse_hole_arrays' h out);
  let _ = elim_empty_chunk _ out.ha_hole_b in
  let _ = AP.join bout out.ha_hole_b in
  impl_ser_u8'
    w
    bout
    sz
    (parse_context_arrays h.context out.ha_context_b out.ha_context `star` kpre)
    kpost
    (fun vl vr br sz' ->
      intro_weaken_parse_some_chunk default_parser_kind br;
      [@inline_let]
      let out' = {
        ha_hole_a = vr;
        ha_hole_b = br;
        ha_hole_sz = sz `SZ.size_sub` sz';
        ha_context = out.ha_context;
        ha_context_a = out.ha_context_a;
        ha_context_b = out.ha_context_b;
        ha_prf = ();
      }
      in
      let h' = Ghost.hide (fill_hole h w) in
      rewrite
        (array_chunk _ br vr `star` parse_context_arrays _ _ _)
        (parse_hole_arrays h' out');
      k_success vl sz' out' h' ()
    )
    (fun vb ->
      let _ = parse_context_arrays_parse_context _ _ _ in
      let vr = elim_array_chunk _ _ _ in
      chunk_desc_ge_intro_exact_parse_some_chunk
        (weaken default_parser_kind (parser_of_typ TU8))
        parse_u8
        w;
      chunk_desc_ge_implies
        (parse_some_chunk (weaken default_parser_kind (parser_of_typ TU8)) w)
        (parse_some_chunk parse_u8 w)
        (AP.length (AP.array_of vb));
      chunk_exceeds_limit_concat_r
        (parse_some_chunk (weaken default_parser_kind (parser_of_typ TU8)) w)
        (AP.length (AP.array_of vb))
        (parse_context h.context)
        (AP.contents_of vr);
      let vb' = AP.join bout _ in
      k_failure vb'
    )

inline_for_extraction
[@@noextract_to "krml"]
let fold_impl_t
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
  (p: fold_t (ser_state #root) ty ret_t pre post)
: Tot Type
= (#vbin: _) ->
  (#vl: AP.v byte) ->
  (bin: byte_array) ->
  (bout: byte_array) ->
  (sz: SZ.size_t) ->
  (out: hole_arrays) ->
  (h: Ghost.erased (ser_state pre)) ->
  (kpre: vprop) ->
  (kpost: vprop) ->
  (k_success: (
    (vl': AP.v byte) ->
    (sz': SZ.size_t) ->
    (out': hole_arrays) ->
    (h': Ghost.erased (ser_state post)) ->
    (v: ret_t) ->
    ST unit
      (kpre `star` aparse pty bin vbin `star`
        AP.arrayptr bout vl' `star` parse_hole_arrays h' out')
      (fun _ -> kpost)
      (
        AP.adjacent (AP.array_of vl) (array_of_hole out) /\
        AP.merge_into (AP.array_of vl') (array_of_hole out') (AP.merge (AP.array_of vl) (array_of_hole out)) /\
        p vbin.contents h == (v, Ghost.reveal h') /\
        SZ.size_v sz' == AP.length (AP.array_of vl')
      )
      (fun _ -> True)
  )) ->
  (k_failure: (
    (vb': AP.v byte) ->
    ST unit
      (kpre `star` aparse pty bin vbin `star` AP.arrayptr bout vb')
      (fun _ -> kpost)
      (
        let (_, h') = p vbin.contents h in
        AP.merge_into (AP.array_of vl) (array_of_hole out) (AP.array_of vb') /\
        chunk_exceeds_limit (parse_hole h') (AP.length (AP.array_of vb'))
      )
      (fun _ -> True)
  )) ->
  ST unit
    (kpre `star` aparse pty bin vbin `star`
      AP.arrayptr bout vl `star` parse_hole_arrays h out)
    (fun _ -> kpost)
    (SZ.size_v sz == AP.length (AP.array_of vl) /\
      AP.array_perm (AP.array_of vl) == full_perm /\
      AP.adjacent (AP.array_of vl) (array_of_hole out)
    )
    (fun _ -> True)

inline_for_extraction
[@@noextract_to "krml"]
let prog_impl_t
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t pre post)
: Tot Type
= fold_impl_t (parser_of_typ ty) (sem ser_action_sem p)

inline_for_extraction
let impl_action
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (p: ser_action ret_t pre post)
  (impl_p: action_impl_t p)
  (t: typ)
: Tot (prog_impl_t (PAction #_ #_ #_ #t p))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  impl_p bout sz out h
    (aparse (parser_of_typ t) bin vbin `star` kpre)
    kpost
    k_success
    k_failure

module R = Steel.ST.Reference

(* loading and storing context *)

let rec context_arrays_shape
  (#tfrom: typ)
  (#tto: typ)
  (c: context_t true tfrom tto)
  (#a: AP.array byte)
  (ca: context_arrays a)
: Tot prop
  (decreases c)
= (CNil? c == CANil? ca) /\
  (CCons? c ==>
    context_arrays_shape (CCons?.c c) (CACons?.c ca))

let rec parse_context_arrays_shape
  (#opened: _)
  (#tfrom: typ)
  (#tto: typ)
  (c: context_t false tfrom tto)
  (b: byte_array)
  (#a: AP.array byte)
  (ca: context_arrays a)
: STGhost unit opened
    (parse_context_arrays c b ca)
    (fun _ -> parse_context_arrays c b ca)
    True
    (fun _ -> context_arrays_shape (context_erase_values c) ca)
    (decreases c)
= if CNil? c
  then begin
    elim_parse_context_arrays_nil c b ca;
    intro_parse_context_arrays_nil tfrom b _;
    rewrite
      (parse_context_arrays _ _ _)
      (parse_context_arrays c b ca)
  end else begin
    let _ = elim_parse_context_arrays_cons c b ca () in
    parse_context_arrays_shape (CCons?.c c) (CACons?.b ca) (CACons?.c ca);
    intro_parse_context_arrays_cons _ _ _ _ _ (CACons?.sz ca) _ _ ();
    rewrite
      (parse_context_arrays _ _ _)
      (parse_context_arrays c b ca)
  end

let parse_hole_arrays_context_arrays_shape
  (#opened: _)
  (h: hole_t false)
  (ha: hole_arrays)
: STGhost unit opened
    (parse_hole_arrays h ha)
    (fun _ -> parse_hole_arrays h ha)
    True
    (fun _ -> context_arrays_shape (context_erase_values h.context) ha.ha_context)
= rewrite
    (parse_hole_arrays h ha)
    (parse_hole_arrays' h ha);
  parse_context_arrays_shape _ _ _;
  rewrite
    (parse_hole_arrays' h ha)
    (parse_hole_arrays h ha)

inline_for_extraction
noeq
type context_arrays_ptr : Type0 =
| CAPNil: context_arrays_ptr
| CAPCons:
  (b: R.ref byte_array) ->
  (bsz: R.ref SZ.size_t) ->
  (c: context_arrays_ptr) ->
  context_arrays_ptr

let rec context_arrays_pts_to
  (cp: context_arrays_ptr)
  (#a: AP.array byte)
  (c: context_arrays a)
: Tot vprop
  (decreases c)
= if CANil? c
  then pure (CAPNil? cp == true)
  else if CAPNil? cp
  then pure False
  else
    R.pts_to (CAPCons?.b cp) full_perm (CACons?.b c) `star`
    R.pts_to (CAPCons?.bsz cp) full_perm (CACons?.sz c) `star`
    context_arrays_pts_to (CAPCons?.c cp) (CACons?.c c)

let intro_context_arrays_pts_to_nil
  (#opened: _)
  (a: AP.array byte)
: STGhostT unit opened
    emp
    (fun _ -> context_arrays_pts_to CAPNil (CANil a))
= rewrite
    (pure (CANil? (CANil a) == true))
    (context_arrays_pts_to CAPNil (CANil a))

let elim_context_arrays_pts_to_nil
  (#opened: _)
  (cp: context_arrays_ptr)
  (#a: AP.array byte)
  (c: context_arrays a)
: STGhost unit opened
    (context_arrays_pts_to cp c)
    (fun _ -> emp)
    (CAPNil? cp \/ CANil? c)
    (fun _ -> CANil? c /\ CAPNil? cp)
= if CANil? c
  then begin
    rewrite
      (context_arrays_pts_to cp c)
      (pure (CAPNil? cp == true));
    let _ = gen_elim () in
    ()
  end else begin
    rewrite
      (context_arrays_pts_to cp c)
      (pure False);
    let _ = gen_elim () in
    ()
  end

let intro_context_arrays_pts_to_cons
  (#opened: _)
  (bb: R.ref byte_array)
  (bsz: R.ref SZ.size_t)
  (cp: context_arrays_ptr)
  (b: byte_array)
  (a0: AP.array byte)
  (al: AP.array byte)
  (sz: SZ.size_t)
  (ar: AP.array byte)
  (sq: squash (AP.merge_into al ar a0 /\ SZ.size_v sz == AP.length al))
  (c: context_arrays ar)
: STGhostT unit opened
    (R.pts_to bb full_perm b `star`
      R.pts_to bsz full_perm sz `star`
      context_arrays_pts_to cp c)
    (fun _ -> context_arrays_pts_to (CAPCons bb bsz cp) (CACons b a0 al sz ar sq c))
= rewrite
    (R.pts_to bb full_perm b `star`
      R.pts_to bsz full_perm sz `star`
      context_arrays_pts_to cp c)
    (context_arrays_pts_to (CAPCons bb bsz cp) (CACons b a0 al sz ar sq c))

let elim_context_arrays_pts_to_cons
  (#opened: _)
  (cp: context_arrays_ptr)
  (#a: AP.array byte)
  (c: context_arrays a)
: STGhost (squash (CACons? c /\ CAPCons? cp)) opened
    (context_arrays_pts_to cp c)
    (fun _ ->
      R.pts_to (CAPCons?.b cp) full_perm (CACons?.b c) `star`
      R.pts_to (CAPCons?.bsz cp) full_perm (CACons?.sz c) `star`
      context_arrays_pts_to (CAPCons?.c cp) (CACons?.c c))
    (CACons? c \/ CAPCons? cp)
    (fun _ -> True)
= if CANil? c
  then begin
    rewrite
      (context_arrays_pts_to cp c)
      (pure (CAPNil? cp == true));
    let _ = gen_elim () in
    assert False;
    rewrite // by contradiction
      emp
      (R.pts_to (CAPCons?.b cp) full_perm (CACons?.b c) `star`
        R.pts_to (CAPCons?.bsz cp) full_perm (CACons?.sz c) `star`
        context_arrays_pts_to (CAPCons?.c cp) (CACons?.c c))
  end else
  if CAPNil? cp
  then begin
    rewrite
      (context_arrays_pts_to cp c)
      (pure False);
    let _ = gen_elim () in
    rewrite // by contradiction
      emp
      (R.pts_to (CAPCons?.b cp) full_perm (CACons?.b c) `star`
        R.pts_to (CAPCons?.bsz cp) full_perm (CACons?.sz c) `star`
        context_arrays_pts_to (CAPCons?.c cp) (CACons?.c c))
  end else
  begin
    rewrite
      (context_arrays_pts_to cp c)
      (R.pts_to (CAPCons?.b cp) full_perm (CACons?.b c) `star`
        R.pts_to (CAPCons?.bsz cp) full_perm (CACons?.sz c) `star`
        context_arrays_pts_to (CAPCons?.c cp) (CACons?.c c))
  end

inline_for_extraction
let with_context_arrays_ptr_t
  (#tfrom #tto: typ)
  (ci: context_t true tfrom tto)
: Tot Type
= (#a: AP.array byte) ->
  (c: context_arrays a) ->
  (kpre: vprop) ->
  (tret: Type) ->
  (kpost: (tret -> vprop)) ->
  (k: (
    (cp: context_arrays_ptr) ->
    STT tret
      (kpre `star` context_arrays_pts_to cp c)
      (fun r -> kpost r `star` exists_ (fun a -> exists_ (context_arrays_pts_to cp #a)))
  )) ->
  ST tret
    kpre
    kpost
    (context_arrays_shape ci c)
    (fun _ -> True)

inline_for_extraction
let with_context_arrays_ptr_nil
  (t: Ghost.erased typ)
: with_context_arrays_ptr_t (CNil #_ #t)
= fun #a c kpre tret kpost k ->
    [@inline_let]
    let cp = CAPNil in
    intro_context_arrays_pts_to_nil a;
    rewrite (context_arrays_pts_to _ _) (context_arrays_pts_to cp c);
    let res = k cp in
    let _ = gen_elim () in
    elim_context_arrays_pts_to_nil _ _;
    return res

inline_for_extraction
let with_context_arrays_ptr_cons
  (#t1 #t2 #t3: Ghost.erased typ)
  (bi: Ghost.erased (base_context_t true t1 t2))
  (ci: Ghost.erased (context_t true t2 t3))
  (w: with_context_arrays_ptr_t ci)
: Tot (with_context_arrays_ptr_t (CCons bi ci))
= fun #a c kpre tret kpost k ->
  with_local (CACons?.b c) (fun b ->
  with_local (CACons?.sz c) (fun bsz ->
    w
      (CACons?.c c)
      (kpre `star`
        R.pts_to b full_perm (CACons?.b c) `star`
        R.pts_to bsz full_perm (CACons?.sz c))
      tret
      (fun r -> kpost r `star`
        exists_ (R.pts_to b full_perm) `star`
        exists_ (R.pts_to bsz full_perm))
      (fun cp ->
        [@inline_let] // CRITICAL for extraction
        let cp' = CAPCons b bsz cp in
        rewrite
          (R.pts_to b _ _ `star` R.pts_to bsz _ _ `star` context_arrays_pts_to _ _)
          (context_arrays_pts_to cp' c);
        let res = k cp' in
        let _ = gen_elim () in
        let _ = elim_context_arrays_pts_to_cons cp' _ in
        let vb = vpattern_replace_erased (R.pts_to (CAPCons?.b cp') full_perm) in
        rewrite (R.pts_to (CAPCons?.b cp') full_perm _) (R.pts_to b full_perm vb);
        let vsz = vpattern_replace_erased (R.pts_to (CAPCons?.bsz cp') full_perm) in
        rewrite (R.pts_to (CAPCons?.bsz cp') full_perm _) (R.pts_to bsz full_perm vsz);
        let vc = vpattern_replace_erased (context_arrays_pts_to _) in
        rewrite (context_arrays_pts_to _ _) (context_arrays_pts_to cp vc);
        return res
      )
  ))

inline_for_extraction
let load_context_arrays_ptr_t
  (#tfrom #tto: typ)
  (ci: context_t true tfrom tto)
: Tot Type
= (#a: AP.array byte) ->
  (gc: Ghost.erased (context_arrays a)) ->
  (cp: context_arrays_ptr) ->
  (kpre: vprop) ->
  (tret: Type) ->
  (kpost: (tret -> vprop)) ->
  (k: (
    (c: context_arrays a) ->
    ST tret
      (kpre `star` context_arrays_pts_to cp c)
      kpost
      (Ghost.reveal gc == c)
      (fun _ -> True)
  )) ->
  ST tret
    (kpre `star` context_arrays_pts_to cp gc)
    kpost
    (context_arrays_shape ci gc)
    (fun _ -> True)

inline_for_extraction
let load_context_arrays_ptr_nil
  (t: Ghost.erased typ)
: Tot (load_context_arrays_ptr_t (CNil #_ #t))
= fun #a gc cp kpre tret kpost k ->
    elim_context_arrays_pts_to_nil cp gc;
    [@inline_let]
    let c = CANil a in
    intro_context_arrays_pts_to_nil a;
    rewrite (context_arrays_pts_to _ _) (context_arrays_pts_to cp c);
    k c

inline_for_extraction
let load_context_arrays_ptr_cons
  (#t1 #t2 #t3: Ghost.erased typ)
  (bi: Ghost.erased (base_context_t true t1 t2))
  (ci: Ghost.erased (context_t true t2 t3))
  (w: load_context_arrays_ptr_t ci)
: Tot (load_context_arrays_ptr_t (CCons bi ci))
= fun #a gc cp kpre tret kpost k ->
    let _ = elim_context_arrays_pts_to_cons cp gc in
    let b = R.read (CAPCons?.b cp) in
    let sz = R.read (CAPCons?.bsz cp) in
    w
      (CACons?.c gc)
      (CAPCons?.c cp)
      (kpre `star`
        R.pts_to (CAPCons?.b cp) full_perm (CACons?.b gc) `star`
        R.pts_to (CAPCons?.bsz cp) full_perm (CACons?.sz gc))
      tret
      kpost
      (fun c ->
        [@inline_let] // CRITICAL for extraction
        let c' = CACons
          b
          a
          (CACons?.al gc)
          sz
          (CACons?.ar gc)
          ()
          c
        in
        rewrite
          (R.pts_to (CAPCons?.b cp) _ _ `star` R.pts_to (CAPCons?.bsz cp) _ _ `star` context_arrays_pts_to _ _)
          (context_arrays_pts_to cp c');
        k c'
      )

inline_for_extraction
let store_context_arrays_ptr_t
  (#tfrom #tto: typ)
  (ci: context_t true tfrom tto)
: Tot Type
= 
  (cp: context_arrays_ptr) ->
  (#a0: _) ->
  (gc0: Ghost.erased (context_arrays a0)) ->
  (#a: _) ->
  (c: context_arrays a) ->
  ST unit
    (context_arrays_pts_to cp gc0)
    (fun _ -> context_arrays_pts_to cp c)
    (context_arrays_shape ci gc0 /\ context_arrays_shape ci c)
    (fun _ -> True)

inline_for_extraction
let store_context_arrays_ptr_nil
  (t: Ghost.erased typ)
: Tot (store_context_arrays_ptr_t (CNil #_ #t))
= fun cp #a0 gc0 #a c ->
    elim_context_arrays_pts_to_nil cp gc0;
    intro_context_arrays_pts_to_nil a;
    rewrite (context_arrays_pts_to _ _) (context_arrays_pts_to cp c)

inline_for_extraction
let store_context_arrays_ptr_cons
  (#t1 #t2 #t3: Ghost.erased typ)
  (bi: Ghost.erased (base_context_t true t1 t2))
  (ci: Ghost.erased (context_t true t2 t3))
  (w: store_context_arrays_ptr_t ci)
: Tot (store_context_arrays_ptr_t (CCons bi ci))
= fun cp #a0 gc0 #a c ->
  let _ = elim_context_arrays_pts_to_cons cp _ in
  w _ _ (CACons?.c c);
  R.write (CAPCons?.b cp) (CACons?.b c);
  R.write (CAPCons?.bsz cp) (CACons?.sz c);
  intro_context_arrays_pts_to_cons (CAPCons?.b cp) (CAPCons?.bsz cp) (CAPCons?.c cp) (CACons?.b c) (CACons?.a0 c) (CACons?.al c) (CACons?.sz c) (CACons?.ar c) () (CACons?.c c);
  rewrite
    (context_arrays_pts_to _ _)
    (context_arrays_pts_to cp c)

inline_for_extraction
noeq
type hole_arrays_ptr =
{
  hap_hole_b: R.ref byte_array;
  hap_hole_sz: R.ref SZ.size_t;
  hap_context_b: R.ref byte_array;
  hap_context: context_arrays_ptr;
}

[@@__reduce__]
let hole_arrays_pts_to0
  (p: hole_arrays_ptr)
  (a: hole_arrays)
: Tot vprop
= R.pts_to p.hap_hole_b full_perm a.ha_hole_b `star`
  R.pts_to p.hap_hole_sz full_perm a.ha_hole_sz `star`
  R.pts_to p.hap_context_b full_perm a.ha_context_b `star`
  context_arrays_pts_to p.hap_context a.ha_context

let hole_arrays_pts_to
  (p: hole_arrays_ptr)
  (a: hole_arrays)
: Tot vprop
= hole_arrays_pts_to0 p a

inline_for_extraction
let with_hole_arrays_ptr
  (hi: Ghost.erased (hole_t true))
  (w: with_context_arrays_ptr_t hi.context)
  (a: hole_arrays)
  (#kpre: vprop)
  (#tret: Type)
  (#kpost: (tret -> vprop))
  (k: (
    (p: hole_arrays_ptr) ->
    STT tret
      (kpre `star` hole_arrays_pts_to p a)
      (fun r -> kpost r `star` exists_ (hole_arrays_pts_to p))
  ))
: STF tret
    kpre
    kpost
    (context_arrays_shape hi.context a.ha_context)
    (fun _ -> True)
= with_local a.ha_hole_b (fun b ->
  with_local a.ha_hole_sz (fun bsz ->
  with_local a.ha_context_b (fun bcb ->
    w a.ha_context
      (kpre `star`
        R.pts_to b full_perm a.ha_hole_b `star`
        R.pts_to bsz full_perm a.ha_hole_sz `star`
        R.pts_to bcb full_perm a.ha_context_b)
      tret
      (fun r -> kpost r `star`
        exists_ (R.pts_to b full_perm) `star`
        exists_ (R.pts_to bsz full_perm) `star`
        exists_ (R.pts_to bcb full_perm))
      (fun cp ->
        [@inline_let] // CRITICAL for extraction
        let p = {
          hap_hole_b = b;
          hap_hole_sz = bsz;
          hap_context_b = bcb;
          hap_context = cp;
        }
        in
        rewrite
          (R.pts_to b _ _ `star` R.pts_to bsz _ _ `star` R.pts_to bcb _ _ `star` context_arrays_pts_to _ _)
          (hole_arrays_pts_to p a);
        let res = k p in
        let _ = gen_elim () in
        let ga' = vpattern_replace_erased (hole_arrays_pts_to p) in
        rewrite
          (hole_arrays_pts_to p _)
          (R.pts_to b full_perm ga'.ha_hole_b `star` R.pts_to bsz full_perm ga'.ha_hole_sz `star` R.pts_to bcb full_perm ga'.ha_context_b `star` context_arrays_pts_to cp ga'.ha_context);
        return res
      )
  )))

inline_for_extraction
let load_hole_arrays_ptr
  (hi: Ghost.erased (hole_t true))
  (w: load_context_arrays_ptr_t hi.context)
  (gh: Ghost.erased (hole_arrays))
  (hp: hole_arrays_ptr)
  (#kpre: vprop)
  (#tret: Type)
  (#kpost: (tret -> vprop))
  (k: (
    (h: hole_arrays) ->
    ST tret
      (kpre `star` hole_arrays_pts_to hp h)
      kpost
      (Ghost.reveal gh == h)
      (fun _ -> True)
  ))
: STF tret
    (kpre `star` hole_arrays_pts_to hp gh)
    kpost
    (context_arrays_shape hi.context gh.ha_context)
    (fun _ -> True)
= rewrite
    (hole_arrays_pts_to hp gh)
    (hole_arrays_pts_to0 hp gh);
  let b = read_replace hp.hap_hole_b in
  let sz = read_replace hp.hap_hole_sz in
  let cb = read_replace hp.hap_context_b in
  w
    gh.ha_context
    hp.hap_context
    (kpre `star`
      R.pts_to hp.hap_hole_b full_perm b `star`
      R.pts_to hp.hap_hole_sz full_perm sz `star`
      R.pts_to hp.hap_context_b full_perm cb)
    tret
    kpost
    (fun c ->
      [@inline_let] // CRITICAL for extraction
      let h = {
        ha_hole_a = gh.ha_hole_a;
        ha_hole_b = b;
        ha_hole_sz = sz;
        ha_context_a = gh.ha_context_a;
        ha_context_b = cb;
        ha_context = c;
        ha_prf = gh.ha_prf;
      }
      in
      rewrite
        (R.pts_to hp.hap_hole_b _ _ `star` R.pts_to hp.hap_hole_sz _ _ `star` R.pts_to hp.hap_context_b _ _ `star` context_arrays_pts_to _ _)
        (hole_arrays_pts_to hp h);
      k h
    )

inline_for_extraction
let store_hole_arrays_ptr
  (hi: Ghost.erased (hole_t true))
  (w: store_context_arrays_ptr_t hi.context)
  (hp: hole_arrays_ptr)
  (gh0: Ghost.erased hole_arrays)
  (h: hole_arrays)
: ST unit
    (hole_arrays_pts_to hp gh0)
    (fun _ -> hole_arrays_pts_to hp h)
    (context_arrays_shape hi.context gh0.ha_context /\ context_arrays_shape hi.context h.ha_context)
    (fun _ -> True)
= rewrite
    (hole_arrays_pts_to hp gh0)
    (hole_arrays_pts_to0 hp gh0);
  R.write hp.hap_hole_b h.ha_hole_b;
  R.write hp.hap_hole_sz h.ha_hole_sz;
  R.write hp.hap_context_b h.ha_context_b;
  w hp.hap_context gh0.ha_context h.ha_context;
  rewrite
    (hole_arrays_pts_to0 hp h)
    (hole_arrays_pts_to hp h)

let run_prog_post_true_prop
  (#root: typ)
  (#ret_t: Type)
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t (initial_ser_index root) (final_ser_index root))
  (vbin: v pkind (type_of_typ ty))
  (vbout: AP.v byte)
  (vl': AP.v byte)
  (vret' : ret_t)
  (vsz' : SZ.size_t)
  (vr': v pkind (type_of_typ root))
: Tot prop
=
  let (vr, s') = sem ser_action_sem p vbin.contents (initial_ser_state root) in
  let HVValue _ v' = s'.hole in
  vr == vret' /\
  AP.merge_into (AP.array_of vl') (array_of' vr') (AP.array_of vbout) /\
  SZ.size_v vsz' == AP.length (AP.array_of vl') /\
  vr'.contents == v'

[@@__reduce__]
let run_prog_post_true
  (#root: typ)
  (#ret_t: Type)
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t (initial_ser_index root) (final_ser_index root))
  (vbin: _)
  (vbout: AP.v byte)
  (bin: byte_array)
  (bout: byte_array)
  (bret: R.ref ret_t)
  (bsz: R.ref SZ.size_t)
: Tot vprop
=
      exists_ (fun vl' -> exists_ (fun vret' -> exists_ (fun vsz' ->
        aparse (parser_of_typ ty) bin vbin `star`
        AP.arrayptr bout vl' `star`
        R.pts_to bret full_perm vret' `star`
        R.pts_to bsz full_perm vsz' `star`
        (
            exists_ (fun br' -> exists_ (fun vr' ->
              aparse (parser_of_typ root) br' vr' `star`
              pure (
                run_prog_post_true_prop p vbin vbout vl' vret' vsz' vr'
              )
            ))
        )
      )))

let run_prog_post_false_prop
  (#root: typ)
  (#ret_t: Type)
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t (initial_ser_index root) (final_ser_index root))
  (vbin: v pkind (type_of_typ ty))
  (vbout: AP.v byte)
  (vl' : AP.v byte)
  (vsz' : SZ.size_t)
: Tot prop
=
  let (_, s') = sem ser_action_sem p vbin.contents (initial_ser_state root) in
  let HVValue _ v' = s'.hole in
  AP.array_of vl' == AP.array_of vbout /\
  SZ.size_v vsz' == AP.length (AP.array_of vbout) /\
  chunk_exceeds_limit (parse_some_chunk (parser_of_typ root) v') (SZ.size_v vsz')

[@@__reduce__]
let run_prog_post_false
  (#root: typ)
  (#ret_t: Type)
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t (initial_ser_index root) (final_ser_index root))
  (vbin: _)
  (vbout: AP.v byte)
  (bin: byte_array)
  (bout: byte_array)
  (bret: R.ref ret_t)
  (bsz: R.ref SZ.size_t)
: Tot vprop
=
      exists_ (fun vl' -> exists_ (fun vret' -> exists_ (fun vsz' ->
        aparse (parser_of_typ ty) bin vbin `star`
        AP.arrayptr bout vl' `star`
        R.pts_to bret full_perm vret' `star`
        R.pts_to bsz full_perm vsz' `star`
        (
            pure (
              run_prog_post_false_prop p vbin vbout vl' vsz'
            )
        )
      )))

let run_prog_post
  (#root: typ)
  (#ret_t: Type)
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t (initial_ser_index root) (final_ser_index root))
  (vbin: _)
  (vbout: AP.v byte)
  (bin: byte_array)
  (bout: byte_array)
  (bret: R.ref ret_t)
  (bsz: R.ref SZ.size_t)
  (b: bool)
: Tot vprop
= if b
  then run_prog_post_true p vbin vbout bin bout bret bsz
  else run_prog_post_false p vbin vbout bin bout bret bsz

let get_final_state_value
  (ty: typ)
  (h: ser_state (final_ser_index ty))
: Tot (type_of_typ ty)
= HVValue?.v h.hole

#push-options "--z3rlimit 64 --split_queries"
#restart-solver

inline_for_extraction
[@@noextract_to "krml"]
let run_prog
  (#root: typ)
  (#ret_t: Type)
  (#ty: typ)
  (#p: prog ser_state ser_action ty ret_t (initial_ser_index root) (final_ser_index root))
  (i: prog_impl_t p)
  ()
  (#vbin: _)
  (#vbout: AP.v byte)
  (#vret: Ghost.erased ret_t)
  (#vsz: Ghost.erased SZ.size_t)
  (bin: byte_array)
  (bout: byte_array)
  (bret: R.ref ret_t)
  (bsz: R.ref SZ.size_t)
: ST bool
    (aparse (parser_of_typ ty) bin vbin `star`
      AP.arrayptr bout vbout `star`
      R.pts_to bret full_perm vret `star`
      R.pts_to bsz full_perm vsz)
    (fun b ->
      run_prog_post p vbin vbout bin bout bret bsz b)
    (
      SZ.size_v vsz == AP.length (AP.array_of vbout) /\
      AP.array_perm (AP.array_of vbout) == full_perm
    )
    (fun _ -> True)
=
  assert (default_parser_kind `is_weaker_than` parse_ret_kind);
  assert (default_parser_kind `is_weaker_than` pkind);
  let sz = R.read bsz in
  let br_hole = AP.split bout sz in
  let _ = gen_elim () in
  let br_ctxt = AP.split br_hole SZ.zero_size in
  let _ = gen_elim () in
  let ac = intro_empty_chunk empty_chunk br_ctxt in
  intro_parse_context_arrays_nil root br_ctxt _;
  parse_some_chunk_empty_weaken default_parser_kind;
  let ah = intro_empty_chunk (parse_some_chunk (weaken default_parser_kind parse_empty) ()) br_hole in
  [@@inline_let]
  let h =
    {
      ha_hole_a = ah;
      ha_hole_b = br_hole;
      ha_hole_sz = SZ.zero_size;
      ha_context_a = ac;
      ha_context_b = br_ctxt;
      ha_context = CANil _;
      ha_prf = ();
    }
  in
  let s' : Ghost.erased (ser_state (final_ser_index root)) = Ghost.hide (
    sndp (sem ser_action_sem p vbin.contents (initial_ser_state root))
  )
  in
  let v' : Ghost.erased (type_of_typ root) = Ghost.hide (get_final_state_value root s') in
  rewrite
    (array_chunk _ br_hole _ `star` parse_context_arrays _ br_ctxt _)
    (parse_hole_arrays (initial_ser_state root) h);
  with_local true (fun bres ->
  i
    bin
    bout
    sz
    h
    (initial_ser_state root)
    (
      R.pts_to bres full_perm true `star`
      R.pts_to bret full_perm vret `star`
      R.pts_to bsz full_perm vsz
    )
    (exists_ (fun b ->
      R.pts_to bres full_perm b `star`
      run_prog_post p vbin vbout bin bout bret bsz b
    ))
    (fun vl' sz' h' _ v ->
      let bh = h'.ha_hole_b in
      let ah = h'.ha_hole_a in
      let bc = Ghost.hide h'.ha_context_b in
      let c = Ghost.hide h'.ha_context in
      rewrite
        (parse_hole_arrays _ h')
        (array_chunk (parse_some_chunk (weaken default_parser_kind (parser_of_typ root)) v') bh ah `star` parse_context_arrays (CNil #_ #root) bc c);
      let _ = elim_parse_some_chunk _ _ bh in
      let _ = rewrite_aparse bh (parser_of_typ root) in
      let _ = elim_parse_context_arrays_nil _ bc _ in
      let _ = elim_empty_chunk _ bc in
      let vh1 = elim_aparse _ bh in
      let vh2 = AP.join bh bc in
      Seq.append_empty_r (AP.contents_of' vh1);
      let _ = intro_aparse (parser_of_typ root) bh in
      R.write bret v;
      R.write bsz sz';
      R.write bres true;
      rewrite
        (run_prog_post_true p vbin vbout bin bout bret bsz)
        (run_prog_post p vbin vbout bin bout bret bsz true);
      return ()
    )
    (fun vb' ->
      let f () : Lemma (chunk_exceeds_limit (parse_some_chunk (parser_of_typ root) v') (SZ.size_v sz)) =
        chunk_desc_ge_zero_r (parse_some_chunk (weaken default_parser_kind (parser_of_typ root)) v') empty_chunk;
        chunk_desc_ge_intro_exact_parse_some_chunk
          (parser_of_typ root)
          (weaken default_parser_kind (parser_of_typ root))
          v';
        chunk_desc_ge_implies
          (parse_some_chunk (parser_of_typ root) v')
          (parse_hole s')
          (SZ.size_v sz)
      in
      f ();
      R.write bres false;
      rewrite
        (run_prog_post_false p vbin vbout bin bout bret bsz)
        (run_prog_post p vbin vbout bin bout bret bsz false);
      return ()
    );
  let _ = gen_elim () in
  let res = R.read bres in
  rewrite
    (run_prog_post p vbin vbout bin bout bret bsz _)
    (run_prog_post p vbin vbout bin bout bret bsz res);
  return res
  )

#pop-options

let ser_action_sem_chunk_desc_ge
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (a: ser_action ret_t pre post)
  (s: ser_state pre)
: Lemma
  (ensures (
    let (_, s') = ser_action_sem a s in
    parse_hole s' `chunk_desc_ge` parse_hole s
  ))
= admit ()

let rec fold_list_chunk_desc_ge
  (#root: typ)
  (#inv: ser_index root)
  (#t: Type)
  (f: fold_t ser_state t unit inv inv)
  (prf: (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = f i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
  (input: list t)
  (s: ser_state inv)
: Lemma
  (ensures (
    let (v, s') = fold_list inv f input s in
    parse_hole s' `chunk_desc_ge` parse_hole s
  ))
  (decreases input)
= match input with
  | [] -> ()
  | hd :: tl ->
    prf hd s;
    let (_, s') = f hd s in
    fold_list_chunk_desc_ge f prf tl s'

let rec fold_for_chunk_desc_ge
  (#root: typ)
  (#inv: ser_index root)
  (#t: Type)
  (from: nat) (to: nat)
  (f: (x: nat { from <= x /\ x < to }) -> fold_t ser_state t unit inv inv)
  (prf: (x: nat { from <= x /\ x < to }) -> (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = f x i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
  (input: t)
  (s: ser_state inv)
: Lemma
  (ensures (
    let (v, s') = fold_for inv from to f input s in
    parse_hole s' `chunk_desc_ge` parse_hole s
  ))
  (decreases (if to <= from then 0 else to - from + 1))
= if from >= to
  then ()
  else begin
    let (_, s') = f from input s in
    prf from input s;
    fold_for_chunk_desc_ge (from + 1) to f prf input s'
  end

let fold_for_list_chunk_desc_ge
  (#root: typ)
  (#inv: ser_index root)
  (#t: Type)
  (f: fold_t ser_state t unit inv inv)
  (idx: (n: nat) -> (i: nat { i < n }) -> Tot (i: nat { i < n }))
  (prf: (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = f i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
  (input: list t)
  (s: ser_state inv)
: Lemma
  (ensures (
    let (v, s') = fold_for_list inv f idx input s in
    parse_hole s' `chunk_desc_ge` parse_hole s
  ))
=
  let n = List.Tot.length input in
  fold_for_chunk_desc_ge 0 (n)
    (fold_list_index_of inv f n (idx n))
    (fun x (i: nlist n t) s -> prf (List.Tot.index i (idx n x)) s)
    input s

#push-options "--z3rlimit 32"
#restart-solver

let rec prog_sem_chunk_desc_ge
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#ty: typ)
  (p: prog ser_state ser_action ty ret_t pre post)
  (input: type_of_typ ty)
  (s: ser_state pre)
: Lemma
  (ensures (
    let (_, s') = sem ser_action_sem p input s in
    parse_hole s' `chunk_desc_ge` parse_hole s
  ))
  (decreases p)
= match p with
  | PRet _ -> ()
  | PAction a ->
    ser_action_sem_chunk_desc_ge a s
  | PBind f g ->
    prog_sem_chunk_desc_ge f input s;
    let (v1, s1) = sem ser_action_sem f input s in
    prog_sem_chunk_desc_ge (g v1) input s1
  | PU8 _ -> ()
  | PPair #_ #_ #_ #t1 #t2 f1 f2 ->
    let (input1, input2) = (input <: type_of_typ (TPair t1 t2)) in
    prog_sem_chunk_desc_ge f1 input1 s;
    let (v1, s1) = sem ser_action_sem f1 input1 s in
    prog_sem_chunk_desc_ge (f2 v1) input2 s1
  | PList i f ->
    fold_list_chunk_desc_ge
      (sem ser_action_sem f)
      (fun i s -> prog_sem_chunk_desc_ge f i s)
      input
      s
  | PListFor i idx f ->
    fold_for_list_chunk_desc_ge
      (sem ser_action_sem f)
      idx.array_index_f_nat
      (fun i s -> prog_sem_chunk_desc_ge f i s)
      input
      s
  | PChoice #_ #_ #_ #t f ->
    let (| tag, payload |) = (input <: type_of_typ (TChoice t)) in
    prog_sem_chunk_desc_ge (f tag) payload s

#pop-options

inline_for_extraction
[@@noextract_to "krml"]
let impl_bind
  (#root: typ)
  (#t: typ)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: prog (ser_state #root) ser_action t ret1 pre1 post1)
  (impl_f: prog_impl_t f)
  (g: ((x: ret1) -> prog ser_state ser_action t ret2 post1 post2))
  (impl_g: ((x: ret1) -> prog_impl_t (g x)))
: Tot (prog_impl_t (PBind f g))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  impl_f
    bin bout sz out h kpre kpost
    (fun vl1 sz1 out1 h1 v1 ->
      impl_g v1
        bin bout sz1 out1 h1 kpre kpost
        (fun vl2 sz2 out2 h2 v2 ->
          k_success vl2 sz2 out2 h2 v2
        )
        (fun vb' ->
          k_failure vb'
        )
    )
    (fun vb' ->
      let f () : Lemma
      (
        let (_, h') = sem ser_action_sem (PBind f g) vbin.contents h in
        parse_hole h' `chunk_exceeds_limit` AP.length (AP.array_of vb')
      ) =
        let (_, h') = sem ser_action_sem (PBind f g) vbin.contents h in
        let (v1, h1) = sem ser_action_sem f vbin.contents h in
        prog_sem_chunk_desc_ge (g v1) vbin.contents h1;
        chunk_desc_ge_implies (parse_hole h') (parse_hole h1) (AP.length (AP.array_of vb'))
      in
      f ();
      k_failure vb'
    )

inline_for_extraction
[@@noextract_to "krml"]
let impl_ret
  (#root: typ)
  (#ret_t: Type)
  (#i: ser_index root)
  (#t: typ)
  (v: ret_t)
: Tot (prog_impl_t (PRet #_ #_ #_ #ret_t #i #t v))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  k_success vl sz out h v

inline_for_extraction
[@@noextract_to "krml"]
let impl_u8
  (#root: typ)
  (i: ser_index root)
: Tot (prog_impl_t (PU8 #_ #_ #_ i))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  let _ = rewrite_aparse bin parse_u8 in
  let w = read_u8 bin in
  let vbin' = rewrite_aparse bin (parser_of_typ TU8) in
  rewrite (aparse _ bin _) (aparse (parser_of_typ TU8) bin vbin);
  k_success vl sz out h w

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
[@@noextract_to "krml"]
let impl_pair
  (#root: typ)
  (#t1: typ)
  (#t2: typ)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (f1: prog (ser_state #root) ser_action t1 ret1 pre1 post1)
  (impl_f1: prog_impl_t f1)
  (j1: jumper (parser_of_typ t1)) // MUST be computed OUTSIDE of impl_pair
  (#ret2: _)
  (#post2: _)
  (f2: ((x: ret1) -> prog ser_state ser_action t2 ret2 post1 post2))
  (impl_f2: ((x: ret1) -> prog_impl_t (f2 x)))
: Tot (prog_impl_t (PPair f1 f2))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  let _ = rewrite_aparse bin (nondep_then (parser_of_typ t1) (parser_of_typ t2)) in
  let bin2 = split_pair j1 (parser_of_typ t2) bin in
  let _ = gen_elim () in
  let vbin1 = vpattern_replace (aparse (parser_of_typ t1) bin) in
  let vbin2 = vpattern_replace (aparse (parser_of_typ t2) bin2) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parser_of_typ t1) bin vbin1 `star` aparse (parser_of_typ t2) bin2 vbin2)
    (fun _ -> aparse (parser_of_typ (TPair t1 t2)) bin vbin)
  =
    let _ = merge_pair (parser_of_typ t1) (parser_of_typ t2) bin bin2 in
    let vbin' = rewrite_aparse bin (parser_of_typ (TPair t1 t2)) in
    rewrite (aparse _ bin vbin') (aparse (parser_of_typ (TPair t1 t2)) bin vbin)
  in
  impl_f1
    bin bout sz out h (kpre `star` aparse (parser_of_typ t2) bin2 vbin2) kpost
    (fun vl1 sz1 out1 h1 v1 ->
      impl_f2 v1
        bin2 bout sz1 out1 h1 (kpre `star` aparse (parser_of_typ t1) bin vbin1) kpost
        (fun vl2 sz2 out2 h2 v2 ->
          restore ();
          k_success vl2 sz2 out2 h2 v2
        )
        (fun vb' ->
          restore ();
          k_failure vb'
        )
    )
    (fun vb' ->
      restore ();
      let f () : Lemma
      (
        let (_, h') = sem ser_action_sem (PPair f1 f2) vbin.contents h in
        parse_hole h' `chunk_exceeds_limit` AP.length (AP.array_of vb')
      ) =
        let (_, h') = sem ser_action_sem (PPair f1 f2) vbin.contents h in
        let (v1, h1) = sem ser_action_sem f1 (fst vbin.contents) h in
        prog_sem_chunk_desc_ge (f2 v1) (snd vbin.contents) h1;
        chunk_desc_ge_implies (parse_hole h') (parse_hole h1) (AP.length (AP.array_of vb'))
      in
      f ();
      k_failure vb'
    )

#pop-options

let parser_of_choice_payload
  (t: (bool -> typ))
  (x: bool)
: Tot (parser pkind (type_of_typ (t x)))
= parser_of_typ (t x)

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
[@@noextract_to "krml"]
let impl_choice
  (#root: typ)
  (#t: (bool -> typ))
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (f: (x: bool) -> prog (ser_state #root) ser_action (t x) ret_t pre post)
  (impl_f1: (x: bool) -> prog_impl_t (f x))
: Tot (prog_impl_t (PChoice f))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  rewrite_with_tactic (aparse (parser_of_typ (TChoice t)) bin vbin) (aparse (weaken pkind (parse_dtuple2 parse_bool (parser_of_choice_payload t))) bin vbin);
  let _ = rewrite_aparse bin (parse_dtuple2 parse_bool (parser_of_choice_payload t)) in
  let bin_pl = split_dtuple2
    (jump_constant_size parse_bool (SZ.mk_size_t 1ul))
    (parser_of_choice_payload t)
    bin
  in
  let tag = read_dtuple2_tag read_bool (parser_of_choice_payload t) bin bin_pl in
  let _ = gen_elim () in
  let vbin_tag = vpattern_replace (aparse parse_bool bin) in
  let vbin_pl = rewrite_aparse bin_pl (parser_of_typ (t tag)) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse parse_bool bin vbin_tag `star` aparse (parser_of_typ (t tag)) bin_pl vbin_pl)
    (fun _ -> aparse (parser_of_typ (TChoice t)) bin vbin)
  =
    let _ = intro_dtuple2 parse_bool (parser_of_choice_payload t) bin bin_pl in
    let vbin' = rewrite_aparse bin (weaken pkind (parse_dtuple2 parse_bool (parser_of_choice_payload t))) in
    rewrite_with_tactic (aparse (weaken pkind (parse_dtuple2 parse_bool (parser_of_choice_payload t))) bin vbin') (aparse (parser_of_typ (TChoice t)) bin vbin');
    rewrite (aparse (parser_of_typ (TChoice t)) bin vbin') (aparse (parser_of_typ (TChoice t)) bin vbin)
  in
  impl_f1 tag
    bin_pl bout sz out h (kpre `star` aparse parse_bool bin vbin_tag) kpost
    (fun vl1 sz1 out1 h1 v1 ->
      restore ();
      k_success vl1 sz1 out1 h1 v1
    )
    (fun vb' ->
      restore ();
      k_failure vb'
    )

#pop-options

module GR = Steel.ST.GhostReference

unfold
let impl_for_inv_true_prop0
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t ser_state t unit inv inv))
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (from: SZ.size_t)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (h: ser_state inv)
  (out: hole_arrays)
  (cont: bool)
: Tot prop
=
  SZ.size_v vout_sz == AP.length (AP.array_of vout) /\
  AP.array_perm (AP.array_of vout) == full_perm /\
  AP.merge_into (AP.array_of vout) (array_of_hole out) a0 /\
  SZ.size_v from0 <= SZ.size_v from /\
  fold_for inv (SZ.size_v from0) (SZ.size_v (if SZ.size_v from <= SZ.size_v to then from else to)) f l h0 == ((), h) /\
  (cont == (SZ.size_v from < SZ.size_v to))

let impl_for_inv_true_prop
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t ser_state t unit inv inv))
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (from: SZ.size_t)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (h: ser_state inv)
  (out: hole_arrays)
  (cont: bool)
: Tot prop
= impl_for_inv_true_prop0 inv from0 to f l a0 h0 from vout vout_sz h out cont

[@@__reduce__]
let impl_for_inv_aux_true
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t ser_state t unit inv inv))
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (cont: bool)
: Tot vprop
= exists_ (fun (h: ser_state inv) ->
    parse_hole_arrays h out `star`
    pure (
      impl_for_inv_true_prop inv from0 to f l a0 h0 from vout vout_sz h out cont
    )
  )

let fold_for_loop_body
  #state_i (state_t: _)
  (inv: state_i)
  (t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
: Tot Type
= Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv)

let impl_for_inv_aux_false_prop
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (cont: bool)
  (from: SZ.size_t)
: Tot prop
=
    SZ.size_v from0 <= SZ.size_v from /\ SZ.size_v from <= SZ.size_v to /\
    chunk_exceeds_limit (parse_hole (sndp (fold_for inv (SZ.size_v from0) (SZ.size_v from) f l h0))) (AP.length a0) /\
    cont == false /\
    AP.array_of vout == a0

[@@__reduce__]
let impl_for_inv_aux_false0
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (cont: bool)
  (from: SZ.size_t)
: Tot vprop
=
  pure (impl_for_inv_aux_false_prop inv from0 to f l a0 h0 vout cont from)

let impl_for_inv_aux_false
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (cont: bool)
: (from: SZ.size_t) ->
  Tot vprop
=
  impl_for_inv_aux_false0 inv from0 to f l a0 h0 vout cont

let intro_impl_for_inv_aux_false
  (#opened: _)
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (cont: bool)
  (from: SZ.size_t)
: STGhost unit opened
    emp
    (fun _ -> impl_for_inv_aux_false inv from0 to f l a0 h0 vout cont from)
    (impl_for_inv_aux_false_prop inv from0 to f l a0 h0 vout cont from)
    (fun _ -> True)
= noop ();
  rewrite
    (impl_for_inv_aux_false0 inv from0 to f l a0 h0 vout cont from)
    (impl_for_inv_aux_false inv from0 to f l a0 h0 vout cont from)

let impl_for_inv_aux
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: Tot vprop
= if no_interrupt
  then impl_for_inv_aux_true inv from0 to f l a0 h0 vout vout_sz out from cont
  else exists_ (impl_for_inv_aux_false inv from0 to f l a0 h0 vout cont)

let intro_impl_for_inv_aux_true
  (#opened: _)
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (cont: bool)
  (h: ser_state inv)
: STGhost unit opened
    (parse_hole_arrays h out)
    (fun _ -> impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from true cont)
    (impl_for_inv_true_prop inv from0 to f l a0 h0 from vout vout_sz h out cont)
    (fun _ -> True)
= intro_pure (
    impl_for_inv_true_prop inv from0 to f l a0 h0 from vout vout_sz h out cont
  );
  rewrite
    (impl_for_inv_aux_true inv from0 to f l a0 h0 vout vout_sz out from cont)
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from true cont)

let elim_impl_for_inv_aux_true
  (#opened: _)
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost (Ghost.erased (ser_state inv)) opened
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (fun h -> parse_hole_arrays h out)
    (no_interrupt == true)
    (fun h -> impl_for_inv_true_prop inv from0 to f l a0 h0 from vout vout_sz h out cont)
= 
  rewrite
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (impl_for_inv_aux_true inv from0 to f l a0 h0 vout vout_sz out from cont);
  let gh = elim_exists () in
  let _ = gen_elim () in
  gh

let elim_impl_for_inv_aux_false
  (#opened: _)
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost (Ghost.erased SZ.size_t) opened
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (fun _ -> emp)
    (no_interrupt == false)
    (fun from ->
      impl_for_inv_aux_false_prop inv from0 to f l a0 h0 vout cont from
    )
=
  rewrite
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (exists_ (impl_for_inv_aux_false0 inv from0 to f l a0 h0 vout cont));
  let gfrom = elim_exists () in
  let _ = gen_elim () in
  gfrom

let impl_for_inv_aux_cont_true
  (#opened: _)
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost unit opened
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (fun _ -> impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (cont == true)
    (fun h -> no_interrupt == true)
= if no_interrupt
  then noop ()
  else begin
    let _ = elim_impl_for_inv_aux_false _ _ _ _ _ _ _ _ _ _ _ _ _ in
    rewrite // by contradiction
      emp
      (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
  end

[@@__reduce__]
let impl_for_inv0
  (#root: typ)
  (inv: ser_index root)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (bin: byte_array)
  (vl: v k t)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (cont: bool)
: Tot vprop
= exists_ (fun vout -> exists_ (fun vout_sz -> exists_ (fun out -> exists_ (fun from -> exists_ (fun no_interrupt ->
    aparse p bin vl `star`
    AP.arrayptr bout vout `star`
    R.pts_to bout_sz full_perm vout_sz `star`
    hole_arrays_pts_to bh out `star`
    R.pts_to bfrom full_perm from `star`
    R.pts_to b_no_interrupt full_perm no_interrupt `star`
    R.pts_to bcont full_perm cont `star`
    impl_for_inv_aux inv from0 to f vl.contents a0 h0 vout vout_sz out from no_interrupt cont
  )))))

let impl_for_inv
  (#root: typ)
  (inv: ser_index root)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (bin: byte_array)
  (vl: v k t)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (cont: bool)
: Tot vprop
= impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont cont

inline_for_extraction
let impl_for_test
  (#root: typ)
  (inv: ser_index root)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (bin: byte_array)
  (vl: v k t)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (_: unit)
: STT bool
    (exists_ (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont))
    (fun cont -> impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont cont)
= let gcont = elim_exists () in
  rewrite
    (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont gcont)
    (impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont gcont);
  let _ = gen_elim () in
  let cont = R.read bcont in
  rewrite
    (impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont gcont)
    (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont cont);
  return cont

let rec fold_for_snoc_nat
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from0 to: nat)
  (f: (x: nat { from0 <= x /\ x < to }) -> fold_t state_t t unit inv inv)
  (from: nat)
  (i: t)
  (s: state_t inv)
: Lemma
  (requires (from0 <= from /\ from < to))
  (ensures (
    let (_, s1) = fold_for inv from0 from f i s in
    fold_for inv from0 (from + 1) f i s == Ghost.reveal f (from) i s1
  ))
  (decreases (from - from0))
= if from = from0
  then ()
  else
    let (_, s1) = Ghost.reveal f from0 i s in
    fold_for_snoc_nat inv (from0 + 1) to f from i s1

let fold_for_snoc
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body state_t inv t from0 to)
  (from: SZ.size_t)
  (i: t)
  (s: state_t inv)
: Lemma
  (requires (SZ.size_v from0 <= SZ.size_v from /\ SZ.size_v from < SZ.size_v to))
  (ensures (
    let (_, s1) = fold_for inv (SZ.size_v from0) (SZ.size_v from) f i s in
    fold_for inv (SZ.size_v from0) (SZ.size_v from + 1) f i s == Ghost.reveal f (SZ.size_v from) i s1
  ))
= fold_for_snoc_nat inv (SZ.size_v from0) (SZ.size_v to) f (SZ.size_v from) i s

inline_for_extraction
let impl_for_body
  (#root: typ)
  (inv: ser_index root)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (bin: byte_array)
  (vl: v k t)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (fi: (x: SZ.size_t { SZ.size_v from0 <= SZ.size_v x /\ SZ.size_v x < SZ.size_v to }) -> fold_impl_t p (Ghost.reveal f (SZ.size_v x)))
  (wl: load_context_arrays_ptr_t inv.context)
  (ws: store_context_arrays_ptr_t inv.context)
  (_: unit)
: STT unit
    (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont true)
    (fun _ -> exists_ (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont))
=
  rewrite
    (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont true)
    (impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont true);
  let _ = gen_elim () in
  impl_for_inv_aux_cont_true _ _ _ _ _ _ _ _ _ _ _ _ _;
  vpattern_rewrite (R.pts_to b_no_interrupt full_perm) true;
  let _ = elim_impl_for_inv_aux_true _ _ _ _ _ _ _ _ _ _ _ _ _ in
  parse_hole_arrays_context_arrays_shape _ _;
  let from1 = read_replace bfrom in
  let sz1 = read_replace bout_sz in
  let from2 = SZ.size_add from1 SZ.one_size in
  fold_for_snoc inv from0 to f from1 vl.contents h0;
  load_hole_arrays_ptr inv wl _ bh (fun out1 ->
    vpattern_rewrite (parse_hole_arrays _) out1;
    fi from1 bin bout sz1 out1 _
      (
        R.pts_to bfrom full_perm from1 `star`
        R.pts_to bout_sz full_perm sz1 `star`
        R.pts_to b_no_interrupt full_perm true `star`
        R.pts_to bcont full_perm true `star`
        hole_arrays_pts_to bh out1
      )
      (exists_ (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont))
      (fun vout2 sz2 out2 h2 _ ->
        R.write bfrom from2;
        R.write bout_sz sz2;
        parse_hole_arrays_context_arrays_shape _ _;
        store_hole_arrays_ptr inv ws bh _ out2;
        let cont2 = from2 `SZ.size_lt` to in
        R.write bcont cont2;
        intro_impl_for_inv_aux_true inv from0 to f vl.contents a0 h0 vout2 sz2 out2 from2 cont2 h2;
        rewrite
          (impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont cont2)
          (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont cont2);        
        noop ()
      )
      (fun vb' ->
        R.write b_no_interrupt false;
        R.write bcont false;
        intro_impl_for_inv_aux_false inv from0 to f vl.contents a0 h0 vb' false from2;
        rewrite
          (exists_ (impl_for_inv_aux_false inv from0 to f vl.contents a0 h0 vb' false))
          (impl_for_inv_aux inv from0 to f vl.contents a0 h0 vb' sz1 out1 from1 false false);
        rewrite
          (impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont false)
          (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont false);
        noop ()
      )
  )

let rec impl_for_inv_aux_false_prop_chunk_exceeds_limit
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (from: SZ.size_t)
  (prf: (x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = Ghost.reveal f x i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
: Lemma
  (requires (
    SZ.size_v from0 <= SZ.size_v from /\ SZ.size_v from <= SZ.size_v to /\
    chunk_exceeds_limit (parse_hole (sndp (fold_for inv (SZ.size_v from0) (SZ.size_v from) f l h0))) (AP.length a0)
  ))
  (ensures (
    chunk_exceeds_limit (parse_hole (sndp (fold_for inv (SZ.size_v from0) (SZ.size_v to) f l h0))) (AP.length a0)
  ))
  (decreases (SZ.size_v to - SZ.size_v from))
= if SZ.size_v to = SZ.size_v from
  then ()
  else begin
    fold_for_snoc inv from0 to f from l h0;
    let (_, h1) = fold_for inv (SZ.size_v from0) (SZ.size_v from) f l h0 in
    prf (SZ.size_v from) l h1;
    let from' = SZ.size_add from SZ.one_size in
    let (_, h2) = fold_for inv (SZ.size_v from0) (SZ.size_v from') f l h0 in
    chunk_desc_ge_implies
      (parse_hole h2)
      (parse_hole h1)
      (AP.length a0);
    impl_for_inv_aux_false_prop_chunk_exceeds_limit inv from0 to f l a0 h0 vout (SZ.size_add from SZ.one_size) prf
  end

let elim_impl_for_inv_aux_false_strong
  (#opened: _)
  (#root: typ)
  (inv: ser_index root)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (prf: (x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = Ghost.reveal f x i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
  (l: t)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (out: hole_arrays)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost (Ghost.erased SZ.size_t) opened
    (impl_for_inv_aux inv from0 to f l a0 h0 vout vout_sz out from no_interrupt cont)
    (fun _ -> emp)
    (no_interrupt == false)
    (fun from ->
      impl_for_inv_aux_false_prop inv from0 to f l a0 h0 vout cont from /\
      chunk_exceeds_limit (parse_hole (sndp (fold_for inv (SZ.size_v from0) (SZ.size_v to) f l h0))) (AP.length a0)
    )
= let gfrom = elim_impl_for_inv_aux_false _ _ _ _ _ _ _ _ _ _ _ _ _ in
  impl_for_inv_aux_false_prop_chunk_exceeds_limit inv from0 to f l a0 h0 vout gfrom prf;
  gfrom

inline_for_extraction
let impl_for_post
  (#root: typ)
  (inv: ser_index root)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: fold_for_loop_body ser_state inv t from0 to)
  (bin: byte_array)
  (vl: v k t)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (vl0: AP.v byte)
  (out0: hole_arrays)
  (kpre kpost: vprop)
  (k_success: (
    (vl': AP.v byte) ->
    (sz': SZ.size_t) ->
    (out': hole_arrays) ->
    (h': Ghost.erased (ser_state inv)) ->
    (v: unit) ->
    ST unit
      (kpre `star` aparse p bin vl `star`
        AP.arrayptr bout vl' `star` parse_hole_arrays h' out')
      (fun _ -> kpost)
      (
        AP.adjacent (AP.array_of vl0) (array_of_hole out0) /\
        AP.merge_into (AP.array_of vl') (array_of_hole out') (AP.merge (AP.array_of vl0) (array_of_hole out0)) /\
        fold_for inv (SZ.size_v from0) (SZ.size_v to) f vl.contents h0 == (v, Ghost.reveal h') /\
        SZ.size_v sz' == AP.length (AP.array_of vl')
      )
      (fun _ -> True)
  ))
  (k_failure: (
    (vb': AP.v byte) ->
    ST unit
      (kpre `star` aparse p bin vl `star` AP.arrayptr bout vb')
      (fun _ -> kpost)
      (
        let (_, h') = fold_for inv (SZ.size_v from0) (SZ.size_v to) f vl.contents h0 in
        AP.merge_into (AP.array_of vl0) (array_of_hole out0) (AP.array_of vb') /\
        chunk_exceeds_limit (parse_hole h') (AP.length (AP.array_of vb'))
      )
      (fun _ -> True)
  ))
  (prf: (x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = Ghost.reveal f x i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
  (wl: load_context_arrays_ptr_t inv.context)
: ST unit
    (kpre `star` impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont false)
    (fun _ -> kpost `star`
      exists_ (R.pts_to bout_sz full_perm) `star`
      exists_ (hole_arrays_pts_to bh) `star`
      exists_ (R.pts_to bfrom full_perm) `star`
      exists_ (R.pts_to b_no_interrupt full_perm) `star`
      exists_ (R.pts_to bcont full_perm)
    )
    (AP.merge_into (AP.array_of vl0) (array_of_hole out0) a0)
    (fun _ -> True)
=
    rewrite
      (impl_for_inv inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont false)
      (impl_for_inv0 inv p from0 to f bin vl bout bout_sz bh a0 h0 bfrom b_no_interrupt bcont false);
    let _ = gen_elim () in
    let no_interrupt = read_replace b_no_interrupt in
    if no_interrupt
    then begin
      let h' = elim_impl_for_inv_aux_true _ _ _ _ _ _ _ _ _ _ _ _ _ in
      parse_hole_arrays_context_arrays_shape _ _;
      let sz' = read_replace bout_sz in
      load_hole_arrays_ptr inv wl _ bh (fun (out': hole_arrays) ->
         vpattern_rewrite (parse_hole_arrays _) out';
         k_success _ sz' out' h' ()
      )
    end else begin
      let from = elim_impl_for_inv_aux_false_strong inv from0 to f prf vl.contents _ _ _ _ _ _ _ _ in
      k_failure _
    end

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let impl_for
  (#root: typ)
  (#inv: ser_index root)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from <= x /\ x < SZ.size_v to }) -> fold_t ser_state t unit inv inv))
  (prf: (x: nat { SZ.size_v from <= x /\ x < SZ.size_v to }) -> (i: t) -> (s: ser_state inv) ->
    Lemma
    (ensures (let (v, s') = Ghost.reveal f x i s in
      parse_hole s' `chunk_desc_ge` parse_hole s
    ))
  )
  (fi: (x: SZ.size_t { SZ.size_v from <= SZ.size_v x /\ SZ.size_v x < SZ.size_v to }) -> fold_impl_t p (Ghost.reveal f (SZ.size_v x)))
  (wc: with_context_arrays_ptr_t inv.context) // same
  (wl: load_context_arrays_ptr_t inv.context)
  (ws: store_context_arrays_ptr_t inv.context)
: Tot (fold_impl_t p (fold_for inv (SZ.size_v from) (SZ.size_v to) f))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  parse_hole_arrays_context_arrays_shape _ _;
  let cont = from `SZ.size_lt` to in
  let a0 = AP.merge (AP.array_of vl) (array_of_hole out) in
  with_local sz (fun bout_sz ->
  with_hole_arrays_ptr inv wc out (fun bh ->
  with_local from (fun bfrom ->
  with_local true (fun b_no_interrupt ->
  with_local cont (fun bcont ->
    intro_impl_for_inv_aux_true inv from to f vbin.contents a0 h vl sz out from cont h;
    rewrite
      (impl_for_inv0 inv p from to f bin vbin bout bout_sz bh a0 h bfrom b_no_interrupt bcont cont)
      (impl_for_inv inv p from to f bin vbin bout bout_sz bh a0 h bfrom b_no_interrupt bcont cont);
    Steel.ST.Loops.while_loop
      (impl_for_inv inv p from to f bin vbin bout bout_sz bh a0 h bfrom b_no_interrupt bcont)
      (impl_for_test inv p from to f bin vbin bout bout_sz bh a0 h bfrom b_no_interrupt bcont)
      (impl_for_body inv p from to f bin vbin bout bout_sz bh a0 h bfrom b_no_interrupt bcont fi wl ws);
    impl_for_post inv p from to f bin vbin bout bout_sz bh a0 h bfrom b_no_interrupt bcont vl out kpre kpost k_success k_failure prf wl
  )))))

#pop-options

[@@__reduce__]
let parse_nlist0
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_filter_kind parse_list_kind) (nlist n t))
= parse_list p `parse_filter` (fun l -> List.Tot.length l = n) `parse_synth` (fun x -> (x <: (nlist n t)))

let parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_filter_kind parse_list_kind) (nlist n t))
= parse_nlist0 n p

let intro_nlist
  (#opened: _)
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#vb: v parse_list_kind (list t))
  (b: byte_array)
: STGhost (v (parse_filter_kind parse_list_kind) (nlist n t)) opened
    (aparse (parse_list p) b vb)
    (fun vb' -> aparse (parse_nlist n p) b vb')
    (List.Tot.length vb.contents == n)
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      (vb'.contents <: list t) == vb.contents
    )
= let _ = intro_filter _ (fun l -> List.Tot.length l = n) b in
  let _ = intro_synth _ (fun (x: parse_filter_refine _) -> (x <: (nlist n t))) b () in
  rewrite_aparse b (parse_nlist n p)

let elim_nlist
  (#opened: _)
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#vb: v (parse_filter_kind parse_list_kind) (nlist n t))
  (b: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_nlist n p) b vb)
    (fun vb' -> aparse (parse_list p) b vb')
    True
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      (vb.contents <: list t) == vb'.contents
    )
= let _ = rewrite_aparse b (parse_nlist0 n p) in
  let _ = elim_synth _ _ b () in
  elim_filter _ _ b

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let impl_list_index
  (#root: typ)
  (#inv: ser_index root)
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (jp: jumper p)
  (n: SZ.size_t)
  (idx: (i: SZ.size_t { SZ.size_v i < SZ.size_v n }))
  (f: Ghost.erased (fold_t ser_state t unit inv inv))
  (fi: fold_impl_t p f) 
: Pure (fold_impl_t (parse_nlist (SZ.size_v n) p) (fold_list_index inv (SZ.size_v n) (SZ.size_v idx) f))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  let _ = elim_nlist _ _ bin in
  let b = list_nth jp bin idx in
  let _ = gen_elim () in
  let vbin_l = vpattern_replace (aparse (parse_list p) bin) in
  let vb = vpattern_replace (aparse p b) in
  let vbin_r = vpattern_replace (aparse (parse_list p) (list_nth_tail _ _ _ _)) in
  let bin_r = vpattern_replace_erased (fun bin_r -> aparse (parse_list p) bin_r vbin_r) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parse_list p) bin vbin_l `star`
      aparse p b vb `star`
      aparse (parse_list p) bin_r vbin_r)
    (fun _ -> aparse (parse_nlist (SZ.size_v n) p) bin vbin)
  = let _ = intro_cons p b bin_r in
    let _ = list_append p bin b in
    let _ = intro_nlist (SZ.size_v n) p bin in
    rewrite
      (aparse (parse_nlist (SZ.size_v n) p) bin _)
      (aparse (parse_nlist (SZ.size_v n) p) bin vbin)
  in
  fi b bout sz out h
    (kpre `star`
      aparse (parse_list p) bin vbin_l `star`
      aparse (parse_list p) bin_r vbin_r)
    kpost
    (fun vl' sz' out' h' v' ->
      restore ();
      k_success vl' sz' out' h' v'
    )
    (fun vb' ->
      restore ();
      k_failure vb'
    )

#pop-options

inline_for_extraction
let impl_list_index_of
  (#root: typ)
  (#inv: ser_index root)
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (jp: jumper p)
  (f: Ghost.erased (fold_t ser_state t unit inv inv))
  (fi: fold_impl_t p f) 
  (n: SZ.size_t)
  (idx: Ghost.erased ((i: nat { i < SZ.size_v n }) -> Tot (i: nat { i < SZ.size_v n })))
  (idx' : (i: SZ.size_t) -> Pure SZ.size_t (requires SZ.size_v i < SZ.size_v n) (ensures fun j -> SZ.size_v j == Ghost.reveal idx (SZ.size_v i)))
  (j: SZ.size_t {SZ.size_v j < SZ.size_v n})
: Pure (fold_impl_t (parse_nlist (SZ.size_v n) p) (fold_list_index_of inv f (SZ.size_v n) idx (SZ.size_v j)))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))
= impl_list_index jp n (idx' j) f fi

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let impl_list_for
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (fi: prog_impl_t f)
  (j: jumper (parser_of_typ t))
  (idx: array_index_fn)
  (wc: with_context_arrays_ptr_t inv.context) // same
  (wl: load_context_arrays_ptr_t inv.context)
  (ws: store_context_arrays_ptr_t inv.context)
: Tot (prog_impl_t (PListFor inv idx f))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  let _ = rewrite_aparse bin (parse_vldata 4 (parse_list (parser_of_typ t))) in
  let bin_l = elim_vldata 4 (parse_list (parser_of_typ t)) bin in
  let _ = gen_elim () in
  let vl_sz = vpattern_replace (aparse (parse_bounded_integer 4) bin) in
  let _ = vpattern_replace (aparse (parse_list (parser_of_typ t)) bin_l) in
  let in_sz = read_bounded_integer 4 bin in
  let a0 = Ghost.hide (AP.merge (AP.array_of vl) (array_of_hole out)) in
  let n = list_length j bin_l (SZ.mk_size_t in_sz) in
  let vl_l = intro_nlist (SZ.size_v n) _ bin_l in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parse_bounded_integer 4) bin vl_sz `star`
      aparse (parse_nlist (SZ.size_v n) (parser_of_typ t)) bin_l vl_l)
    (fun _ -> aparse (parser_of_typ (TList t)) bin vbin)
  =
    let _ = elim_nlist _ _ bin_l in
    let _ = intro_vldata 4 (parse_list (parser_of_typ t)) bin bin_l in
    let vbin' = rewrite_aparse bin (parser_of_typ (TList t)) in
    rewrite (aparse _ bin _) (aparse (parser_of_typ (TList t)) bin vbin)
  in
  impl_for
    (parse_nlist (SZ.size_v n) (parser_of_typ t))
    SZ.zero_size
    n
    (fold_list_index_of inv (sem ser_action_sem f) (SZ.size_v n) (idx.array_index_f_nat (SZ.size_v n)))
    (fun x i s -> prog_sem_chunk_desc_ge f (List.Tot.index i (idx.array_index_f_nat (SZ.size_v n) x)) s)
    (impl_list_index_of j (sem ser_action_sem f) fi n (idx.array_index_f_nat (SZ.size_v n)) (idx.array_index_f_sz n))
    wc wl ws
    bin_l bout sz out h
    (kpre `star` aparse (parse_bounded_integer 4) bin vl_sz)
    kpost
    (fun vl' sz' out' h' v' ->
      restore ();
      k_success vl' sz' out' h' v'
    )
    (fun vb' ->
      restore ();
      k_failure vb'
    )

#pop-options

let impl_list_hole_inv_true_prop
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (l: list (type_of_typ t))
  (vout: AP.v byte)
  (vout_sz: SZ.size_t)
  (h: ser_state inv)
  (out: hole_arrays)
: Tot prop
=
  SZ.size_v vout_sz == AP.length (AP.array_of vout) /\
  AP.array_perm (AP.array_of vout) == full_perm /\
  AP.merge_into (AP.array_of vout) (array_of_hole out) a0 /\
  fold_list inv (sem ser_action_sem f) l h0 == ((), h)

[@@__reduce__]
let impl_list_hole_inv_true
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (h0: ser_state inv)
  (l: list (type_of_typ t))
: Tot vprop
= exists_ (fun vout -> exists_ (fun vout_sz -> exists_ (fun (h: ser_state inv) -> exists_ (fun out ->
    AP.arrayptr bout vout `star`
    R.pts_to bout_sz full_perm vout_sz `star`
    GR.pts_to gh full_perm h `star`
    parse_hole_arrays h out `star`
    hole_arrays_pts_to bh out `star`
    pure (
      impl_list_hole_inv_true_prop f a0 h0 l vout vout_sz h out
    )
  ))))

[@@__reduce__]
let impl_list_hole_inv_false
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (h0: ser_state inv)
  (l: list (type_of_typ t))
: Tot vprop
= pure (chunk_exceeds_limit (parse_hole (sndp (fold_list inv (sem ser_action_sem f) l h0))) (AP.length a0)) `star`
  exists_ (R.pts_to bout_sz full_perm) `star`
  exists_ (GR.pts_to gh full_perm) `star`
  exists_ (hole_arrays_pts_to bh) `star`
  exists_ (fun vout ->
    AP.arrayptr bout vout `star`
    pure (
      AP.array_of vout == a0
    )
  )

let impl_list_hole_inv
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (h0: ser_state inv)
  (cont: bool)
  (l: list (type_of_typ t))
: Tot vprop
= if cont
  then impl_list_hole_inv_true f bout bout_sz bh gh a0 h0 l
  else impl_list_hole_inv_false f bout bout_sz bh gh a0 h0 l

inline_for_extraction
let impl_list_post_true
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (w: load_context_arrays_ptr_t inv.context)
  (vbin: _)
  (vl: _)
  (bin: byte_array)
  (bout: byte_array)
  (out: hole_arrays)
  (h: Ghost.erased (ser_state inv))
  (kpre kpost: vprop)
  (k_success: (
    (vl': AP.v byte) ->
    (sz': SZ.size_t) ->
    (out': hole_arrays) ->
    (h': Ghost.erased (ser_state inv)) ->
    (v: unit) ->
    ST unit
      (kpre `star` aparse (parser_of_typ (TList t)) bin vbin `star`
        AP.arrayptr bout vl' `star` parse_hole_arrays h' out')
      (fun _ -> kpost)
      (
        AP.adjacent (AP.array_of vl) (array_of_hole out) /\
        AP.merge_into (AP.array_of vl') (array_of_hole out') (AP.merge (AP.array_of vl) (array_of_hole out)) /\
        sem ser_action_sem (PList inv f) vbin.contents h == (v, Ghost.reveal h') /\
        SZ.size_v sz' == AP.length (AP.array_of vl')
      )
      (fun _ -> True)
  ))
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (cont: bool)
  (l: Ghost.erased (list (type_of_typ t)))
: ST unit
    (kpre `star` aparse (parser_of_typ (TList t)) bin vbin `star`
      impl_list_hole_inv f bout bout_sz bh gh a0 h cont l)
    (fun _ ->
      kpost `star`
      exists_ (R.pts_to bout_sz full_perm) `star`
      exists_ (GR.pts_to gh full_perm) `star`
      exists_ (hole_arrays_pts_to bh)
    )
    (AP.merge_into (AP.array_of vl) (array_of_hole out) a0 /\
      cont == true /\
      Ghost.reveal l == vbin.contents)
    (fun _ -> True)
=
      rewrite
        (impl_list_hole_inv f bout bout_sz bh gh a0 h cont l)
        (impl_list_hole_inv_true f bout bout_sz bh gh a0 h l);
      let _ = gen_elim () in
      let sz' = R.read bout_sz in
      let h' = GR.read gh in
      parse_hole_arrays_context_arrays_shape _ _;
    load_hole_arrays_ptr inv w _ bh (fun out' ->
      rewrite
        (parse_hole_arrays _ _)
        (parse_hole_arrays h' out');
      k_success _ sz' out' h' ();
      noop () // for automatic intro_exists
    )

inline_for_extraction
let impl_list_post_false
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (vbin: _)
  (vl: _)
  (bin: byte_array)
  (bout: byte_array)
  (out: hole_arrays)
  (h: Ghost.erased (ser_state inv))
  (kpre kpost: vprop)
  (k_failure: (
    (vb': AP.v byte) ->
    ST unit
      (kpre `star` aparse (parser_of_typ (TList t)) bin vbin `star` AP.arrayptr bout vb')
      (fun _ -> kpost)
      (
        let (_, h') = sem ser_action_sem (PList inv f) vbin.contents h in
        AP.merge_into (AP.array_of vl) (array_of_hole out) (AP.array_of vb') /\
        chunk_exceeds_limit (parse_hole h') (AP.length (AP.array_of vb'))
      )
      (fun _ -> True)
  ))
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (cont: bool)
  (l: Ghost.erased (list (type_of_typ t)))
: ST unit
    (kpre `star` aparse (parser_of_typ (TList t)) bin vbin `star`
      impl_list_hole_inv f bout bout_sz bh gh a0 h cont l)
    (fun _ ->
      kpost `star`
      exists_ (R.pts_to bout_sz full_perm) `star`
      exists_ (GR.pts_to gh full_perm) `star`
      exists_ (hole_arrays_pts_to bh)
    )
    (AP.merge_into (AP.array_of vl) (array_of_hole out) a0 /\
      cont == false /\
      Ghost.reveal l == vbin.contents)
    (fun _ -> True)
=
      rewrite
        (impl_list_hole_inv f bout bout_sz bh gh a0 h cont l)
        (impl_list_hole_inv_false f bout bout_sz bh gh a0 h l);
      let _ = gen_elim () in
      k_failure _;
      noop () // for automatic intro_exists

let rec fold_list_append
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (l1 l2: list t)
: Lemma
  (ensures (fold_list inv f (l1 `List.Tot.append` l2) state ==
    (let (_, state1) = fold_list inv f l1 state in
    fold_list inv f l2 state1)))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q ->
    let (_, state0) = f a state in
    fold_list_append inv f state0 q l2

let fold_list_snoc
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (l: list t)
  (x: t)
: Lemma
  (ensures (fold_list inv f (List.Tot.snoc (l, x)) state ==
    (let (_, state1) = fold_list inv f l state in
    f x state1)))
= fold_list_append inv f state l [x]

inline_for_extraction
let impl_list_body_false
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (#opened: _)
  (va: v pkind (type_of_typ t) { AP.length (array_of' va) > 0 })
  (a: byte_array)
  (l: Ghost.erased (list (type_of_typ t)))
: STGhostT unit opened
    (aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bh gh a0 h0 false l)
    (fun _ -> aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bh gh a0 h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)))
=
  rewrite
    (impl_list_hole_inv f bout bout_sz bh gh a0 h0 false l)
    (impl_list_hole_inv_false f bout bout_sz bh gh a0 h0 l);
  elim_pure _;
  fold_list_snoc inv (sem ser_action_sem f) h0 l va.contents;
  prog_sem_chunk_desc_ge f va.contents (sndp (fold_list inv (sem ser_action_sem f) l h0));
  chunk_desc_ge_implies
    (parse_hole (sndp (fold_list inv (sem ser_action_sem f) (List.Tot.snoc (Ghost.reveal l, va.contents)) h0)))
    (parse_hole (sndp (fold_list inv (sem ser_action_sem f) l h0)))
    (AP.length a0);
  noop ();
  rewrite
    (impl_list_hole_inv_false f bout bout_sz bh gh a0 h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
    (impl_list_hole_inv f bout bout_sz bh gh a0 h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)))

let gread_replace
  (#t: _)
  (#p: _)
  (#v: Ghost.erased t)
  (#opened: _)
  (r: GR.ref t)
: STGhost (Ghost.erased t) opened
    (GR.pts_to r p v)
    (fun res -> GR.pts_to r p res)
    True
    (fun res -> v == res)
= let res = GR.read r in
  res

inline_for_extraction
let impl_list_body_true
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (impl_f: prog_impl_t f)
  (wl: load_context_arrays_ptr_t inv.context)
  (ws: store_context_arrays_ptr_t inv.context)
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bh: hole_arrays_ptr)
  (gh: GR.ref (ser_state inv))
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (va: v pkind (type_of_typ t) { AP.length (array_of' va) > 0 })
  (a: byte_array)
  (l: Ghost.erased (list (type_of_typ t)))
: STT bool
    (aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bh gh a0 h0 true l)
    (fun res -> aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bh gh a0 h0 res (List.Tot.snoc (Ghost.reveal l, va.contents)))
=
  with_local true (fun bres ->
    noop ();
    rewrite
      (impl_list_hole_inv f bout bout_sz bh gh a0 h0 true l)
      (impl_list_hole_inv_true f bout bout_sz bh gh a0 h0 l);
    let _ = gen_elim () in
    let out_sz = read_replace bout_sz in
    let h = gread_replace gh in
  parse_hole_arrays_context_arrays_shape _ _;
  load_hole_arrays_ptr inv wl _ bh (fun out ->
    fold_list_snoc inv (sem ser_action_sem f) h0 l va.contents;
    rewrite
      (parse_hole_arrays _ _)
      (parse_hole_arrays h out);
    impl_f
      a
      bout
      out_sz
      out
      h
      (R.pts_to bout_sz full_perm out_sz `star` hole_arrays_pts_to bh out `star` GR.pts_to gh full_perm h `star` R.pts_to bres full_perm true)
      (aparse (parser_of_typ t) a va `star` exists_ (fun res -> R.pts_to bres full_perm res `star` impl_list_hole_inv f bout bout_sz bh gh a0 h0 res (List.Tot.snoc (Ghost.reveal l, va.contents))))
      (fun vl' sz' out' h' _ ->
        parse_hole_arrays_context_arrays_shape _ _;
        store_hole_arrays_ptr inv ws bh _ out' ;
        R.write bout_sz sz';
        GR.write gh h';
        rewrite
          (impl_list_hole_inv_true f bout bout_sz bh gh a0 h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
          (impl_list_hole_inv f bout bout_sz bh gh a0 h0 true (List.Tot.snoc (Ghost.reveal l, va.contents)));
        noop ()
      )
      (fun vb' ->
        R.write bres false;
        rewrite
          (impl_list_hole_inv_false f bout bout_sz bh gh a0 h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
          (impl_list_hole_inv f bout bout_sz bh gh a0 h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)));
        noop ()
      )
      ;
    let _ = gen_elim () in
    let res = R.read bres in
    rewrite
      (impl_list_hole_inv f bout bout_sz bh gh a0 h0 _ _)
      (impl_list_hole_inv f bout bout_sz bh gh a0 h0 res (List.Tot.snoc (Ghost.reveal l, va.contents)));
    return res
  ))

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let impl_list
  (#root: typ)
  (#t: typ)
  (#inv: _)
  (f: prog (ser_state #root) ser_action t unit inv inv)
  (impl_f: prog_impl_t f)
  (j: jumper (parser_of_typ t)) // MUST be computed OUTSIDE of impl_list
  (wc: with_context_arrays_ptr_t inv.context) // same
  (wl: load_context_arrays_ptr_t inv.context)
  (ws: store_context_arrays_ptr_t inv.context)
: Tot (prog_impl_t (PList inv f))
= fun #vbin #vl bin bout sz out h kpre kpost k_success k_failure ->
  let _ = rewrite_aparse bin (parse_vldata 4 (parse_list (parser_of_typ t))) in
  let bin_l = elim_vldata 4 (parse_list (parser_of_typ t)) bin in
  let _ = gen_elim () in
  let vl_sz = vpattern_replace (aparse (parse_bounded_integer 4) bin) in
  let vl_l = vpattern_replace (aparse (parse_list (parser_of_typ t)) bin_l) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parse_bounded_integer 4) bin vl_sz `star`
      aparse (parse_list (parser_of_typ t)) bin_l vl_l)
    (fun _ -> aparse (parser_of_typ (TList t)) bin vbin)
  =
    let _ = intro_vldata 4 (parse_list (parser_of_typ t)) bin bin_l in
    let vbin' = rewrite_aparse bin (parser_of_typ (TList t)) in
    rewrite (aparse _ bin _) (aparse (parser_of_typ (TList t)) bin vbin)
  in
  let in_sz = read_bounded_integer 4 bin in
  let a0 = Ghost.hide (AP.merge (AP.array_of vl) (array_of_hole out)) in
  parse_hole_arrays_context_arrays_shape _ _;
  with_local sz (fun bout_sz ->
  with_ghost_local h (fun gh ->
  with_hole_arrays_ptr inv wc out (fun bh ->
    noop ();
    rewrite
      (impl_list_hole_inv_true f bout bout_sz bh gh a0 h [])
      (impl_list_hole_inv f bout bout_sz bh gh a0 h true []);
    let cont = list_iter_with_interrupt
      j
      (impl_list_hole_inv f bout bout_sz bh gh a0 h)
      (impl_list_body_true f impl_f wl ws bout bout_sz bh gh a0 h)
      (impl_list_body_false f bout bout_sz bh gh a0 h)
      bin_l
      (SZ.mk_size_t in_sz)
    in
    restore ();
    if cont
    then impl_list_post_true f wl vbin vl bin bout out h kpre kpost k_success bout_sz bh gh a0 cont _
    else impl_list_post_false f vbin vl bin bout out h kpre kpost k_failure bout_sz bh gh a0 cont _
  )))

#pop-options
