module LowParse.SteelST.Fold
include LowParse.SteelST.Fold.Base

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
  | CNil -> parse_some_chunk parse_empty ()
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
  (sq: squash (pre.leaf == TU8 /\ HVHole? pre.hole /\ CNil? pre.context))
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
      chunk_desc_ge_intro_exact_parse_some_chunk
        (weaken default_parser_kind (parser_of_typ TU8))
        parse_u8
        w;
      chunk_desc_ge_concat_chunk_intro_r
        (parse_some_chunk (weaken default_parser_kind (parser_of_typ TU8)) w)
        (parse_context h.context);
      chunk_desc_ge_implies
        (parse_hole (fill_hole h w))
        (parse_some_chunk parse_u8 w)
        (AP.length (AP.array_of vb));
      elim_parse_context_arrays_nil _ _ _;
      let _ = elim_empty_chunk empty_chunk _ in
      let vb' = AP.join bout _ in
      k_failure vb'
    )

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
      (kpre `star` aparse (parser_of_typ ty) bin vbin `star`
        AP.arrayptr bout vl' `star` parse_hole_arrays h' out')
      (fun _ -> kpost)
      (
        AP.adjacent (AP.array_of vl) (array_of_hole out) /\
        AP.merge_into (AP.array_of vl') (array_of_hole out') (AP.merge (AP.array_of vl) (array_of_hole out)) /\
        sem ser_action_sem p vbin.contents h == (v, Ghost.reveal h') /\
        SZ.size_v sz' == AP.length (AP.array_of vl')
      )
      (fun _ -> True)
  )) ->
  (k_failure: (
    (vb': AP.v byte) ->
    ST unit
      (kpre `star` aparse (parser_of_typ ty) bin vbin `star` AP.arrayptr bout vb')
      (fun _ -> kpost)
      (
        let (_, h') = sem ser_action_sem p vbin.contents h in
        AP.merge_into (AP.array_of vl) (array_of_hole out) (AP.array_of vb') /\
        chunk_exceeds_limit (parse_hole h') (AP.length (AP.array_of vb'))
      )
      (fun _ -> True)
  )) ->
  ST unit
    (kpre `star` aparse (parser_of_typ ty) bin vbin `star`
      AP.arrayptr bout vl `star` parse_hole_arrays h out)
    (fun _ -> kpost)
    (SZ.size_v sz == AP.length (AP.array_of vl) /\
      AP.array_perm (AP.array_of vl) == full_perm /\
      AP.adjacent (AP.array_of vl) (array_of_hole out)
    )
    (fun _ -> True)

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
        chunk_desc_ge_zero_r (parse_some_chunk (weaken default_parser_kind (parser_of_typ root)) v') (parse_some_chunk parse_empty ());
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
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (l: list (type_of_typ t))
: Tot vprop
= exists_ (fun vout -> exists_ (fun vout_sz -> exists_ (fun (h: ser_state inv) -> exists_ (fun out ->
    AP.arrayptr bout vout `star`
    R.pts_to bout_sz full_perm vout_sz `star`
    GR.pts_to gh full_perm h `star`
    GR.pts_to gout full_perm out `star`
    parse_hole_arrays h out `star`
    R.pts_to bhead full_perm out.ha_hole_b `star`
    R.pts_to bhead_sz full_perm out.ha_hole_sz `star`
    R.pts_to btail full_perm out.ha_context_b `star`
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
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (l: list (type_of_typ t))
: Tot vprop
= pure (chunk_exceeds_limit (parse_hole (sndp (fold_list inv (sem ser_action_sem f) l h0))) (AP.length a0)) `star`
  exists_ (R.pts_to bout_sz full_perm) `star`
  exists_ (GR.pts_to gh full_perm) `star`
  exists_ (GR.pts_to gout full_perm) `star`
  exists_ (R.pts_to bhead full_perm) `star`
  exists_ (R.pts_to bhead_sz full_perm) `star`
  exists_ (R.pts_to btail full_perm) `star`
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
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (h0: ser_state inv)
  (cont: bool)
  (l: list (type_of_typ t))
: Tot vprop
= if cont
  then impl_list_hole_inv_true f bout bout_sz bhead bhead_sz btail gh gout a0 h0 l
  else impl_list_hole_inv_false f bout bout_sz bhead bhead_sz btail gh gout a0 h0 l

inline_for_extraction
let impl_list_post_true
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
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (cont: bool)
  (l: Ghost.erased (list (type_of_typ t)))
: ST unit
    (kpre `star` aparse (parser_of_typ (TList t)) bin vbin `star`
      impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h cont l)
    (fun _ ->
      kpost `star`
      exists_ (R.pts_to bout_sz full_perm) `star`
      exists_ (R.pts_to bhead full_perm) `star`
      exists_ (R.pts_to bhead_sz full_perm) `star`
      exists_ (R.pts_to btail full_perm) `star`
      exists_ (GR.pts_to gh full_perm) `star`
      exists_ (GR.pts_to gout full_perm)
    )
    (AP.merge_into (AP.array_of vl) (array_of_hole out) a0 /\
      cont == true /\
      Ghost.reveal l == vbin.contents /\
      CNil? inv.context)
    (fun _ -> True)
=
      rewrite
        (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h cont l)
        (impl_list_hole_inv_true f bout bout_sz bhead bhead_sz btail gh gout a0 h l);
      let _ = gen_elim () in
      let sz' = R.read bout_sz in
      let h' = GR.read gh in
      let gout' = GR.read gout in
      let head' = R.read bhead in
      let head_sz' = R.read bhead_sz in
      let tail' = R.read btail in
      parse_hole_arrays_empty_context _ _;
      [@inline_let] // CRITICAL to avoid extracting whole struct values
      let out' = {
        ha_hole_a = gout'.ha_hole_a;
        ha_hole_b = head';
        ha_hole_sz = head_sz';
        ha_context_a = gout'.ha_context_a;
        ha_context_b = tail';
        ha_context = CANil _;
        ha_prf = gout'.ha_prf;
      }
      in
      rewrite
        (parse_hole_arrays _ _)
        (parse_hole_arrays h' out');
      k_success _ sz' out' h' ();
      noop () // for automatic intro_exists

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
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (cont: bool)
  (l: Ghost.erased (list (type_of_typ t)))
: ST unit
    (kpre `star` aparse (parser_of_typ (TList t)) bin vbin `star`
      impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h cont l)
    (fun _ ->
      kpost `star`
      exists_ (R.pts_to bout_sz full_perm) `star`
      exists_ (R.pts_to bhead full_perm) `star`
      exists_ (R.pts_to bhead_sz full_perm) `star`
      exists_ (R.pts_to btail full_perm) `star`
      exists_ (GR.pts_to gh full_perm) `star`
      exists_ (GR.pts_to gout full_perm)
    )
    (AP.merge_into (AP.array_of vl) (array_of_hole out) a0 /\
      cont == false /\
      Ghost.reveal l == vbin.contents /\
      CNil? inv.context)
    (fun _ -> True)
= 
      rewrite
        (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h cont l)
        (impl_list_hole_inv_false f bout bout_sz bhead bhead_sz btail gh gout a0 h l);
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
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (#opened: _)
  (va: v pkind (type_of_typ t) { AP.length (array_of' va) > 0 })
  (a: byte_array)
  (l: Ghost.erased (list (type_of_typ t)))
: STGhostT unit opened
    (aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 false l)
    (fun _ -> aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)))
=
  rewrite
    (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 false l)
    (impl_list_hole_inv_false f bout bout_sz bhead bhead_sz btail gh gout a0 h0 l);
  elim_pure _;
  fold_list_snoc inv (sem ser_action_sem f) h0 l va.contents;
  prog_sem_chunk_desc_ge f va.contents (sndp (fold_list inv (sem ser_action_sem f) l h0));
  chunk_desc_ge_implies
    (parse_hole (sndp (fold_list inv (sem ser_action_sem f) (List.Tot.snoc (Ghost.reveal l, va.contents)) h0)))
    (parse_hole (sndp (fold_list inv (sem ser_action_sem f) l h0)))
    (AP.length a0);
  noop ();
  rewrite
    (impl_list_hole_inv_false f bout bout_sz bhead bhead_sz btail gh gout a0 h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
    (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)))

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
  (bout: byte_array)
  (bout_sz: R.ref SZ.size_t)
  (bhead: R.ref byte_array)
  (bhead_sz: R.ref SZ.size_t)
  (btail: R.ref byte_array)
  (gh: GR.ref (ser_state inv))
  (gout: GR.ref hole_arrays)
  (a0: AP.array byte)
  (h0: Ghost.erased (ser_state inv))
  (sq: squash (CNil? inv.context))
  (va: v pkind (type_of_typ t) { AP.length (array_of' va) > 0 })
  (a: byte_array)
  (l: Ghost.erased (list (type_of_typ t)))
: STT bool
    (aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 true l)
    (fun res -> aparse (parser_of_typ t) a va `star` impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 res (List.Tot.snoc (Ghost.reveal l, va.contents)))
=
  with_local true (fun bres ->
    noop ();
    rewrite
      (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 true l)
      (impl_list_hole_inv_true f bout bout_sz bhead bhead_sz btail gh gout a0 h0 l);
    let _ = gen_elim () in
    let out_sz = read_replace bout_sz in
    let head = read_replace bhead in
    let head_sz = read_replace bhead_sz in
    let tail = read_replace btail in
    let h = gread_replace gh in
    let out0 = gread_replace gout in
    parse_hole_arrays_empty_context _ _;
    fold_list_snoc inv (sem ser_action_sem f) h0 l va.contents;
    [@inline_let]
    let out = {
      ha_hole_a = out0.ha_hole_a;
      ha_hole_b = head;
      ha_hole_sz = head_sz;
      ha_context_a = out0.ha_context_a;
      ha_context_b = tail;
      ha_context = CANil _;
      ha_prf = ();
    }
    in
    rewrite
      (parse_hole_arrays _ _)
      (parse_hole_arrays h out);
    impl_f
      a
      bout
      out_sz
      out
      h
      (R.pts_to bout_sz full_perm out_sz `star` R.pts_to bhead full_perm head `star` R.pts_to bhead_sz full_perm head_sz `star` R.pts_to btail full_perm tail `star` GR.pts_to gh full_perm h `star` GR.pts_to gout full_perm out0 `star` R.pts_to bres full_perm true)
      (aparse (parser_of_typ t) a va `star` exists_ (fun res -> R.pts_to bres full_perm res `star` impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 res (List.Tot.snoc (Ghost.reveal l, va.contents))))
      (fun vl' sz' out' h' _ ->
        R.write bout_sz sz';
        R.write bhead out'.ha_hole_b;
        R.write bhead_sz out'.ha_hole_sz;
        R.write btail out'.ha_context_b;
        GR.write gh h';
        GR.write gout out';
        rewrite
          (impl_list_hole_inv_true f bout bout_sz bhead bhead_sz btail gh gout a0 h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
          (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 true (List.Tot.snoc (Ghost.reveal l, va.contents)));
        noop ()
      )
      (fun vb' ->
        R.write bres false;
        rewrite
          (impl_list_hole_inv_false f bout bout_sz bhead bhead_sz btail gh gout a0 h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
          (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)));
        noop ()
      )
      ;
    let _ = gen_elim () in
    let res = R.read bres in
    rewrite
      (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 _ _)
      (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h0 res (List.Tot.snoc (Ghost.reveal l, va.contents)));
    return res
  )

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
: Pure (prog_impl_t (PList inv f))
    (requires (CNil? inv.context))
    (ensures (fun _ -> True))
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
  with_local sz (fun bout_sz ->
  with_local out.ha_hole_b (fun bhead ->
  with_local out.ha_hole_sz (fun bhead_sz ->
  with_local out.ha_context_b (fun btail ->
  with_ghost_local h (fun gh ->
  with_ghost_local out (fun gout ->
    noop ();
    rewrite
      (impl_list_hole_inv_true f bout bout_sz bhead bhead_sz btail gh gout a0 h [])
      (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h true []);
    let cont = list_iter_with_interrupt
      j
      (impl_list_hole_inv f bout bout_sz bhead bhead_sz btail gh gout a0 h)
      (impl_list_body_true f impl_f bout bout_sz bhead bhead_sz btail gh gout a0 h ())
      (impl_list_body_false f bout bout_sz bhead bhead_sz btail gh gout a0 h)
      bin_l
      (SZ.mk_size_t in_sz)
    in
    restore ();
    if cont
    then impl_list_post_true f vbin vl bin bout out h kpre kpost k_success bout_sz bhead bhead_sz btail gh gout a0 cont _
    else impl_list_post_false f vbin vl bin bout out h kpre kpost k_failure bout_sz bhead bhead_sz btail gh gout a0 cont _
  ))))))

#pop-options
