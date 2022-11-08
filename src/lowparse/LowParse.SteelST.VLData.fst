module LowParse.SteelST.VLData
include LowParse.SteelST.Combinators
include LowParse.SteelST.FLData
include LowParse.SteelST.BoundedInt
include LowParse.Spec.VLData

module U32 = FStar.UInt32
module SZ = LowParse.Steel.StdInt
module AP = LowParse.SteelST.ArrayPtr

open Steel.ST.GenElim

inline_for_extraction
let validate_vldata_payload
  (sz: integer_size)
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (i: bounded_integer sz { f i == true } )
: Tot (validator (parse_vldata_payload sz f p i))
= coerce _ (validate_weaken (parse_vldata_payload_kind sz k) (validate_fldata v (SZ.mk_size_t i)) ())

inline_for_extraction
let validate_vldata_gen
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (f' : ((x: bounded_integer sz) -> Tot (y: bool { y == f x })))
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_vldata_gen sz f p))
= parse_vldata_gen_eq_def sz f p;
  coerce _ (
    (validate_filter_and_then
      (validate_bounded_integer sz)
      (read_bounded_integer sz)
      f
      f'
      #_ #_ #(parse_vldata_payload sz f p)
      (validate_vldata_payload sz f v)
      ())
  )

inline_for_extraction
let jump_vldata_payload
  (sz: integer_size)
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (i: bounded_integer sz { f i == true } )
: Tot (jumper (parse_vldata_payload sz f p i))
= jump_weaken (parse_vldata_payload_kind sz k) (jump_fldata p (SZ.mk_size_t i)) ()

inline_for_extraction
let jump_vldata_gen
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (jumper (parse_vldata_gen sz f p))
= parse_vldata_gen_eq_def sz f p;
  rewrite_jumper
    (jump_filter_and_then
      (jump_bounded_integer sz)
      (read_bounded_integer sz)
      f
      #_ #_ #(parse_vldata_payload sz f p)
      (jump_vldata_payload sz f p)
      ())
    (parse_vldata_gen sz f p)

#set-options "--ide_id_info_off"

let ghost_elim_vldata_gen
  (#opened: _)
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhostT (Ghost.erased byte_array) opened
    (aparse (parse_vldata_gen sz f p) a va)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse (parse_bounded_integer sz) a va1 `star`
      aparse p a2 va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      f va1.contents == true /\
      U32.v va1.contents == AP.length (array_of va2) /\
      (va2.contents <: t) == va.contents
    ))))
= parse_vldata_gen_eq_def sz f p;
  let _ = rewrite_aparse a (and_then (parse_filter (parse_bounded_integer sz) f) (parse_vldata_payload sz f p)) in
  let res = ghost_split_and_then
    (parse_filter (parse_bounded_integer sz) f)
    (parse_vldata_payload sz f p)
    ()
    a
  in
  let _ = gen_elim () in
  let tag = ghost_and_then_tag
    (parse_filter (parse_bounded_integer sz) f)
    (parse_vldata_payload sz f p)
    ()
    a
    res
  in
  let _ = gen_elim () in
  let _ = elim_filter _ _ a in
  let _ = rewrite_aparse res (parse_fldata p (U32.v tag)) in
  let _ = elim_fldata _ _ res in
  res

inline_for_extraction
let elim_vldata_gen
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STT byte_array
    (aparse (parse_vldata_gen sz f p) a va)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse (parse_bounded_integer sz) a va1 `star`
      aparse p a2 va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      f va1.contents == true /\
      U32.v va1.contents == AP.length (array_of va2) /\
      (va2.contents <: t) == va.contents
    ))))
= let gres = ghost_elim_vldata_gen sz f p a in
  let _ = gen_elim () in
  let res = hop_aparse_aparse (jump_bounded_integer sz) _ a gres in
  return res

let intro_vldata_gen
  (#opened: _)
  (sz: integer_size) // must be a constant
  (f: ((x: bounded_integer sz) -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a a2: byte_array)
: STGhost (v (parse_vldata_gen_kind sz k) t) opened
    (aparse (parse_bounded_integer sz) a va1 `star` aparse p a2 va2)
    (fun va -> aparse (parse_vldata_gen sz f p) a va)
    (AP.adjacent (array_of va1) (array_of va2) /\
      f va1.contents == true /\
      U32.v va1.contents == AP.length (array_of va2)
    )
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      (va2.contents <: t) == va.contents
    )
=
  let tag = va1.contents in
  let _ = intro_filter (parse_bounded_integer sz) f a in
  let _ = intro_fldata p (U32.v tag) a2 in
  parse_vldata_gen_eq_def sz f p;
  let _ = intro_and_then (parse_filter (parse_bounded_integer sz) f) (parse_vldata_payload sz f p) _ () a a2 in
  rewrite_aparse a _

inline_for_extraction
let elim_vldata
  (sz: integer_size) // must be a constant
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STT byte_array
    (aparse (parse_vldata sz p) a va)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse (parse_bounded_integer sz) a va1 `star`
      aparse p a2 va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      U32.v va1.contents == AP.length (array_of va2) /\
      (va2.contents <: t) == va.contents
    ))))
= let res = elim_vldata_gen sz (unconstrained_bounded_integer _) p a in
  let _ = gen_elim () in
  return res

let intro_vldata
  (#opened: _)
  (sz: integer_size) // must be a constant
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a a2: byte_array)
: STGhost (v (parse_vldata_gen_kind sz k) t) opened
    (aparse (parse_bounded_integer sz) a va1 `star` aparse p a2 va2)
    (fun va -> aparse (parse_vldata sz p) a va)
    (AP.adjacent (array_of va1) (array_of va2) /\
      U32.v va1.contents == AP.length (array_of va2)
    )
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      (va2.contents <: t) == va.contents
    )
= intro_vldata_gen sz (unconstrained_bounded_integer _) p a a2
