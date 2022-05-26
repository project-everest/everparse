module LowParse.SteelST.FLData
include LowParse.Spec.FLData
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module R = Steel.ST.Reference
module SZ = LowParse.Steel.StdInt

let validator_error_wrong_size = 3ul

let assertf (#opened_invariants:_)
            (p:vprop)
  : STGhostF unit opened_invariants p (fun _ -> p) True (fun _ -> True)
= noop ()

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_fldata_gen
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: SZ.size_t)
: Pure (validator (parse_fldata p sz))
    (requires (SZ.size_v sz32 == sz))
    (ensures (fun _ -> True))
= fun #va a len err ->
  if len `SZ.size_lt` sz32
  then begin
      R.write err validator_error_not_enough_data;
      return (SZ.zero_size <: SZ.size_t)
  end else begin
      let ar = AP.split a sz32 in
      let _ = gen_elim () in
      let s1 = v a sz32 err in
      let _ = gen_elim () in
      let _ = AP.join a ar in
      let _ = gen_elim () in
      let verr = R.read err in
      assertf (R.pts_to err full_perm verr `star` AP.arrayptr a va); // FIXME: WHY WHY WHY?
      if verr = 0ul // returns STT SZ.size_t (R.pts_to err full_perm verr `star` AP.arrayptr a va) (validator_post (parse_fldata p sz) va a len err)
      then begin
          if s1 <> sz32
          then begin
              R.write err validator_error_wrong_size;
              return s1
          end else begin
              noop ();
              return s1
          end
       end else begin
          noop ();
          return s1
       end
  end

inline_for_extraction
let validate_fldata_consumes_all
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: SZ.size_t)
: Pure (validator (parse_fldata p sz))
    (requires (SZ.size_v sz32 == sz /\ k.parser_kind_subkind == Some ParserConsumesAll))
    (ensures (fun _ -> True))
= fun #va a len err ->
  if len `SZ.size_lt` sz32
  then begin
      R.write err validator_error_not_enough_data;
      return (SZ.zero_size <: SZ.size_t)
  end else begin
      let ar = AP.split a sz32 in
      let _ = gen_elim () in
      parser_kind_prop_equiv k p;
      let s1 = v a sz32 err in
      let _ = gen_elim () in
      let _ = AP.join a ar in
      let _ = gen_elim () in
      return s1
  end

#pop-options

inline_for_extraction
let validate_fldata
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (sz: nat)
  (sz32: SZ.size_t)
: Pure (validator (parse_fldata p sz))
    (requires (SZ.size_v sz32 == sz))
    (ensures (fun _ -> True))
= if k.parser_kind_subkind = Some ParserConsumesAll
  then validate_fldata_consumes_all v sz sz32
  else validate_fldata_gen v sz sz32

inline_for_extraction
let validate_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (v: validator p)
  (sz: nat)
  (sz32: SZ.size_t)
: Pure (validator (parse_fldata_strong s sz))
    (requires (SZ.size_v sz32 == sz))
    (ensures (fun _ -> True))
= fun #va a len err ->
  let res = validate_fldata v sz sz32 a len err in
  let _ = gen_elim () in
  return res

inline_for_extraction
let jump_fldata
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  (sz32: SZ.size_t)
: Pure (jumper (parse_fldata p sz))
    (requires (SZ.size_v sz32 == sz))
    (ensures (fun _ -> True))
= jump_constant_size (parse_fldata p sz) sz32

inline_for_extraction
let jump_fldata_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: SZ.size_t)
: Pure (jumper (parse_fldata_strong s sz))
    (requires (SZ.size_v sz32 == sz))
    (ensures (fun _ -> True))
= jump_constant_size (parse_fldata_strong s sz) sz32

let intro_fldata
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  #va (a: byte_array)
: STGhost (v (parse_fldata_kind sz k) t) opened
    (aparse p a va)
    (fun va' -> aparse (parse_fldata p sz) a va')
    (sz == AP.length (array_of' va))
    (fun va' ->
      array_of' va' == array_of va /\
      va'.contents == va.contents
    )
= let _ = elim_aparse p a in
  intro_aparse (parse_fldata p sz) a

let elim_fldata
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: nat)
  #va (a: byte_array)
: STGhost (v k t) opened
    (aparse (parse_fldata p sz) a va)
    (fun va' -> aparse p a va')
    True
    (fun va' ->
      sz == AP.length (array_of' va) /\
      array_of' va' == array_of va /\
      va'.contents == va.contents
    )
= let _ = elim_aparse (parse_fldata p sz) a in
  intro_aparse p a

let intro_fldata_strong
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  #va (a: byte_array)
: STGhost (v (parse_fldata_kind sz k) (parse_fldata_strong_t s sz)) opened
    (aparse p a va)
    (fun va' -> aparse (parse_fldata_strong s sz) a va')
    (sz == AP.length (array_of' va))
    (fun va' ->
      array_of' va' == array_of va /\
      (va'.contents <: t) == va.contents
    )
= let _ = elim_aparse p a in
  intro_aparse (parse_fldata_strong s sz) a

let elim_fldata_strong
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (#va: v (parse_fldata_kind sz k) (parse_fldata_strong_t s sz)) (a: byte_array)
: STGhost (v k t) opened
    (aparse (parse_fldata_strong s sz) a va)
    (fun va' -> aparse p a va')
    True
    (fun va' ->
      sz == AP.length (array_of' va) /\
      array_of' va' == (array_of va) /\
      (va.contents <: t) == va'.contents
    )
= let _ = elim_aparse (parse_fldata_strong s sz) a in
  intro_aparse p a
