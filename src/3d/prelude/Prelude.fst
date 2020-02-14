(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Prelude
include Prelude.StaticHeader
include ResultOps
module BF = LowParse.BitFields
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Low.Base
module LPLC = LowParse.Low.Combinators
////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction
noextract
let parser_kind (nz:bool) =
  k:LP.parser_kind{LP.(k.parser_kind_subkind == Some ParserStrong /\
                      (nz ==> (k.parser_kind_low > 0)))}

let parser #nz (k:parser_kind nz) (t:Type) = LP.parser k t

let is_weaker_than #nz1 (k:parser_kind nz1)
                   #nz2 (k':parser_kind nz2) = k `LP.is_weaker_than` k'

inline_for_extraction
noextract
let glb #nz1 (k1:parser_kind nz1)
        #nz2 (k2:parser_kind nz2)
    : parser_kind (nz1 && nz2)
    = LP.glb k1 k2

let is_weaken_than_refl #nz (k:parser_kind nz)
  : Lemma (ensures (is_weaker_than k k))
          [SMTPat (is_weaker_than k k)]
  = ()

let is_weaker_than_glb #nz1 (k1:parser_kind nz1)
                       #nz2 (k2:parser_kind nz2)
  : Lemma (is_weaker_than (glb k1 k2) k1 /\
           is_weaker_than (glb k1 k2) k2)
          [SMTPatOr
            [[SMTPat (is_weaker_than (glb k1 k2) k1)];
             [SMTPat (is_weaker_than (glb k1 k2) k2)]]]
  = ()

/// Parser: return
inline_for_extraction
noextract
let ret_kind : parser_kind false = LPC.parse_ret_kind
inline_for_extraction noextract
let parse_ret #t (v:t)
  : Tot (parser ret_kind t)
  = LPC.parse_ret #t v

/// Parser: bind
inline_for_extraction
noextract
let and_then_kind #nz1 (k1:parser_kind nz1)
                  #nz2 (k2:parser_kind nz2)
    : parser_kind (nz1 || nz2)
    = LPC.and_then_kind k1 k2
inline_for_extraction noextract
let parse_dep_pair #nz1 (#k1:parser_kind nz1) (#t1: Type0) (p1: parser k1 t1)
                   #nz2 (#k2:parser_kind nz2) (#t2: (t1 -> Tot Type0)) (p2: (x: t1) -> parser k2 (t2 x))
  : Tot (parser (and_then_kind k1 k2) (dtuple2 t1 t2) )
  = LPC.parse_dtuple2 p1 p2

/// Parser: sequencing
inline_for_extraction noextract
let parse_pair #nz1 (#k1:parser_kind nz1) #t1 (p1:parser k1 t1)
               #nz2 (#k2:parser_kind nz2) #t2 (p2:parser k2 t2)
  : Tot (parser (and_then_kind k1 k2) (t1 * t2))
  = LPC.nondep_then p1 p2

/// Parser: map
let injective_map a b = f:(a -> Tot b) //{LPC.synth_injective f}

inline_for_extraction noextract
let parse_map #nz (#k:parser_kind nz) #t1 #t2 (p:parser k t1)
              (f:injective_map t1 t2)
  : Tot (parser k t2)
  = assume (LPC.synth_injective f); LPC.parse_synth p f

/// Parser: filter
let refine t (f:t -> bool) = x:t{f x}

inline_for_extraction
noextract
let filter_kind #nz (k:parser_kind nz) : parser_kind nz = LPC.parse_filter_kind k
inline_for_extraction noextract
let parse_filter #nz (#k:parser_kind nz) #t (p:parser k t) (f:(t -> bool))
  : Tot (parser (filter_kind k) (refine t f))
  = LPC.parse_filter #k #t p f

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken #nz  (#k:parser_kind nz) #t (p:parser k t)
                 #nz' (k':parser_kind nz'{k' `is_weaker_than` k})
  : Tot (parser k' t)
  = LP.weaken k' p

inline_for_extraction
noextract
let impos_kind : parser_kind true =
  LPC.(strong_parser_kind 1 1 (Some ParserKindMetadataFail))


unfold
let parser_kind_prop' (#t: Type0) (k: LP.parser_kind) (f: LP.bare_parser t) : GTot Type0 =
  let open LP in
  injective f /\
  (Some? k.parser_kind_subkind ==> parser_subkind_prop (Some?.v k.parser_kind_subkind) f) /\
  parses_at_least k.parser_kind_low f /\
  (Some? k.parser_kind_high ==> (parses_at_most (Some?.v k.parser_kind_high) f)) /\
  parser_kind_metadata_prop k f

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
let parse_impos ()
  : parser impos_kind False
  = let p : LP.bare_parser False = fun b -> None in
    LP.parser_kind_prop_equiv impos_kind p;
    p

let t_ite (e:bool) (a:Type) (b:Type) = if e then a else b
let parse_ite #nz (#k:parser_kind nz) (#a:Type) (#b:Type) (e:bool)
              (p1:squash e -> parser k a)
              (p2:squash (not e) -> parser k b)
  : Tot (parser k (t_ite e a b))
  = if e then p1 () else p2 ()

module U32 = FStar.UInt32
module U16 = FStar.UInt16

let nlist (n:U32.t) (t:Type) = list t

/// Lists/arrays
inline_for_extraction
noextract
let kind_nlist : parser_kind false =
  let open LP in
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None
  }

inline_for_extraction noextract
let parse_nlist (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Tot (parser kind_nlist (nlist n t))
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false #(parse_fldata_kind (U32.v n) parse_list_kind) #(list t)
            (LowParse.Spec.FLData.parse_fldata (LowParse.Spec.List.parse_list p) (U32.v n))
            #false kind_nlist


////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let reader #nz (#k:parser_kind nz) #t (p:parser k t) = LPLC.leaf_reader p

inline_for_extraction noextract
let read_filter #nz
                (#k: parser_kind nz)
                (#t: Type0)
                (#p: parser k t)
                (p32: LPL.leaf_reader p)
                (f: (t -> bool))
    : LPL.leaf_reader (parse_filter p f)
    = LPLC.read_filter p32 f

////////////////////////////////////////////////////////////////////////////////
// Validators
////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let validator #nz (#k:parser_kind nz) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator #k #t p

inline_for_extraction noextract
let validate_ret
  : validator (parse_ret ())
  = LPLC.validate_ret ()

inline_for_extraction noextract
let validate_pair #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1) (v1:validator p1)
                  #nz2 (#k2:parser_kind nz2) #t2 (#p2:parser k2 t2) (v2:validator p2)
  : validator (p1 `parse_pair` p2)
  = LPLC.validate_nondep_then v1 v2

inline_for_extraction noextract
let validate_dep_pair #nz1 (#k1:parser_kind nz1) #t1 (#p1:parser k1 t1) (v1:validator p1) (r1: LPL.leaf_reader p1)
                      #nz2 (#k2:parser_kind nz2) (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x))) (v2:(x:t1 -> validator (p2 x)))
  : Tot (validator (p1 `parse_dep_pair` p2))
  = LPLC.validate_dtuple2 v1 r1 v2

inline_for_extraction noextract
let validate_map #nz (#k:parser_kind nz) #t1 (#p:parser k t1) (v:validator p)
                 #t2 (f:injective_map t1 t2)
  : Tot (validator (p `parse_map` f))
  = assume (LPC.synth_injective f); LPLC.validate_synth v f ()

inline_for_extraction noextract
let validate_filter #nz (#k:parser_kind nz) (#t:_) (#p:parser k t) (v:validator p) (r:LPL.leaf_reader p) (f:(t -> bool))
  : Tot (validator (p `parse_filter` f))
  = LPLC.validate_filter v r f (fun x -> f x)

inline_for_extraction noextract
let validate_weaken #nz (#k:parser_kind nz) #t (#p:parser k t) (v:validator p)
                    #nz' (k':parser_kind nz'{k' `is_weaker_than` k})
  : Tot (validator (p `parse_weaken` k'))
  = LPLC.validate_weaken k' v ()

[@ CMacro ]
let validator_error_impossible : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 3uL)

inline_for_extraction noextract
let validate_impos ()
  : Tot (validator (parse_impos ()))
  = fun #_ #_ _ _ -> validator_error_impossible

inline_for_extraction noextract
let validate_nlist (n:U32.t) (#k:parser_kind true) #t (#p:parser k t) (v:validator p)
  : Tot (validator (parse_nlist n p))
  = validate_weaken
      #false
      (LowParse.Low.FLData.validate_fldata_consumes_all (LowParse.Low.List.validate_list v ()) (U32.v n) n ())
      #false kind_nlist

let parse_nlist_total_fixed_size_aux
  (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  (x: LP.bytes)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    Seq.length x >= U32.v n
  ))
  (ensures (
    Some? (LP.parse (parse_nlist n p) x)
  ))
= let x' = Seq.slice x 0 (U32.v n) in
  LowParse.Spec.List.parse_list_total_constant_size p (U32.v n / k.LP.parser_kind_low) x';
  LP.parser_kind_prop_equiv LowParse.Spec.List.parse_list_kind (LowParse.Spec.List.parse_list p)

let parse_nlist_total_fixed_size_kind_correct
  (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    LP.parser_kind_prop (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)
  ))
= LP.parser_kind_prop_equiv (LowParse.Spec.FLData.parse_fldata_kind (U32.v n) LowParse.Spec.List.parse_list_kind) (parse_nlist n p);
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p);
  Classical.forall_intro (Classical.move_requires (parse_nlist_total_fixed_size_aux n p))

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Pure (validator (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296 /\
    U32.v n % k.LP.parser_kind_low == 0
  ))
  (ensures (fun _ -> True))
= 
      (fun #rrel #rel sl pos ->
         let h = FStar.HyperStack.ST.get () in
         [@inline_let]
         let _ =
           parse_nlist_total_fixed_size_kind_correct n p;
           LPL.valid_facts (parse_nlist n p) h sl (LPL.uint64_to_uint32 pos);
           LPL.valid_facts (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) h sl (LPL.uint64_to_uint32 pos)
         in
         LPL.validate_total_constant_size (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) (FStar.Int.Cast.uint32_to_uint64 n) () sl pos
      )

[@ CMacro ]
let validator_error_list_size_not_multiple : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 4uL)

inline_for_extraction noextract
let validate_nlist_constant_size_mod_ko (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Pure (validator (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.LP.parser_kind_low <> 0
  ))
  (ensures (fun _ -> True))
= 
  (fun #rrel #rel sl pos ->
     let h = FStar.HyperStack.ST.get () in
     [@inline_let]
     let _ =
       LPL.valid_facts (parse_nlist n p) h sl (LPL.uint64_to_uint32 pos)
     in
     [@inline_let]
     let f () : Lemma
       (requires (LPL.valid (parse_nlist n p) h sl (LPL.uint64_to_uint32 pos)))
       (ensures False)
     = let sq = LPL.bytes_of_slice_from h sl (LPL.uint64_to_uint32 pos) in
       let sq' = Seq.slice sq 0 (U32.v n) in
       LowParse.Spec.List.list_length_constant_size_parser_correct p sq' ;
       let Some (l, _) = LP.parse (parse_nlist n p) sq in
       assert (U32.v n == FStar.List.Tot.length l `Prims.op_Multiply` k.LP.parser_kind_low) ;
       FStar.Math.Lemmas.cancel_mul_mod (FStar.List.Tot.length l) k.LP.parser_kind_low ;
       assert (U32.v n % k.LP.parser_kind_low == 0)
     in
     [@inline_let]
     let _ = Classical.move_requires f () in
     validator_error_list_size_not_multiple
  )

inline_for_extraction noextract
let validate_nlist_total_constant_size' (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Pure (validator (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
= fun #rrel #rel sl pos ->
  if n `U32.rem` U32.uint_to_t k.LP.parser_kind_low = 0ul
  then validate_nlist_total_constant_size_mod_ok n p sl pos
  else validate_nlist_constant_size_mod_ko n p sl pos

inline_for_extraction noextract
let validate_nlist_total_constant_size (n_is_const: bool) (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
: Pure (validator (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind = Some ParserStrong /\
    k.parser_kind_high = Some k.parser_kind_low /\
    k.parser_kind_metadata = Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
=
  if
    if k.LP.parser_kind_low = 1
    then true
    else if n_is_const
    then U32.v n % k.LP.parser_kind_low = 0
    else false
  then
    validate_nlist_total_constant_size_mod_ok n p
  else if
    if n_is_const
    then U32.v n % k.LP.parser_kind_low <> 0
    else false
  then
    validate_nlist_constant_size_mod_ko n p
  else
    validate_nlist_total_constant_size' n p

noextract inline_for_extraction
let validate_ite #nz (#k:parser_kind nz) (#a:Type) (#b:Type) (e:bool)
                 (p1:squash e -> parser k a) (v1:(squash e -> validator (p1())))
                 (p2:squash (not e) -> parser k b) (v2:(squash (not e) -> validator (p2())))
  : Tot (validator (parse_ite e p1 p2))
  = fun #rrel #rel sl pos ->
      if e then v1 () sl pos else v2 () sl pos

module U32 = FStar.UInt32
module U64 = FStar.UInt64

inline_for_extraction noextract
let validate_with_error #nz (#k:parser_kind nz) #t (#p:parser k t) (f:field_id) (v:validator p)
  : Tot (validator p)
  = LPL.validate_with_error_code v f

inline_for_extraction noextract
let validate_with_comment #nz (#k:parser_kind nz) #t (#p:parser k t) (c:string) (v:validator p)
  : Tot (validator p)
  = LPL.validate_with_comment c v

////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////


/// UINT8
let ___UINT8 : eqtype = FStar.UInt8.t
inline_for_extraction noextract
let kind____UINT8 : parser_kind true= LowParse.Spec.Int.parse_u8_kind
let parse____UINT8 : parser kind____UINT8 ___UINT8 = LowParse.Spec.Int.parse_u8
let validate____UINT8 : validator parse____UINT8 = LowParse.Low.Int.validate_u8 ()
let read____UINT8 : LPL.leaf_reader parse____UINT8 = LowParse.Low.Int.read_u8

/// UInt16
let ___UINT16 : eqtype = U16.t
inline_for_extraction noextract
let kind____UINT16 : parser_kind true = LowParse.Spec.BoundedInt.parse_u16_kind
let parse____UINT16 : parser kind____UINT16 ___UINT16 = LowParse.Spec.BoundedInt.parse_u16_le
let validate____UINT16 : validator parse____UINT16 = LowParse.Low.BoundedInt.validate_u16_le ()
let read____UINT16 : LPL.leaf_reader parse____UINT16 = LowParse.Low.BoundedInt.read_u16_le

/// UInt32
let ___UINT32 : eqtype = U32.t
inline_for_extraction noextract
let kind____UINT32 : parser_kind true = LowParse.Spec.BoundedInt.parse_u32_kind
let parse____UINT32 : parser kind____UINT32 ___UINT32 = LowParse.Spec.BoundedInt.parse_u32_le
let validate____UINT32 : validator parse____UINT32 = LowParse.Low.BoundedInt.validate_u32_le ()
let read____UINT32 : LPL.leaf_reader parse____UINT32 = LowParse.Low.BoundedInt.read_u32_le


/// UInt64
let ___UINT64 : eqtype = U64.t
inline_for_extraction noextract
let kind____UINT64 : parser_kind true = LowParse.Spec.Int.parse_u64_kind
let parse____UINT64 : parser kind____UINT64 ___UINT64 = LowParse.Spec.Int.parse_u64_le
let validate____UINT64 : validator parse____UINT64 = LowParse.Low.Int.validate_u64_le ()
let read____UINT64 : LPL.leaf_reader parse____UINT64 = LowParse.Low.Int.read_u64_le

inline_for_extraction noextract
let kind_unit : parser_kind false = LPC.parse_ret_kind
let parse_unit : parser kind_unit unit = parse_ret ()
inline_for_extraction noextract
let validate_unit : validator parse_unit = validate_ret
inline_for_extraction noextract
let read_unit
  : LPL.leaf_reader (parse_ret ())
  = LPLC.read_ret ()

////////////////////////////////////////////////////////////////////////////////
//Convenience lemmas for bounded arithmetic, especially on bitfields
////////////////////////////////////////////////////////////////////////////////

let max_int_sizes
  : squash FStar.UInt.(
      max_int 10 == 1023 /\
      max_int 8 == 255
    )
  = let open FStar.UInt in
    normalize_term_spec (max_int 10)
