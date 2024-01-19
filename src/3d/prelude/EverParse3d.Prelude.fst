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
module EverParse3d.Prelude
friend EverParse3d.Kinds
module BF = LowParse.BitFields
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Low.Base
module LPLC = LowParse.Low.Combinators
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////

let parser k t = LP.parser k t

let is_weaker_than #nz1 #wk1 (k:parser_kind nz1 wk1)
                   #nz2 #wk2 (k':parser_kind nz2 wk2) = k `LP.is_weaker_than` k'

let is_weaker_than_refl #nz #wk (k:parser_kind nz wk)
  : Lemma (ensures (is_weaker_than k k))
          [SMTPat (is_weaker_than k k)]
  = ()

let is_weaker_than_glb #nz1 #wk1 (k1:parser_kind nz1 wk1)
                       #nz2 #wk2 (k2:parser_kind nz2 wk2)
  : Lemma (is_weaker_than (glb k1 k2) k1 /\
           is_weaker_than (glb k1 k2) k2)
          [SMTPatOr
            [[SMTPat (is_weaker_than (glb k1 k2) k1)];
             [SMTPat (is_weaker_than (glb k1 k2) k2)]]]
  = ()

/// Parser: return
inline_for_extraction noextract
let parse_ret #t (v:t)
  : Tot (parser ret_kind t)
  = LPC.parse_ret #t v

/// Parser: bind
inline_for_extraction noextract
let parse_dep_pair p1 p2
  = LPC.parse_dtuple2 p1 p2

/// Parser: sequencing
inline_for_extraction noextract
let parse_pair p1 p2
  = LPC.nondep_then p1 p2

/// Parser: map
let injective_map a b = (a -> Tot b) //{LPC.synth_injective f}

inline_for_extraction noextract
let parse_filter p f
  = LPC.parse_filter p f

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken #nz #wk (#k:parser_kind nz wk) #t (p:parser k t)
                 #nz' #wk' (k':parser_kind nz' wk' {k' `is_weaker_than` k})
  : Tot (parser k' t)
  = LP.weaken k' p

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_left #nz #wk #k p k'
  = LP.weaken (glb k' k) p

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_right #nz #wk #k p k'
  = LP.weaken (glb k k') p

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
let parse_impos ()
  : parser impos_kind False
  = let p : LP.bare_parser False = fun b -> None in
    LP.parser_kind_prop_equiv impos_kind p;
    p

let parse_ite e p1 p2
  = if e then p1 () else p2 ()

let serializer p = LP.serializer p

let serialize_dep_pair p1 p2 s1 s2 = LPC.serialize_dtuple2 s1 s2

let serialize_pair p1 p2 s1 s2 = LPC.serialize_nondep_then s1 s2

let serialize_filter p f s = LPC.serialize_filter s f

inline_for_extraction noextract
let serialize_weaken_left #nz #wk #k p k' s b = s b

inline_for_extraction noextract
let serialize_weaken_right #nz #wk #k p k' s b = s b

let serialize_impos () (t:False) = Seq.empty

let serialize_ite e p1 p2 s1 s2 =
  if e then s1 () else s2 ()

let nlist (n:U32.t) t #k #p s =
  LowParse.Spec.FLData.parse_fldata_strong_t (LowParse.Spec.List.serialize_list p s) (U32.v n)

inline_for_extraction noextract
let parse_nlist n s
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false #WeakKindStrongPrefix #_ #_
            (parse_fldata_strong (serialize_list _ s) (U32.v n))
            #false kind_nlist

let serialize_nlist n s b =
  LowParse.Spec.FLData.serialize_fldata_strong _ _ b

let all_bytes = Seq.seq LP.byte
let parse_all_bytes' 
  : LP.bare_parser all_bytes 
  = fun input -> Some (input, (Seq.length input <: LP.consumed_length input))
let parse_all_bytes =
  LP.parser_kind_prop_equiv kind_all_bytes parse_all_bytes';
  parse_all_bytes'
let serialize_all_bytes b = b

////////////////////////////////////////////////////////////////////////////////
module B32 = FStar.Bytes
let t_at_most (n:U32.t) (t:Type) s =
  LowParse.Spec.FLData.parse_fldata_strong_t
    (LPC.serialize_nondep_then s serialize_all_bytes) (U32.v n)

inline_for_extraction noextract
let parse_t_at_most n #nz #k #t #p s
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            #WeakKindStrongPrefix
            (LowParse.Spec.FLData.parse_fldata_strong
                (LPC.serialize_nondep_then s serialize_all_bytes)
                (U32.v n))
            #false
            kind_t_at_most

let serialize_t_at_most n s b =
  LowParse.Spec.FLData.serialize_fldata_strong _ _ b

////////////////////////////////////////////////////////////////////////////////
let t_exact n t s =
  LowParse.Spec.FLData.parse_fldata_strong_t s (U32.v n)
inline_for_extraction noextract
let parse_t_exact n #nz #k #t #p s
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            #WeakKindStrongPrefix
            (LowParse.Spec.FLData.parse_fldata_strong
                s
                (U32.v n))
            #false
            kind_t_exact

let serialize_t_exact n s b =
  LowParse.Spec.FLData.serialize_fldata_strong _ _ b

////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let reader p = LPLC.leaf_reader p

inline_for_extraction noextract
let read_filter p32 f
    = LPLC.read_filter p32 f

let read_impos : reader (parse_impos()) = 
  fun #rrel #rel sl pos -> 
    let h = FStar.HyperStack.ST.get() in
    assert (LPLC.valid (parse_impos()) h sl pos);
    LowParse.Low.Base.Spec.valid_equiv (parse_impos()) h sl pos;
    false_elim ()
  
// ////////////////////////////////////////////////////////////////////////////////
// // Validators
// ////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let validator #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator #k #t p

inline_for_extraction noextract
let validator_no_read #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator_no_read #k #t p

let parse_nlist_total_fixed_size_aux
  (n:U32.t) (#k:parser_kind true WeakKindStrongPrefix) #t (p:parser k t) (s:serializer p)
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
    Some? (LP.parse (parse_nlist n s) x)
  ))
= let x' = Seq.slice x 0 (U32.v n) in
  let cnt = (U32.v n / k.LP.parser_kind_low) in
  FStar.Math.Lemmas.lemma_div_exact (U32.v n) k.LP.parser_kind_low;
  FStar.Math.Lemmas.nat_over_pos_is_nat (U32.v n) k.LP.parser_kind_low;
  LowParse.Spec.List.parse_list_total_constant_size p cnt x';
  LP.parser_kind_prop_equiv LowParse.Spec.List.parse_list_kind (LowParse.Spec.List.parse_list p)

let parse_nlist_total_fixed_size_kind_correct
  (n:U32.t) (#k:parser_kind true WeakKindStrongPrefix) #t (p:parser k t) (s:serializer p)
: Lemma
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.parser_kind_low == 0 /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
    LP.parser_kind_prop (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n s)
  ))
= LP.parser_kind_prop_equiv (LowParse.Spec.FLData.parse_fldata_kind (U32.v n) LowParse.Spec.List.parse_list_kind) (parse_nlist n s);
  LP.parser_kind_prop_equiv (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n s);
  Classical.forall_intro (Classical.move_requires (parse_nlist_total_fixed_size_aux n p s))

inline_for_extraction noextract
let validate_nlist_total_constant_size_mod_ok (n:U32.t) (#k:parser_kind true WeakKindStrongPrefix) (#t: Type) (p:parser k t) (s:serializer p)
  : Pure (validator_no_read (parse_nlist n s))
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
      (fun #rrel #rel sl len pos ->
         let h = FStar.HyperStack.ST.get () in
         [@inline_let]
         let _ =
           parse_nlist_total_fixed_size_kind_correct n p s;
           LPL.valid_facts (parse_nlist n s) h sl (LPL.uint64_to_uint32 pos);
           LPL.valid_facts (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n s)) h sl (LPL.uint64_to_uint32 pos)
         in
         LPL.validate_total_constant_size_no_read (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n s)) (FStar.Int.Cast.uint32_to_uint64 n) () sl len pos
      )

module LUT = LowParse.Spec.ListUpTo

inline_for_extraction
noextract
let cond_string_up_to
  (#t: eqtype)
  (terminator: t)
  (x: t)
: Tot bool
= x = terminator

let cstring
  (t: eqtype)
  (terminator: t)
: Tot Type0
= LUT.parse_list_up_to_t (cond_string_up_to terminator)

let parse_string
  #k #t p terminator
=
  LowParse.Spec.Base.parser_kind_prop_equiv k p;
  LP.weaken parse_string_kind (LUT.parse_list_up_to (cond_string_up_to terminator) p (fun _ _ _ -> ()))

let serialize_string #k #t #p s terminator =
  LowParse.Spec.Base.parser_kind_prop_equiv k p;
  let s = LUT.serialize_list_up_to (cond_string_up_to terminator) (fun _ _ _ -> ()) s in
  fun b -> s b

inline_for_extraction noextract
let is_zero (x: FStar.UInt8.t) : Tot bool = x = 0uy

let all_zeros = list (LowParse.Spec.Combinators.parse_filter_refine is_zero)
let parse_all_zeros = LowParse.Spec.List.parse_list (LowParse.Spec.Combinators.parse_filter LowParse.Spec.Int.parse_u8 is_zero)
let serialize_all_zeros = LowParse.Spec.List.serialize_list _ (LowParse.Spec.Combinators.serialize_filter LowParse.Spec.Int.serialize_u8 is_zero)


////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////

/// UINT8
let parse____UINT8 = LowParse.Spec.Int.parse_u8
let serialize____UINT8 = LowParse.Spec.Int.serialize_u8
let read____UINT8 = LowParse.Low.Int.read_u8

/// UINT8BE
let parse____UINT8BE = LowParse.Spec.Int.parse_u8
let serialize____UINT8BE = LowParse.Spec.Int.serialize_u8
let read____UINT8BE = LowParse.Low.Int.read_u8

/// UInt16BE
let parse____UINT16BE = LowParse.Spec.Int.parse_u16
let serialize____UINT16BE = LowParse.Spec.Int.serialize_u16
let read____UINT16BE = LowParse.Low.Int.read_u16

/// UInt32BE
let parse____UINT32BE = LowParse.Spec.Int.parse_u32
let serialize____UINT32BE = LowParse.Spec.Int.serialize_u32
let read____UINT32BE = LowParse.Low.Int.read_u32

/// UInt64BE
let parse____UINT64BE = LowParse.Spec.Int.parse_u64
let serialize____UINT64BE = LowParse.Spec.Int.serialize_u64
let read____UINT64BE = LowParse.Low.Int.read_u64


/// UInt16
let parse____UINT16 = LowParse.Spec.BoundedInt.parse_u16_le
let serialize____UINT16 = LowParse.Spec.BoundedInt.serialize_u16_le
let read____UINT16 = LowParse.Low.BoundedInt.read_u16_le

/// UInt32
let parse____UINT32 = LowParse.Spec.BoundedInt.parse_u32_le
let serialize____UINT32 = LowParse.Spec.BoundedInt.serialize_u32_le
let read____UINT32 = LowParse.Low.BoundedInt.read_u32_le


/// UInt64
let parse____UINT64 = LowParse.Spec.Int.parse_u64_le
let serialize____UINT64 = LowParse.Spec.Int.serialize_u64_le
let read____UINT64 = LowParse.Low.Int.read_u64_le

let serialize_unit () = Seq.empty
  
inline_for_extraction noextract
let read_unit
  : LPL.leaf_reader (parse_ret ())
  = LPLC.read_ret ()
