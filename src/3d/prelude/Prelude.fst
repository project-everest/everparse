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
let parse_dep_pair #nz1 (#k1:parser_kind nz1) (#t1: Type) (p1: parser k1 t1)
                   #nz2 (#k2:parser_kind nz2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> parser k2 (t2 x))
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

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_left #nz  (#k:parser_kind nz) #t (p:parser k t)
                      #nz' (k':parser_kind nz')
  : Tot (parser (glb k' k) t)
  = LP.weaken (glb k' k) p

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken_right #nz  (#k:parser_kind nz) #t (p:parser k t)
                       #nz' (k':parser_kind nz')
  : Tot (parser (glb k k') t)
  = LP.weaken (glb k k') p

inline_for_extraction
noextract
let impos_kind : parser_kind true =
  LPC.(strong_parser_kind 1 1 (Some ParserKindMetadataFail))

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
let parse_impos ()
  : parser impos_kind False
  = let p : LP.bare_parser False = fun b -> None in
    LP.parser_kind_prop_equiv impos_kind p;
    p

let parse_ite #nz (#k:parser_kind nz) (#a:Type) (#b:Type) (e:bool)
              (p1:squash e -> parser k a)
              (p2:squash (not e) -> parser k b)
  : Tot (parser k (t_ite e a b))
  = if e then p1 () else p2 ()


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
module B32 = FStar.Bytes
let t_at_most (n:U32.t) (t:Type) = t & B32.bytes
let kind_t_at_most : parser_kind false = kind_nlist
inline_for_extraction noextract
let parse_t_at_most (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Tot (parser kind_t_at_most (t_at_most n t))
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            (LowParse.Spec.FLData.parse_fldata 
                (LPC.nondep_then p LowParse.Spec.Bytes.parse_all_bytes)
                (U32.v n))
            #false
            kind_t_at_most

////////////////////////////////////////////////////////////////////////////////
let t_exact (n:U32.t) (t:Type) = t
let kind_t_exact : parser_kind false = kind_nlist
inline_for_extraction noextract
let parse_t_exact (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Tot (parser kind_t_exact (t_exact n t))
  = let open LowParse.Spec.FLData in
    let open LowParse.Spec.List in
    parse_weaken
            #false 
            (LowParse.Spec.FLData.parse_fldata 
                p
                (U32.v n))
            #false
            kind_t_exact

////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let reader #nz (#k:parser_kind nz) #t (p:parser k t) = LPLC.leaf_reader p

inline_for_extraction noextract
let read_filter #nz
                (#k: parser_kind nz)
                (#t: Type)
                (#p: parser k t)
                (p32: LPL.leaf_reader p)
                (f: (t -> bool))
    : LPL.leaf_reader (parse_filter p f)
    = LPLC.read_filter p32 f

// ////////////////////////////////////////////////////////////////////////////////
// // Validators
// ////////////////////////////////////////////////////////////////////////////////
inline_for_extraction noextract
let validator #nz (#k:parser_kind nz) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator #k #t p

inline_for_extraction noextract
let validator_no_read #nz (#k:parser_kind nz) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator_no_read #k #t p

[@ CMacro ]
let validator_error_impossible : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 3uL)

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
let validate_nlist_total_constant_size_mod_ok (n:U32.t) (#k:parser_kind true) (#t: Type) (p:parser k t)
  : Pure (validator_no_read (parse_nlist n p))
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
           parse_nlist_total_fixed_size_kind_correct n p;
           LPL.valid_facts (parse_nlist n p) h sl (LPL.uint64_to_uint32 pos);
           LPL.valid_facts (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) h sl (LPL.uint64_to_uint32 pos)
         in
         LPL.validate_total_constant_size_no_read (LP.strengthen (LP.total_constant_size_parser_kind (U32.v n)) (parse_nlist n p)) (FStar.Int.Cast.uint32_to_uint64 n) () sl len pos
      )

[@ CMacro ]
let validator_error_list_size_not_multiple : LPL.validator_error = normalize_term (LPL.set_validator_error_kind 0uL 4uL)

inline_for_extraction noextract
let validate_nlist_constant_size_mod_ko (n:U32.t) (#k:parser_kind true) #t (p:parser k t)
  : Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    U32.v n % k.LP.parser_kind_low <> 0
  ))
  (ensures (fun _ -> True))
= 
  (fun #rrel #rel sl len pos ->
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
  : Pure (validator_no_read (parse_nlist n p))
  (requires (
    let open LP in
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal /\
    k.parser_kind_low < 4294967296
  ))
  (ensures (fun _ -> True))
= fun #rrel #rel sl len pos ->
  if n `U32.rem` U32.uint_to_t k.LP.parser_kind_low = 0ul
  then validate_nlist_total_constant_size_mod_ok n p sl len pos
  else validate_nlist_constant_size_mod_ko n p sl len pos

inline_for_extraction noextract
let validate_nlist_total_constant_size (n_is_const: bool) (n:U32.t) (#k:parser_kind true) (#t: Type) (p:parser k t)
: Pure (validator_no_read (parse_nlist n p))
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

////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////

/// UINT8
inline_for_extraction noextract
let kind____UINT8 : parser_kind true= LowParse.Spec.Int.parse_u8_kind
let parse____UINT8 : parser kind____UINT8 ___UINT8 = LowParse.Spec.Int.parse_u8
let read____UINT8 : reader parse____UINT8 = LowParse.Low.Int.read_u8

/// UInt16
inline_for_extraction noextract
let kind____UINT16 : parser_kind true = LowParse.Spec.BoundedInt.parse_u16_kind
let parse____UINT16 : parser kind____UINT16 ___UINT16 = LowParse.Spec.BoundedInt.parse_u16_le
let read____UINT16 : LPL.leaf_reader parse____UINT16 = LowParse.Low.BoundedInt.read_u16_le

/// UInt32
inline_for_extraction noextract
let kind____UINT32 : parser_kind true = LowParse.Spec.BoundedInt.parse_u32_kind
let parse____UINT32 : parser kind____UINT32 ___UINT32 = LowParse.Spec.BoundedInt.parse_u32_le
let read____UINT32 : LPL.leaf_reader parse____UINT32 = LowParse.Low.BoundedInt.read_u32_le


/// UInt64
inline_for_extraction noextract
let kind____UINT64 : parser_kind true = LowParse.Spec.Int.parse_u64_kind
let parse____UINT64 : parser kind____UINT64 ___UINT64 = LowParse.Spec.Int.parse_u64_le
let read____UINT64 : LPL.leaf_reader parse____UINT64 = LowParse.Low.Int.read_u64_le
  
inline_for_extraction noextract
let read_unit
  : LPL.leaf_reader (parse_ret ())
  = LPLC.read_ret ()

inline_for_extraction noextract
let u8_add _ x y = UInt8.add x y

inline_for_extraction noextract
let u8_sub _ x y = UInt8.sub x y

inline_for_extraction noextract
let u8_mul _ x y = UInt8.mul x y

inline_for_extraction noextract
let u8_div _ x y = UInt8.div x y

inline_for_extraction noextract
let u16_add _ x y = UInt16.add x y

inline_for_extraction noextract
let u16_sub _ x y = UInt16.sub x y

inline_for_extraction noextract
let u16_mul _ x y = UInt16.mul x y

inline_for_extraction noextract
let u16_div _ x y = UInt16.div x y

inline_for_extraction noextract
let u32_add _ x y = UInt32.add x y

inline_for_extraction noextract
let u32_sub _ x y = UInt32.sub x y

inline_for_extraction noextract
let u32_mul _ x y = UInt32.mul x y

inline_for_extraction noextract
let u32_div _ x y = UInt32.div x y

inline_for_extraction noextract
let u64_add _ x y = UInt64.add x y

inline_for_extraction noextract
let u64_sub _ x y = UInt64.sub x y

inline_for_extraction noextract
let u64_mul _ x y = UInt64.mul x y

inline_for_extraction noextract
let u64_div _ x y = UInt64.div x y


// inline_for_extraction noextract
// let u8_add (r:Prims.range) (x y:UInt8.t)
//   : Pure UInt8.t
//       (requires labeled r "Cannot verify u8 addition" (UInt.size (UInt8.v x + UInt8.v y) UInt8.n))
//       (ensures fun z -> UInt8.v z == UInt8.v x + UInt8.v y)
//   = UInt8.add x y

// inline_for_extraction noextract
// let u8_add (r:Prims.range) (x y:UInt8.t)
//   : Pure UInt8.t
//       (requires labeled r "Cannot verify u8 addition" (UInt.size (UInt8.v x + UInt8.v y) UInt8.n))
//       (ensures fun z -> UInt8.v z == UInt8.v x + UInt8.v y)
//   = UInt8.add x y


// noeq
// type t_uint = {
//   n   : nat;
//   t   : Type0;
//   v   : t -> FStar.UInt.uint_t n;
//   add : x:t -> y:t -> Pure t (requires UInt.size (v x + v y) n) (ensures fun z -> v z == v x + v y);
//   sub : x:t -> y:t -> Pure t (requires UInt.size (v x - v y) n) (ensures fun z -> v z == v x - v y);
//   mul : x:t -> y:t -> Pure t (requires UInt.size (v x * v y) n) (ensures fun z -> v z == v x * v y);
//   div : x:t -> y:t{v y =!= 0} -> Pure t (requires True)            (ensures fun z -> v z == v x / v y);
// }

// noextract
// let u_add (t:t_uint) (msg:string) (r:Prims.range) (x y:t.t)
//   : Pure t.t
//       (requires labeled r msg (UInt.size (t.v x + t.v y) t.n))
//       (ensures fun z -> t.v z == t.v x + t.v y)
//   = t.add x y

// noextract
// let u_sub (t:t_uint) (msg:string) (r:Prims.range) (x y:t.t)
//   : Pure t.t
//       (requires labeled r msg (UInt.size (t.v x - t.v y) t.n))
//       (ensures fun z -> t.v z == t.v x - t.v y)
//   = t.sub x y

// noextract
// let u_mul (t:t_uint) (msg:string) (r:Prims.range) (x y:t.t)
//   : Pure t.t
//       (requires labeled r msg (UInt.size (t.v x * t.v y) t.n))
//       (ensures fun z -> t.v z == t.v x * t.v y)
//   = t.mul x y

// noextract
// let u_div (t:t_uint) (msg:string) (r:Prims.range) (x y:t.t)
//   : Pure t.t
//       (requires labeled r msg (t.v y =!= 0))
//       (ensures fun z -> t.v z == t.v x / t.v y)
//   = t.div x y

// noextract
// let t_8 =
//   let open FStar.UInt8 in
//   { n = n; t = t; v = v; add = add; sub = sub; mul = mul; div = div }

// noextract
// let t_16 =
//   let open FStar.UInt16 in
//   { n = n; t = t; v = v; add = add; sub = sub; mul = mul; div = div }

// noextract
// let t_32 =
//   let open FStar.UInt32 in
//   { n = n; t = t; v = v; add = add; sub = sub; mul = mul; div = div }

// noextract
// let t_64 =
//   let open FStar.UInt64 in
//   { n = n; t = t; v = v; add = add; sub = sub; mul = mul; div = div }

// open FStar.Tactics

// noextract
// let norm () : Tac unit =
//   norm [iota; delta_only [
//     `%u_add; `%u_sub; `%u_mul; `%u_div;    
//     `%Mkt_uint?.n; `%Mkt_uint?.t; `%Mkt_uint?.v; `%Mkt_uint?.add; `%Mkt_uint?.sub; `%Mkt_uint?.mul; `%Mkt_uint?.div;
//     `%t_8; `%t_16; `%t_32; `%t_64 ]
//   ];
//   trefl ()

// unfold let msg_prefix : string = "Cannot verify the safety of "

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u8_add = u_add t_8 (String.concat "" [msg_prefix; "u8 addition"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u16_add = u_add t_16 (String.concat "" [msg_prefix; "u16 addition"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u32_add = u_add t_32 (String.concat "" [msg_prefix; "u32 addition"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u64_add = u_add t_64 (String.concat "" [msg_prefix; "u64 addition"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u8_sub = u_sub t_8 (String.concat "" [msg_prefix; "u8 subtraction"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u16_sub = u_sub t_16 (String.concat "" [msg_prefix; "u16 subtraction"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u32_sub = u_sub t_32 (String.concat "" [msg_prefix; "u32 subtraction"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u64_sub = u_sub t_64 (String.concat "" [msg_prefix; "u64 subtraction"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u8_mul = u_mul t_8 (String.concat "" [msg_prefix; "u8 multiplication"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u16_mul = u_mul t_16 (String.concat "" [msg_prefix; "u16 multiplication"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u32_mul = u_mul t_32 (String.concat "" [msg_prefix; "u32 multiplication"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u64_mul = u_mul t_64 (String.concat "" [msg_prefix; "u64 multiplication"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u8_div = u_div t_8 (String.concat "" [msg_prefix; "u8 division"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u16_div = u_div t_16 (String.concat "" [msg_prefix; "u16 division"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u32_div = u_div t_32 (String.concat "" [msg_prefix; "u32 division"])

// [@@postprocess_with norm]
// inline_for_extraction noextract
// let u64_div = u_div t_64 (String.concat "" [msg_prefix; "u64 division"])
