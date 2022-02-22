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
include EverParse3d.Prelude.StaticHeader
include EverParse3d.Kinds
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = FStar.Int.Cast

let pow2_values (x:nat) : Lemma
  (let p = pow2 x in
   match x with
   | 0  -> p=1
   | 1  -> p=2
   | 2  -> p=4
   | 3  -> p=8
   | 4  -> p=16
   | 5  -> p=32
   | 6  -> p=64
   | 7  -> p=128
   | 8  -> p=256
   | _ -> True)
  [SMTPat (pow2 x)]
  = norm_spec [delta;zeta;primops] (pow2 0);
    norm_spec [delta;zeta;primops] (pow2 1);
    norm_spec [delta;zeta;primops] (pow2 2);
    norm_spec [delta;zeta;primops] (pow2 3);
    norm_spec [delta;zeta;primops] (pow2 4);
    norm_spec [delta;zeta;primops] (pow2 5);
    norm_spec [delta;zeta;primops] (pow2 6);
    norm_spec [delta;zeta;primops] (pow2 7);
    norm_spec [delta;zeta;primops] (pow2 8)

////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////


[@@erasable]
inline_for_extraction
noextract
val parser (#nz:bool) (#wk: weak_kind) (k:parser_kind nz wk) (t:Type u#r) : Type u#r

inline_for_extraction noextract
val parse_ret (#t:Type) (v:t)
  : Tot (parser ret_kind t)

inline_for_extraction noextract
val parse_dep_pair (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1: Type) (p1: parser k1 t1)
                   (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2: (t1 -> Tot Type)) (p2: (x: t1) -> parser k2 (t2 x))
  : Tot (parser (and_then_kind k1 k2) (dtuple2 t1 t2) )

/// Parser: sequencing
inline_for_extraction noextract
val parse_pair (#nz1:_) (#k1:parser_kind nz1 WeakKindStrongPrefix) (#t1:_) (p1:parser k1 t1)
               (#nz2:_) (#wk2: _) (#k2:parser_kind nz2 wk2) (#t2:_) (p2:parser k2 t2)
  : Tot (parser (and_then_kind k1 k2) (t1 * t2))

/// Parser: filter
let refine t (f:t -> bool) = x:t{f x}

inline_for_extraction noextract
val parse_filter (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (p:parser k t) (f:(t -> bool))
  : Tot (parser (filter_kind k) (refine t f))


inline_for_extraction noextract
val parse_weaken_left (#nz:_) (#wk: _)  (#k:parser_kind nz wk) (#t:_) (p:parser k t)
                      (#nz':_) (#wk': _) (k':parser_kind nz' wk')
  : Tot (parser (glb k' k) t)

inline_for_extraction noextract
val parse_weaken_right (#nz:_) (#wk: _) (#k:parser_kind nz wk) (#t:_) (p:parser k t)
                       (#nz':_) (#wk': _) (k':parser_kind nz' wk')
  : Tot (parser (glb k k') t)

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
val parse_impos (_:unit)
  : parser impos_kind False

let t_ite (e:bool) (a:squash e -> Type) (b:squash (not e) -> Type)
  : Type
  = if e then a() else b()

val parse_ite (#nz:_) (#wk: _) (#k:parser_kind nz wk)
              (e:bool)
              (#a:squash e -> Type)
              (#b:squash (not e) -> Type)
              (p1:squash e -> parser k (a()))
              (p2:squash (not e) -> parser k (b()))
  : Tot (parser k (t_ite e a b))

////////////////////////////////////////////////////////////////////////////////
// Variable-sized list whose size in bytes is exactly n
////////////////////////////////////////////////////////////////////////////////
val nlist (n:U32.t) (t:Type u#r) : Type u#r

inline_for_extraction noextract
val parse_nlist (n:U32.t) (#wk: _) (#k:parser_kind true wk) (#t:_) (p:parser k t)
  : Tot (parser kind_nlist (nlist n t))

/////
// Parse all of the remaining bytes of the input buffer
/////
noextract
val all_bytes: Type0

val parse_all_bytes: parser kind_all_bytes all_bytes

////////////////////////////////////////////////////////////////////////////////
// Variable-sized element whose size in bytes is at most n
////////////////////////////////////////////////////////////////////////////////
val t_at_most (n:U32.t) (t:Type u#r) : Type u#r

inline_for_extraction noextract
val parse_t_at_most (n:U32.t) (#nz: _) (#wk: _) (#k:parser_kind nz wk) (#t:_) (p:parser k t)
  : Tot (parser kind_t_at_most (t_at_most n t))

////////////////////////////////////////////////////////////////////////////////
// Variable-sized element whose size in bytes is exactly n
////////////////////////////////////////////////////////////////////////////////
val t_exact (n:U32.t) (t:Type u#r) : Type u#r

inline_for_extraction noextract
val parse_t_exact (n:U32.t) (#nz:bool) (#wk: _) (#k:parser_kind nz wk) (#t:_) (p:parser k t)
  : Tot (parser kind_t_exact (t_exact n t))

////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
val reader (#nz:_) (#k:parser_kind nz WeakKindStrongPrefix) (#t:_) (p:parser k t) : Type u#1

inline_for_extraction noextract
val read_filter (#nz:_)
                (#k: parser_kind nz WeakKindStrongPrefix)
                (#t: Type)
                (#p: parser k t)
                (p32: reader p)
                (f: (t -> bool))
    : reader (parse_filter p f)

inline_for_extraction noextract
val read_impos : reader (parse_impos())

/// Parse a zero-terminated string

noextract
val cstring
  (t: eqtype)
  (terminator: t)
: Tot Type0

val parse_string
  (#k: parser_kind true WeakKindStrongPrefix)
  (#t: eqtype)
  (p: parser k t)
  (terminator: t)
: Tot (parser parse_string_kind (cstring t terminator))

noextract
val all_zeros: Type0

val parse_all_zeros: parser kind_all_zeros all_zeros

////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction
let ___Bool = bool

/// UINT8
let ___UINT8 : eqtype = FStar.UInt8.t
val parse____UINT8 : parser kind____UINT8 ___UINT8
val read____UINT8 : reader parse____UINT8

// Big-endian (or "network order")

/// UInt16BE
let ___UINT16BE : eqtype = U16.t
val parse____UINT16BE : parser kind____UINT16BE ___UINT16BE
val read____UINT16BE : reader parse____UINT16BE

/// UInt32BE
let ___UINT32BE : eqtype = U32.t
val parse____UINT32BE : parser kind____UINT32BE ___UINT32BE
val read____UINT32BE : reader parse____UINT32BE

/// UInt64BE
let ___UINT64BE : eqtype = U64.t
val parse____UINT64BE : parser kind____UINT64BE ___UINT64BE
val read____UINT64BE : reader parse____UINT64BE

// Little-endian

/// UInt16
let ___UINT16 : eqtype = U16.t
val parse____UINT16 : parser kind____UINT16 ___UINT16
val read____UINT16 : reader parse____UINT16

/// UInt32
let ___UINT32 : eqtype = U32.t
val parse____UINT32 : parser kind____UINT32 ___UINT32
val read____UINT32 : reader parse____UINT32

/// UInt64
let ___UINT64 : eqtype = U64.t
val parse____UINT64 : parser kind____UINT64 ___UINT64
val read____UINT64 : reader parse____UINT64

let parse_unit
  : parser kind_unit unit
  = parse_ret ()

inline_for_extraction noextract
val read_unit
  : reader (parse_ret ())

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


(*
 * AR: scaffolding for getting arithmetic error locations in the 3d file
 *)

(*** UInt8 operations ***)
unfold noextract
let u8_add (r:Prims.range) (x y:UInt8.t)
  : Pure UInt8.t
      (requires labeled r "Cannot verify u8 addition" (UInt.size (UInt8.v x + UInt8.v y) UInt8.n))
      (ensures fun z -> UInt8.v z == UInt8.v x + UInt8.v y)
  = UInt8.add x y

unfold noextract
let u8_sub (r:Prims.range) (x y:UInt8.t)
  : Pure UInt8.t
      (requires labeled r "Cannot verify u8 subtraction" (UInt.size (UInt8.v x - UInt8.v y) UInt8.n))
      (ensures fun z -> UInt8.v z == UInt8.v x - UInt8.v y)
  = UInt8.sub x y

unfold noextract
let u8_mul (r:Prims.range) (x y:UInt8.t)
  : Pure UInt8.t
      (requires labeled r "Cannot verify u8 multiplication" (UInt.size (UInt8.v x `Prims.op_Multiply` UInt8.v y) UInt8.n))
      (ensures fun z -> UInt8.v z == UInt8.v x `Prims.op_Multiply` UInt8.v y)
  = UInt8.mul x y

unfold noextract
let u8_div (r:Prims.range) (x y:UInt8.t)
  : Pure UInt8.t
      (requires labeled r "Cannot verify u8 division" (UInt8.v y =!= 0))
      (ensures fun z -> UInt8.v z == UInt8.v x / UInt8.v y)
  = UInt8.div x y

(** Euclidean remainder *)
unfold noextract
let u8_rem (r:Prims.range) (x y:UInt8.t)
  : Pure UInt8.t
      (requires labeled r "Cannot verify u8 remainder" (UInt8.v y =!= 0))
      (ensures (fun z -> FStar.UInt.mod (UInt8.v x) (UInt8.v y) == UInt8.v z))
  = UInt8.rem x y

(** Bitwise logical conjunction *)
unfold noextract
let u8_logand (r:Prims.range) (x:UInt8.t) (y:UInt8.t)
  : Pure UInt8.t
    (requires True)
    (ensures (fun z -> UInt8.v x `UInt.logand` UInt8.v y == UInt8.v z))
  = UInt8.logand x y

(** Bitwise logical exclusive-or *)
unfold noextract
let u8_logxor (r:Prims.range) (x:UInt8.t) (y:UInt8.t)
  : Pure UInt8.t
    (requires True)
    (ensures (fun z -> UInt8.v x `UInt.logxor` UInt8.v y == UInt8.v z))
  = UInt8.logxor x y

(** Bitwise logical disjunction *)
unfold noextract
let u8_logor (r:Prims.range) (x:UInt8.t) (y:UInt8.t)
  : Pure UInt8.t
    (requires True)
    (ensures (fun z -> UInt8.v x `UInt.logor` UInt8.v y == UInt8.v z))
  = UInt8.logor x y

(** Bitwise logical negation *)
unfold noextract
let u8_lognot (r:Prims.range) (x:UInt8.t)
  : Pure UInt8.t
    (requires True)
    (ensures (fun z -> UInt.lognot (UInt8.v x) == UInt8.v z))
  = UInt8.lognot x

(** Shift right with zero fill, shifting at most the integer width *)
unfold noextract
let u8_shift_right (r:Prims.range) (a:UInt8.t) (s:UInt32.t)
  : Pure UInt8.t
    (requires labeled r "Cannot verify u8 shift right" (UInt32.v s < UInt8.n))
    (ensures (fun c -> FStar.UInt.shift_right (UInt8.v a) (UInt32.v s) = UInt8.v c))
  = UInt8.shift_right a s

(** Shift left with zero fill, shifting at most the integer width *)
unfold noextract
let u8_shift_left (r:Prims.range) (a:UInt8.t) (s:UInt32.t)
  : Pure UInt8.t
    (requires labeled r "Cannot verify u8 shift left" (UInt32.v s < UInt8.n))
    (ensures (fun c -> FStar.UInt.shift_left (UInt8.v a) (UInt32.v s) = UInt8.v c))
  = UInt8.shift_left a s

(*** UInt16 operations ***)

unfold noextract
let u16_add (r:Prims.range) (x y:UInt16.t)
  : Pure UInt16.t
      (requires labeled r "Cannot verify u16 addition" (UInt.size (UInt16.v x + UInt16.v y) UInt16.n))
      (ensures fun z -> UInt16.v z == UInt16.v x + UInt16.v y)
  = UInt16.add x y

unfold noextract
let u16_sub (r:Prims.range) (x y:UInt16.t)
  : Pure UInt16.t
      (requires labeled r "Cannot verify u16 subtraction" (UInt.size (UInt16.v x - UInt16.v y) UInt16.n))
      (ensures fun z -> UInt16.v z == UInt16.v x - UInt16.v y)
  = UInt16.sub x y

unfold noextract
let u16_mul (r:Prims.range) (x y:UInt16.t)
  : Pure UInt16.t
      (requires labeled r "Cannot verify u16 multiplication" (UInt.size (UInt16.v x `Prims.op_Multiply` UInt16.v y) UInt16.n))
      (ensures fun z -> UInt16.v z == UInt16.v x `Prims.op_Multiply` UInt16.v y)
  = UInt16.mul x y

unfold noextract
let u16_div (r:Prims.range) (x y:UInt16.t)
  : Pure UInt16.t
      (requires labeled r "Cannot verify u16 division" (UInt16.v y =!= 0))
      (ensures fun z -> UInt16.v z == UInt16.v x / UInt16.v y)
  = UInt16.div x y

(** Euclidean remainder *)
unfold noextract
let u16_rem (r:Prims.range) (x y:UInt16.t)
  : Pure UInt16.t
      (requires labeled r "Cannot verify u16 remainder" (UInt16.v y =!= 0))
      (ensures (fun z -> FStar.UInt.mod (UInt16.v x) (UInt16.v y) == UInt16.v z))
  = UInt16.rem x y

(** Bitwise logical conjunction *)
unfold noextract
let u16_logand (r:Prims.range) (x:UInt16.t) (y:UInt16.t)
  : Pure UInt16.t
    (requires True)
    (ensures (fun z -> UInt16.v x `UInt.logand` UInt16.v y == UInt16.v z))
  = UInt16.logand x y

(** Bitwise logical exclusive-or *)
unfold noextract
let u16_logxor (r:Prims.range) (x:UInt16.t) (y:UInt16.t)
  : Pure UInt16.t
    (requires True)
    (ensures (fun z -> UInt16.v x `UInt.logxor` UInt16.v y == UInt16.v z))
  = UInt16.logxor x y

(** Bitwise logical disjunction *)
unfold noextract
let u16_logor (r:Prims.range) (x:UInt16.t) (y:UInt16.t)
  : Pure UInt16.t
    (requires True)
    (ensures (fun z -> UInt16.v x `UInt.logor` UInt16.v y == UInt16.v z))
  = UInt16.logor x y

(** Bitwise logical negation *)
unfold noextract
let u16_lognot (r:Prims.range) (x:UInt16.t)
  : Pure UInt16.t
    (requires True)
    (ensures (fun z -> UInt.lognot (UInt16.v x) == UInt16.v z))
  = UInt16.lognot x

(** Shift right with zero fill, shifting at most the integer width *)
unfold noextract
let u16_shift_right (r:Prims.range) (a:UInt16.t) (s:UInt32.t)
  : Pure UInt16.t
    (requires labeled r "Cannot verify u16 shift right" (UInt32.v s < UInt16.n))
    (ensures (fun c -> FStar.UInt.shift_right (UInt16.v a) (UInt32.v s) = UInt16.v c))
  = UInt16.shift_right a s

(** Shift left with zero fill, shifting at most the integer width *)
unfold noextract
let u16_shift_left (r:Prims.range) (a:UInt16.t) (s:UInt32.t)
  : Pure UInt16.t
    (requires labeled r "Cannot verify u16 shift left" (UInt32.v s < UInt16.n))
    (ensures (fun c -> FStar.UInt.shift_left (UInt16.v a) (UInt32.v s) = UInt16.v c))
  = UInt16.shift_left a s

(*** UInt32 operations ***)


unfold noextract
let u32_add (r:Prims.range) (x y:UInt32.t)
  : Pure UInt32.t
      (requires labeled r "Cannot verify u32 addition" (UInt.size (UInt32.v x + UInt32.v y) UInt32.n))
      (ensures fun z -> UInt32.v z == UInt32.v x + UInt32.v y)
  = UInt32.add x y

unfold noextract
let u32_sub (r:Prims.range) (x y:UInt32.t)
  : Pure UInt32.t
      (requires labeled r "Cannot verify u32 subtraction" (UInt.size (UInt32.v x - UInt32.v y) UInt32.n))
      (ensures fun z -> UInt32.v z == UInt32.v x - UInt32.v y)
  = UInt32.sub x y

unfold noextract
let u32_mul (r:Prims.range) (x y:UInt32.t)
  : Pure UInt32.t
      (requires labeled r "Cannot verify u32 multiplication" (UInt.size (UInt32.v x `Prims.op_Multiply` UInt32.v y) UInt32.n))
      (ensures fun z -> UInt32.v z == UInt32.v x `Prims.op_Multiply` UInt32.v y)
  = UInt32.mul x y

unfold noextract
let u32_div (r:Prims.range) (x y:UInt32.t)
  : Pure UInt32.t
      (requires labeled r "Cannot verify u32 division" (UInt32.v y =!= 0))
      (ensures fun z -> UInt32.v z == UInt32.v x / UInt32.v y)
  = UInt32.div x y

(** Euclidean remainder *)
unfold noextract
let u32_rem (r:Prims.range) (x y:UInt32.t)
  : Pure UInt32.t
      (requires labeled r "Cannot verify u32 remainder" (UInt32.v y =!= 0))
      (ensures (fun z -> FStar.UInt.mod (UInt32.v x) (UInt32.v y) == UInt32.v z))
  = UInt32.rem x y

(** Bitwise logical conjunction *)
unfold noextract
let u32_logand (r:Prims.range) (x:UInt32.t) (y:UInt32.t)
  : Pure UInt32.t
    (requires True)
    (ensures (fun z -> UInt32.v x `UInt.logand` UInt32.v y == UInt32.v z))
  = UInt32.logand x y

(** Bitwise logical exclusive-or *)
unfold noextract
let u32_logxor (r:Prims.range) (x:UInt32.t) (y:UInt32.t)
  : Pure UInt32.t
    (requires True)
    (ensures (fun z -> UInt32.v x `UInt.logxor` UInt32.v y == UInt32.v z))
  = UInt32.logxor x y

(** Bitwise logical disjunction *)
unfold noextract
let u32_logor (r:Prims.range) (x:UInt32.t) (y:UInt32.t)
  : Pure UInt32.t
    (requires True)
    (ensures (fun z -> UInt32.v x `UInt.logor` UInt32.v y == UInt32.v z))
  = UInt32.logor x y

(** Bitwise logical negation *)
unfold noextract
let u32_lognot (r:Prims.range) (x:UInt32.t)
  : Pure UInt32.t
    (requires True)
    (ensures (fun z -> UInt.lognot (UInt32.v x) == UInt32.v z))
  = UInt32.lognot x

(** Shift right with zero fill, shifting at most the integer width *)
unfold noextract
let u32_shift_right (r:Prims.range) (a:UInt32.t) (s:UInt32.t)
  : Pure UInt32.t
    (requires labeled r "Cannot verify u32 shift right" (UInt32.v s < UInt32.n))
    (ensures (fun c -> FStar.UInt.shift_right (UInt32.v a) (UInt32.v s) = UInt32.v c))
  = UInt32.shift_right a s

(** Shift left with zero fill, shifting at most the integer width *)
unfold noextract
let u32_shift_left (r:Prims.range) (a:UInt32.t) (s:UInt32.t)
  : Pure UInt32.t
    (requires labeled r "Cannot verify u32 shift left" (UInt32.v s < UInt32.n))
    (ensures (fun c -> FStar.UInt.shift_left (UInt32.v a) (UInt32.v s) = UInt32.v c))
  = UInt32.shift_left a s

(*** UInt64 operators ***)

unfold noextract
let u64_add (r:Prims.range) (x y:UInt64.t)
  : Pure UInt64.t
      (requires labeled r "Cannot verify u64 addition" (UInt.size (UInt64.v x + UInt64.v y) UInt64.n))
      (ensures fun z -> UInt64.v z == UInt64.v x + UInt64.v y)
  = UInt64.add x y

unfold noextract
let u64_sub (r:Prims.range) (x y:UInt64.t)
  : Pure UInt64.t
      (requires labeled r "Cannot verify u64 subtraction" (UInt.size (UInt64.v x - UInt64.v y) UInt64.n))
      (ensures fun z -> UInt64.v z == UInt64.v x - UInt64.v y)
  = UInt64.sub x y

unfold noextract
let u64_mul (r:Prims.range) (x y:UInt64.t)
  : Pure UInt64.t
      (requires labeled r "Cannot verify u64 multiplication" (UInt.size (UInt64.v x `Prims.op_Multiply` UInt64.v y) UInt64.n))
      (ensures fun z -> UInt64.v z == UInt64.v x `Prims.op_Multiply` UInt64.v y)
  = UInt64.mul x y

unfold noextract
let u64_div (r:Prims.range) (x y:UInt64.t)
  : Pure UInt64.t
      (requires labeled r "Cannot verify u64 division" (UInt64.v y =!= 0))
      (ensures fun z -> UInt64.v z == UInt64.v x / UInt64.v y)
  = UInt64.div x y

(** Euclidean remainder *)
unfold noextract
let u64_rem (r:Prims.range) (x y:UInt64.t)
  : Pure UInt64.t
      (requires labeled r "Cannot verify u64 remainder" (UInt64.v y =!= 0))
      (ensures (fun z -> FStar.UInt.mod (UInt64.v x) (UInt64.v y) == UInt64.v z))
  = UInt64.rem x y

(** Bitwise logical conjunction *)
unfold noextract
let u64_logand (r:Prims.range) (x:UInt64.t) (y:UInt64.t)
  : Pure UInt64.t
    (requires True)
    (ensures (fun z -> UInt64.v x `UInt.logand` UInt64.v y == UInt64.v z))
  = UInt64.logand x y

(** Bitwise logical exclusive-or *)
unfold noextract
let u64_logxor (r:Prims.range) (x:UInt64.t) (y:UInt64.t)
  : Pure UInt64.t
    (requires True)
    (ensures (fun z -> UInt64.v x `UInt.logxor` UInt64.v y == UInt64.v z))
  = UInt64.logxor x y

(** Bitwise logical disjunction *)
unfold noextract
let u64_logor (r:Prims.range) (x:UInt64.t) (y:UInt64.t)
  : Pure UInt64.t
    (requires True)
    (ensures (fun z -> UInt64.v x `UInt.logor` UInt64.v y == UInt64.v z))
  = UInt64.logor x y

(** Bitwise logical negation *)
unfold noextract
let u64_lognot (r:Prims.range) (x:UInt64.t)
  : Pure UInt64.t
    (requires True)
    (ensures (fun z -> UInt.lognot (UInt64.v x) == UInt64.v z))
  = UInt64.lognot x

(** Shift right with zero fill, shifting at most the integer width *)
unfold noextract
let u64_shift_right (r:Prims.range) (a:UInt64.t) (s:UInt32.t)
  : Pure UInt64.t
    (requires labeled r "Cannot verify u64 shift right" (UInt32.v s < UInt64.n))
    (ensures (fun c -> FStar.UInt.shift_right (UInt64.v a) (UInt32.v s) = UInt64.v c))
  = UInt64.shift_right a s

(** Shift left with zero fill, shifting at most the integer width *)
unfold noextract
let u64_shift_left (r:Prims.range) (a:UInt64.t) (s:UInt32.t)
  : Pure UInt64.t
    (requires labeled r "Cannot verify u64 shift left" (UInt32.v s < UInt64.n))
    (ensures (fun c -> FStar.UInt.shift_left (UInt64.v a) (UInt32.v s) = UInt64.v c))
  = UInt64.shift_left a s


(*** Casts ***)


(* Identity function for endianness-only casts *)

inline_for_extraction noextract
let id (#t: Type) (x: t) : Tot t = x

(** Widening casts **)

inline_for_extraction noextract
let uint8_to_uint16 (x:U8.t) : (y:U16.t{U16.v y == U8.v x}) =
  FStar.Int.Cast.uint8_to_uint16 x

inline_for_extraction noextract
let uint8_to_uint32 (x:U8.t) : (y:U32.t{U32.v y == U8.v x}) =
  FStar.Int.Cast.uint8_to_uint32 x

inline_for_extraction noextract
let uint8_to_uint64 (x:U8.t) : (y:U64.t{U64.v y == U8.v x}) =
  FStar.Int.Cast.uint8_to_uint64 x

inline_for_extraction noextract
let uint16_to_uint32 (x:U16.t) : (y:U32.t{U32.v y == U16.v x}) =
  FStar.Int.Cast.uint16_to_uint32 x

inline_for_extraction noextract
let uint16_to_uint64 (x:U16.t) : (y:U64.t{U64.v y == U16.v x}) =
  FStar.Int.Cast.uint16_to_uint64 x

inline_for_extraction noextract
let uint32_to_uint64 (x:U32.t) : (y:U64.t{U64.v y == U32.v x}) =
  FStar.Int.Cast.uint32_to_uint64 x

(** Narrowing casts, only when narrowing does not lose any precision **)

inline_for_extraction noextract
let uint16_to_uint8 (x:U16.t{FStar.UInt.fits (U16.v x) 8}) : (y:U8.t{U8.v y == U16.v x}) =
  FStar.Int.Cast.uint16_to_uint8 x

inline_for_extraction noextract
let uint32_to_uint16 (x:U32.t{FStar.UInt.fits (U32.v x) 16}) : (y:U16.t{U16.v y == U32.v x}) =
  FStar.Int.Cast.uint32_to_uint16 x

inline_for_extraction noextract
let uint32_to_uint8 (x:U32.t{FStar.UInt.fits (U32.v x) 8}) : (y:U8.t{U8.v y == U32.v x}) =
  FStar.Int.Cast.uint32_to_uint8 x

inline_for_extraction noextract
let uint64_to_uint32 (x:U64.t{FStar.UInt.fits (U64.v x) 32}) : (y:U32.t{U32.v y == U64.v x}) =
  FStar.Int.Cast.uint64_to_uint32 x

inline_for_extraction noextract
let uint64_to_uint16 (x:U64.t{FStar.UInt.fits (U64.v x) 16}) : (y:U16.t{U16.v y == U64.v x}) =
  FStar.Int.Cast.uint64_to_uint16 x

inline_for_extraction noextract
let uint64_to_uint8 (x:U64.t{FStar.UInt.fits (U64.v x) 8}) : (y:U8.t{U8.v y == U64.v x}) =
  FStar.Int.Cast.uint64_to_uint8 x

(*** Lemma for casts ***)

let cast_mul_fits_8_16 (x y :U8.t)
  : Lemma (
           FStar.UInt.fits
             ((U16.v (C.uint8_to_uint16 x))
               `op_Multiply`
              (U16.v (C.uint8_to_uint16 y)))
              16)
           [SMTPat ((U16.v (C.uint8_to_uint16 x))
                      `op_Multiply`
                   (U16.v (C.uint8_to_uint16 y)))]
  = let n = U16.v (C.uint8_to_uint16 x) in
    let m = U16.v (C.uint8_to_uint16 y) in
    FStar.Math.Lemmas.lemma_mult_lt_sqr n m (pow2 8)

let cast_mul_fits_16_32 (x y :U16.t)
  : Lemma (
           FStar.UInt.fits
             ((U32.v (C.uint16_to_uint32 x))
               `op_Multiply`
              (U32.v (C.uint16_to_uint32 y)))
              32)
           [SMTPat ((U32.v (C.uint16_to_uint32 x))
                      `op_Multiply`
                   (U32.v (C.uint16_to_uint32 y)))]
  = let n = U32.v (C.uint16_to_uint32 x) in
    let m = U32.v (C.uint16_to_uint32 y) in
    FStar.Math.Lemmas.lemma_mult_lt_sqr n m (pow2 16)

let cast_mul_fits_32_64 (x y :U32.t)
  : Lemma (
           FStar.UInt.fits
             ((U64.v (C.uint32_to_uint64 x))
               `op_Multiply`
              (U64.v (C.uint32_to_uint64 y)))
              64)
           [SMTPat ((U64.v (C.uint32_to_uint64 x))
                      `op_Multiply`
                      (U64.v (C.uint32_to_uint64 y)))]
  = let n = U64.v (C.uint32_to_uint64 x) in
    let m = U64.v (C.uint32_to_uint64 y) in
    FStar.Math.Lemmas.lemma_mult_lt_sqr n m (pow2 32)
