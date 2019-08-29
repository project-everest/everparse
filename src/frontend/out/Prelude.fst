module Prelude
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators
module LPL = LowParse.Low.Base
module LPLC = LowParse.Low.Combinators
////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////

let parser_kind = k:LP.parser_kind{LP.(k.parser_kind_subkind == Some ParserStrong)}
let parser (k:parser_kind) (t:Type) = LP.parser k t
let glb (k1 k2:parser_kind) : parser_kind = LP.glb k1 k2

/// Parser: return
let ret_kind = LPC.parse_ret_kind
inline_for_extraction noextract
let parse_ret #t (v:t)
  : Tot (parser ret_kind t)
  = LPC.parse_ret #t v

/// Parser: bind
let and_then_kind k1 k2 = LPC.and_then_kind k1 k2
inline_for_extraction noextract
let parse_dep_pair #k1 (#t1: Type0) (p1: parser k1 t1)
                   #k2 (#t2: (t1 -> Tot Type0)) (p2: (x: t1) -> parser k2 (t2 x))
  : Tot (parser (and_then_kind k1 k2) (dtuple2 t1 t2) )
  = LPC.parse_dtuple2 p1 p2

/// Parser: sequencing
inline_for_extraction noextract
let parse_pair #k1 #t1 (p1:parser k1 t1)
               #k2 #t2 (p2:parser k2 t2)
  : Tot (parser (and_then_kind k1 k2) (t1 * t2))
  = LPC.nondep_then p1 p2

/// Parser: map
let injective_map a b = f:(a -> Tot b){LPC.synth_injective f}
inline_for_extraction noextract
let parse_map #k #t1 #t2 (p:parser k t1)
              (f:injective_map t1 t2)
  : Tot (parser k t2)
  = LPC.parse_synth p f

/// Parser: filter
let refine t (f:t -> bool) = x:t{f x}
let filter_kind k = LPC.parse_filter_kind k
inline_for_extraction noextract
let parse_filter #k #t (p:parser k t) (f:(t -> bool))
  : Tot (parser (LPC.parse_filter_kind k) (refine t f))
  = LPC.parse_filter #k #t p f

/// Parser: weakening kinds
inline_for_extraction noextract
let parse_weaken #k #t (p:parser k t) (k':parser_kind{k' `LP.is_weaker_than` k})
  : Tot (parser k' t)
  = LP.weaken k' p

/// Parser: unreachable, for default cases of exhaustive pattern matching
inline_for_extraction noextract
let parse_impos (_:squash False)
  : Tot (parser ret_kind False)
  = false_elim()

////////////////////////////////////////////////////////////////////////////////
// Readers
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let reader #k #t (p:parser k t) = LPLC.leaf_reader p

inline_for_extraction noextract
let read_filter (#k: parser_kind)
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
let validator (#k:parser_kind) (#t:Type) (p:parser k t)
  : Type
  = LPL.validator #k #t p

inline_for_extraction noextract
let validate_ret
  : validator (parse_ret ())
  = LPLC.validate_ret ()

inline_for_extraction noextract
let validate_pair #k1 #t1 (#p1:parser k1 t1) (v1:validator p1)
                  #k2 #t2 (#p2:parser k2 t2) (v2:validator p2)
  : validator (p1 `parse_pair` p2)
  = LPLC.validate_nondep_then v1 v2

inline_for_extraction noextract
let validate_dep_pair #k1 #t1 (#p1:parser k1 t1) (v1:validator p1) (r1: LPL.leaf_reader p1)
                      #k2 (#t2:t1 -> Type) (#p2:(x:t1 -> parser k2 (t2 x))) (v2:(x:t1 -> validator (p2 x)))
  : Tot (validator (p1 `parse_dep_pair` p2))
  = LPLC.validate_dtuple2 v1 r1 v2

inline_for_extraction noextract
let validate_map #k #t1 (#p:parser k t1) (v:validator p)
                    #t2 (f:injective_map t1 t2)
  : Tot (validator (p `parse_map` f))
  = LPLC.validate_synth v f ()

inline_for_extraction noextract
let validate_filter (#k:_) (#t:_) (#p:parser k t) (v:validator p) (r:LPL.leaf_reader p) (f:(t -> bool))
  : Tot (validator (p `parse_filter` f))
  = LPLC.validate_filter v r f (fun x -> f x)

inline_for_extraction noextract
let validate_weaken #k #t (#p:parser k t) (v:validator p) (k':parser_kind{k' `LP.is_weaker_than` k})
  : Tot (validator (p `parse_weaken` k'))
  = LPLC.validate_weaken k' v ()

inline_for_extraction noextract
let validate_impos (_:squash False)
  : Tot (validator (parse_impos ()))
  = fun #_ #_ _ _ -> 0ul

////////////////////////////////////////////////////////////////////////////////
// Base types
////////////////////////////////////////////////////////////////////////////////

/// UInt32
module U32 = FStar.UInt32
let _UINT32 = U32.t
let kind__UINT32 = LowParse.Spec.BoundedInt.parse_u32_kind
let parse__UINT32 : parser kind__UINT32 _UINT32 = LowParse.Spec.BoundedInt.parse_u32_le
inline_for_extraction noextract
let validate__UINT32 : validator parse__UINT32 = LowParse.Low.BoundedInt.validate_u32_le ()
inline_for_extraction noextract
let read__UINT32 : LPL.leaf_reader parse__UINT32 = LowParse.Low.BoundedInt.read_u32_le

/// Lists/arrays
let nlist (n:U32.t) (t:Type) = LowParse.Spec.VCList.nlist (U32.v n) t
let kind_nlist : parser_kind =
  let open LP in
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_subkind = Some ParserStrong;
    parser_kind_metadata = None
  }
inline_for_extraction noextract
let parse_nlist (n:U32.t) #k #t (p:parser k t)
  : Tot (parser kind_nlist (nlist n t))
  = parse_weaken (LowParse.Spec.VCList.parse_nlist (U32.v n) p) kind_nlist
inline_for_extraction noextract
let validate_nlist (n:U32.t) #k #t (#p:parser k t) (v:validator p)
  : Tot (validator (parse_nlist n p))
  = validate_weaken (LowParse.Low.VCList.validate_nlist n v) kind_nlist

////////////////////////////////////////////////////////////////////////////////
//placeholders
////////////////////////////////////////////////////////////////////////////////
let suffix = FStar.UInt8.t
let kind_suffix : parser_kind = LowParse.Spec.Int.parse_u8_kind
let parse_suffix : parser kind_suffix suffix = LowParse.Spec.Int.parse_u8
inline_for_extraction noextract
let validate_suffix : validator parse_suffix = LowParse.Low.Int.validate_u8 ()

////////////////////////////////////////////////////////////////////////////////
let parse_ite (#k:parser_kind) (#a:Type) (#b:Type) (e:bool)
              (p1:squash e -> parser k a)
              (p2:squash (not e) -> parser k b)
  : Tot (parser k (if e then a else b))
  = if e then p1 () else p2 ()

noextract inline_for_extraction
let validate_ite (#k:parser_kind) (#a:Type) (#b:Type) (e:bool)
                 (p1:squash e -> parser k a) (v1:(squash e -> validator (p1())))
                 (p2:squash (not e) -> parser k b) (v2:(squash (not e) -> validator (p2())))
  : Tot (validator (parse_ite e p1 p2))
  = fun #rrel #rel sl pos ->
      if e then v1 () sl pos else v2 () sl pos
