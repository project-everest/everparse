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
module EverParse3d.Kinds
module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators

////////////////////////////////////////////////////////////////////////////////
// Parsers
////////////////////////////////////////////////////////////////////////////////

let parser_kind_prop
  (nz: bool)
  (wk: weak_kind)
  (k: LP.parser_kind)
: Tot prop
= (nz ==> (k.LP.parser_kind_low > 0)) /\
  begin match wk with
  | WeakKindStrongPrefix -> k.LP.parser_kind_subkind == Some LP.ParserStrong
  | WeakKindConsumesAll -> k.LP.parser_kind_subkind == Some LP.ParserConsumesAll
  | _ -> True
  end

inline_for_extraction
noextract
let parser_kind (nz:bool) (wk: weak_kind) =
  k:LP.parser_kind { parser_kind_prop nz wk k }

inline_for_extraction
noextract
let glb (#nz1:bool) (#wk1: weak_kind) (k1:parser_kind nz1 wk1)
        (#nz2:bool) (#wk2: weak_kind) (k2:parser_kind nz2 wk2)
    : parser_kind (nz1 && nz2) (weak_kind_glb wk1 wk2)
    = LP.glb k1 k2

/// Parser: return
inline_for_extraction
noextract
let ret_kind
  : parser_kind false WeakKindStrongPrefix
  = LPC.parse_ret_kind

/// Parser: bind
inline_for_extraction
noextract
let and_then_kind (#nz1:_) (k1:parser_kind nz1 WeakKindStrongPrefix)
                  (#nz2:_) (#wk2: _) (k2:parser_kind nz2 wk2)
    : parser_kind (nz1 || nz2) wk2
    = LPC.and_then_kind k1 k2

inline_for_extraction
noextract
let filter_kind (#nz:_) (#wk: _) (k:parser_kind nz wk)
  : parser_kind nz wk
  = LPC.parse_filter_kind k

inline_for_extraction
noextract
let impos_kind
  : parser_kind true WeakKindStrongPrefix
  = LPC.(strong_parser_kind 1 1 (Some ParserKindMetadataFail))

/// Lists/arrays
inline_for_extraction
noextract
let kind_nlist
  : parser_kind false WeakKindStrongPrefix
  = let open LP in
    {
      parser_kind_low = 0;
      parser_kind_high = None;
      parser_kind_subkind = Some ParserStrong;
      parser_kind_metadata = None
    }

let kind_all_bytes
  : parser_kind false WeakKindConsumesAll
  = LowParse.Spec.Bytes.parse_all_bytes_kind

let kind_t_at_most
  : parser_kind false WeakKindStrongPrefix
  = kind_nlist

let kind_t_exact
  : parser_kind false WeakKindStrongPrefix
  = kind_nlist

let parse_string_kind
  : parser_kind true WeakKindStrongPrefix
  = {
     LP.parser_kind_low = 1;
     LP.parser_kind_high = None;
     LP.parser_kind_subkind = Some LP.ParserStrong;
     LP.parser_kind_metadata = None;
    }

let kind_all_zeros
  : parser_kind false WeakKindConsumesAll
  = LowParse.Spec.List.parse_list_kind

inline_for_extraction noextract
let kind____UINT8
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.Int.parse_u8_kind

inline_for_extraction noextract
let kind____UINT16BE
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.BoundedInt.parse_u16_kind

inline_for_extraction noextract
let kind____UINT32BE
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.BoundedInt.parse_u32_kind

inline_for_extraction noextract
let kind____UINT64BE
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.Int.parse_u64_kind

inline_for_extraction noextract
let kind____UINT16
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.BoundedInt.parse_u16_kind

inline_for_extraction noextract
let kind____UINT32
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.BoundedInt.parse_u32_kind

inline_for_extraction noextract
let kind____UINT64
  : parser_kind true WeakKindStrongPrefix
  = LowParse.Spec.Int.parse_u64_kind
