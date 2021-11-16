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

noextract
type weak_kind =
| WeakKindWeak
| WeakKindStrongPrefix
| WeakKindConsumesAll


inline_for_extraction
noextract
let weak_kind_glb
  (k1 k2: weak_kind)
: Tot weak_kind
= if k1 = k2
  then k1
  else WeakKindWeak

inline_for_extraction
noextract
val parser_kind (nz:bool) (wk: weak_kind) : Type0

inline_for_extraction
noextract
val glb (#nz1:bool) (#wk1: weak_kind) (k1:parser_kind nz1 wk1)
        (#nz2:bool) (#wk2: weak_kind) (k2:parser_kind nz2 wk2)
    : parser_kind (nz1 && nz2) (weak_kind_glb wk1 wk2)

/// Parser: return
inline_for_extraction
noextract
val ret_kind
  : parser_kind false WeakKindStrongPrefix

/// Parser: bind
inline_for_extraction
noextract
val and_then_kind (#nz1:_) (k1:parser_kind nz1 WeakKindStrongPrefix)
                  (#nz2:_) (#wk2: _) (k2:parser_kind nz2 wk2)
    : parser_kind (nz1 || nz2) wk2


inline_for_extraction
noextract
val filter_kind (#nz:_) (#wk: _) (k:parser_kind nz wk)
  : parser_kind nz wk

inline_for_extraction
noextract
val impos_kind
  : parser_kind true WeakKindStrongPrefix

/// Lists/arrays
inline_for_extraction
noextract
val kind_nlist
  : parser_kind false WeakKindStrongPrefix

val kind_all_bytes
  : parser_kind false WeakKindConsumesAll

val kind_t_at_most
  : parser_kind false WeakKindStrongPrefix

val kind_t_exact
  : parser_kind false WeakKindStrongPrefix

val parse_string_kind
  : parser_kind true WeakKindStrongPrefix

val kind_all_zeros
  : parser_kind false WeakKindConsumesAll

inline_for_extraction noextract
val kind____UINT8
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
val kind____UINT16BE
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
val kind____UINT32BE
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
val kind____UINT64BE
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
val kind____UINT16
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
val kind____UINT32
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
val kind____UINT64
  : parser_kind true WeakKindStrongPrefix

inline_for_extraction noextract
let kind_unit
  : parser_kind false WeakKindStrongPrefix
= ret_kind

