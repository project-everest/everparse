module EverParse3d.Smoke
#lang-pulse
(* A smoke test: check that the combinators exported by
   EverParse3d.Actions.Base can actually be applied by a client module, at the
   `buffer` backend instance. *)
open Pulse.Lib.Pervasives
open EverParse3d.Prelude
open EverParse3d.State
module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.Buffer

inline_for_extraction noextract
let smoke_v
: A.validate_with_action_t
    #B.base_t #B.len_t #B.pos_t
    (parse____UINT8 `parse_pair` parse____UINT16)
    state_dict_empty
    false
    false
= A.validate_pair "smoke" "fst" true (A.validate_without_reading A.validate____UINT8) true (A.validate_without_reading A.validate____UINT16)

inline_for_extraction noextract
let smoke_r
: A.leaf_reader #B.base_t #B.len_t #B.pos_t parse____UINT32
= A.read____UINT32
