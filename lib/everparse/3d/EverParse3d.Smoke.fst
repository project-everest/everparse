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

(* The same, at the `extern` backend. The instance has to be given explicitly,
   since `extern` and `static` share the same base type. *)
module E = EverParse3d.InputStream.Extern

inline_for_extraction noextract
let smoke_extern
: A.validate_with_action_t
    #E.base_t #E.len_t #E.pos_t #E.input_stream_extern
    (parse____UINT8 `parse_pair` parse____UINT16)
    state_dict_empty
    false
    false
= A.validate_pair #_ #_ #_ #E.input_stream_extern "smoke" "fst" true
    (A.validate_without_reading A.validate____UINT8) true
    (A.validate_without_reading A.validate____UINT16)

(* And at the `static` backend. *)
module St = EverParse3d.InputStream.Static

inline_for_extraction noextract
let smoke_static
: A.validate_with_action_t
    #St.base_t #St.len_t #St.pos_t #St.input_stream_static
    parse____UINT32
    state_dict_empty
    false
    false
= A.validate_without_reading #_ #_ #_ #St.input_stream_static A.validate____UINT32
