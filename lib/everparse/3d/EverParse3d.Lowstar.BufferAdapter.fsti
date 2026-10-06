module EverParse3d.Lowstar.BufferAdapter
module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.LowstarBuffer
module P = EverParse3d.Prelude
open EverParse3d.State

inline_for_extraction noextract
val validator
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (p: P.parser k t)
  (d: state_dict) (has_action consumes use_error_handler: bool)
  : Type0

inline_for_extraction noextract
val adapt_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (#p: P.parser k t) (#d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_buffer p d has_action use_error_handler)
  : validator p d has_action true use_error_handler

inline_for_extraction noextract
val adapt_no_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (#p: P.parser k t) (#d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_no_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_buffer p d has_action use_error_handler)
  : validator p d has_action false use_error_handler

module IT = EverParse3d.Interpreter

[@@noextract_to "krml"; EverParse3d.Actions.Common.specialize_backend]
inline_for_extraction noextract
let validator_of
  (d: state_dict) (eh: bool)
  #ha #ar #nz #wk (#k: P.parser_kind nz wk)
  (t: IT.typ B.base_t B.len_t B.pos_t B.input_stream_buffer d eh k ha ar)
  = validator (IT.as_parser t) d ha (not ar) eh

inline_for_extraction noextract
let adapt
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk) (#t: Type)
  (#p: P.parser k t) (#d: state_dict) (#ha: bool) (#eh: bool)
  (ar: bool)
  (worker: A.validate_with_action_t #B.base_t #B.len_t #B.pos_t
    #B.input_stream_buffer p d ha ar eh)
  : validator p d ha (not ar) eh
  = if ar then adapt_no_read #nz #wk #k #t #p #d #ha #eh worker
    else adapt_read #nz #wk #k #t #p #d #ha #eh worker
