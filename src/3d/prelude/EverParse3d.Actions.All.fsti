module EverParse3d.Actions.All
include EverParse3d.Actions.Base
module P = EverParse3d.Prelude

inline_for_extraction
noextract
val ___PUINT8: Type0

noextract
inline_for_extraction
val action_field_ptr
      (#nz:_)
      (#wk: _)
      (#k:P.parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:P.parser k t)
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagBuffer))
   : action p true_inv eloc_none true ___PUINT8

noextract
inline_for_extraction
val action_field_pos_32
      (#nz:_)
      (#wk: _)
      (#k:P.parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:P.parser k t)
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagBuffer))
   : action p true_inv eloc_none false FStar.UInt32.t
