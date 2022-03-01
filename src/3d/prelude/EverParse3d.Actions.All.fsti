module EverParse3d.Actions.All
include EverParse3d.Actions.Base
module P = EverParse3d.Prelude

inline_for_extraction
noextract
val ___PUINT8: Type0 // these are never NULL

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
val action_field_ptr_after
      (#nz:_)
      (#wk: _)
      (#k:P.parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:P.parser k t)
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagExtern))
      (sz: FStar.UInt64.t)
      (write_to: bpointer ___PUINT8)
   : action p (ptr_inv write_to) (ptr_loc write_to) false bool // if action returns true, writes some value to write_to. if false, do nothing

noextract
inline_for_extraction
val action_field_ptr_after_with_setter
      (#nz:_)
      (#wk: _)
      (#k:P.parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:P.parser k t)
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagExtern))
      (sz: FStar.UInt64.t)
      (#output_loc: eloc)
      (write_to: (___PUINT8 -> Tot (external_action output_loc)))
   : action p true_inv output_loc false bool // if action returns true, writes some value to write_to. if false, do nothing

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
