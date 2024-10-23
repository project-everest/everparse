module EverParse3d.Actions.All
include EverParse3d.Actions.Base
module P = EverParse3d.Prelude

inline_for_extraction
noextract
val ___PUINT8: Type0 // these are never NULL

noextract
inline_for_extraction
val action_field_ptr
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagBuffer))
   : action true_inv disjointness_trivial eloc_none true false ___PUINT8

noextract
inline_for_extraction
val action_field_ptr_after
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagExtern))
      (sz: FStar.UInt64.t)
      (write_to: bpointer ___PUINT8)
   : action (ptr_inv write_to) disjointness_trivial (ptr_loc write_to) false false bool // if action returns true, writes some value to write_to. if false, do nothing

noextract
inline_for_extraction
val action_field_ptr_after_with_setter
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagExtern))
      (sz: FStar.UInt64.t)
      (#output_loc: eloc)
      (write_to: (___PUINT8 -> Tot (external_action unit output_loc)))
   : action true_inv disjointness_trivial output_loc false false bool // if action returns true, writes some value to write_to. if false, do nothing

noextract
inline_for_extraction
val action_field_pos_32
      (u:squash (EverParse3d.Actions.BackendFlag.backend_flag == BackendFlagBuffer))
   : action true_inv disjointness_trivial eloc_none false false FStar.UInt32.t
