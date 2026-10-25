module LargeExtern
module B = EverParse3d.InputStream.LowstarExtern
module AD = EverParse3d.Lowstar.ExternAdapter
module P = EverParse3d.Prelude
open EverParse3d.State

noextract val kind : P.parser_kind true P.WeakKindStrongPrefix
noextract val parser : P.parser kind P.all_bytes

val no_read (extra: B.extra_t)
  : AD.validator parser state_dict_empty false false false

val skip (extra: B.extra_t)
  : AD.validator parser state_dict_empty false true false

val drain (extra: B.extra_t)
  : AD.validator P.parse_all_bytes state_dict_empty false true false
