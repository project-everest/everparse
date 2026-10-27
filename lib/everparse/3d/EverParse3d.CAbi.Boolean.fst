module EverParse3d.CAbi.Boolean

module U8 = FStar.UInt8

[@@FStar.Attributes.custard_no_unfold;
   FStar.Attributes.rename_let "BOOLEAN"]
type t = U8.t

inline_for_extraction
let of_bool (b: bool) : t = if b then 1uy else 0uy

inline_for_extraction
let to_bool (b: t) : bool = b <> 0uy

noextract
let round_trip (b: bool)
  : Lemma (to_bool (of_bool b) == b)
  = ()

noextract
let canonicalize (b: t)
  : Lemma (of_bool (to_bool b) == (if b = 0uy then 0uy else 1uy))
  = ()
