module LowParse.PulseParse.SizeLeaf

(* Adapter turning a pure, total [LowParse.SLow.Base.size32] serialized-size
   function into the exact [FStar.SizeT.t] size function required by the
   variable-length leaf writer/size combinators
   ([LowParse.PulseParse.Base.l2r_safe_writer_leaf_vl] /
   [l2r_safe_size_leaf_vl]). This lets a leaf-readable (by-value) type whose
   copyful representation is the value itself (vmatch = [eq_as_slprop], conv =
   [leaf_conv]) obtain a graceful safe writer/size even when it is
   variable-size, reusing the already-generated [<n>_writer] and [<n>_size32]. *)

open LowParse.Spec.Base
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module LSZ = LowParse.SLow.Base

(* The parser kind bounds the serialized length below [u32_max], so [size32]
   never saturates and its result is the exact serialized length. *)
inline_for_extraction
let leaf_size_of_size32
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sz32: LSZ.size32 s)
  (sq: squash (Some? k.parser_kind_high /\ Some?.v k.parser_kind_high < pow2 16))
  (x: t)
: Pure SZ.t
    (requires True)
    (ensures (fun sz -> SZ.v sz == Seq.length (serialize s x) /\ SZ.v sz < pow2 64))
= serialize_length s x;
  // serialized length <= parser_kind_high < pow2 16, so fits via fits_at_least_16
  SZ.uint32_to_sizet (sz32 x)
