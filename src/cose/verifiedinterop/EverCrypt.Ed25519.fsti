module EverCrypt.Ed25519
open Pulse.Lib.Pervasives
module AP = Pulse.Lib.ArrayPtr
module U8 = FStar.UInt8
module U32 = FStar.UInt32

/// From Lib.IntTypes.size_t
inline_for_extraction noextract [@@noextract_to "krml"]
let size_t = U32.t

/// From Lib.IntTypes.max_size_t
noextract [@@noextract_to "krml"]
let max_size_t = pow2 32 - 1

/// From Spec.Ed25519.sign
noextract [@@noextract_to "krml"]
val spec_ed25519_sign: secret:Seq.lseq U8.t 32 -> msg:Seq.seq U8.t{Seq.length msg <= max_size_t} -> Seq.lseq U8.t 64

/// From EverCrypt.Ed25519.sign
val sign:
    signature:AP.ptr U8.t
  -> #p_private_key: perm
  -> #v_private_key: Ghost.erased (Seq.seq U8.t) { Seq.length v_private_key == 32 }
  -> private_key:AP.ptr U8.t
  -> msg_len:size_t
  -> #p_msg: perm
  -> #v_msg: Ghost.erased (Seq.seq U8.t) { Seq.length v_msg == U32.v msg_len }
  -> msg:AP.ptr U8.t ->
  stt (squash (Seq.length v_private_key == 32 /\ Seq.length v_msg == U32.v msg_len))
    (requires
      (exists* v_signature . pts_to signature v_signature ** pure (Seq.length v_signature == 64)) **
      pts_to private_key #p_private_key v_private_key **
      pts_to msg #p_msg v_msg
    )
    (ensures fun _ ->
      AP.pts_to signature (spec_ed25519_sign v_private_key v_msg) **
      pts_to private_key #p_private_key v_private_key **
      pts_to msg #p_msg v_msg
    )

/// From Spec.Ed25519
noextract [@@noextract_to "krml"]
val spec_ed25519_verify: public:Seq.lseq U8.t 32 -> msg:Seq.seq U8.t{Seq.length msg <= max_size_t} -> signature:Seq.lseq U8.t 64 -> bool

/// From EverCrypt.Ed25519.verify
val verify:
    #p_public_key: perm
  -> #v_public_key: Ghost.erased (Seq.seq U8.t) { Seq.length v_public_key == 32 }
  -> public_key:AP.ptr U8.t
  -> msg_len:size_t
  -> #p_msg: perm
  -> #v_msg: Ghost.erased (Seq.seq U8.t) { Seq.length v_msg == U32.v msg_len}
  -> msg:AP.ptr U8.t
  -> #p_signature: perm
  -> #v_signature: Ghost.erased (Seq.seq U8.t) { Seq.length v_signature == 64 }
  -> signature:AP.ptr U8.t ->
  stt bool
    (requires
      pts_to public_key #p_public_key v_public_key **
      pts_to msg #p_msg v_msg **
      pts_to signature #p_signature v_signature
    )
    (ensures fun b ->
      pure (b == spec_ed25519_verify v_public_key v_msg v_signature) **
      pts_to public_key #p_public_key v_public_key **
      pts_to msg #p_msg v_msg **
      pts_to signature #p_signature v_signature
    )
