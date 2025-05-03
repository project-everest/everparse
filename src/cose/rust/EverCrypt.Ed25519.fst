module EverCrypt.Ed25519
open Pulse
#lang-pulse

let spec_ed25519_sign secret msg = Seq.create 64 0uy

fn sign
    (signature:S.slice U8.t)
    (#p_private_key: perm)
    (#v_private_key: Ghost.erased (Seq.seq U8.t) { Seq.length v_private_key == 32 })
    (private_key:S.slice U8.t)
    (#p_msg: perm)
    (#v_msg: Ghost.erased (Seq.seq U8.t) { Seq.length v_msg <= max_size_t })
    (msg:S.slice U8.t)
  requires
    (exists* v_signature . pts_to signature v_signature ** pure (Seq.length v_signature == 64)) **
    pts_to private_key #p_private_key v_private_key **
    pts_to msg #p_msg v_msg
  returns _: squash (Seq.length v_private_key == 32)
  ensures
    S.pts_to signature (spec_ed25519_sign v_private_key v_msg) **
    pts_to private_key #p_private_key v_private_key **
    pts_to msg #p_msg v_msg
{
  S.(signature.(0sz) <- 0uy);
  admit ()
}

let spec_ed25519_verify public msg sig = true

fn verify
    (#p_public_key: perm)
    (#v_public_key: Ghost.erased (Seq.seq U8.t) { Seq.length v_public_key == 32 })
    (public_key:S.slice U8.t)
    (#p_msg: perm)
    (#v_msg: Ghost.erased (Seq.seq U8.t) { Seq.length v_msg <= max_size_t })
    (msg:S.slice U8.t)
    (#p_signature: perm)
    (#v_signature: Ghost.erased (Seq.seq U8.t) { Seq.length v_signature == 64 })
    (signature:S.slice U8.t)
{
  admit ()
}
