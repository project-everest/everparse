module CDDLTest.DPE.CertifyKeyInput
module EqTest = CDDL.Spec.EqTest
open CDDLTest.Test
open Pulse.Lib
open Pulse.Lib.Pervasives
open CDDLTest.Destructors
#lang-pulse
open CDDL.Pulse.Parse.Base
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8
open CDDL.Pulse.Types
module T = CDDL.Pulse.AST.Tactics
open CDDL.Pulse.AST.Bundle
open CBOR.Spec.API.Type
open CDDL.Spec.Base
open CDDLTest.DPE.Common

fn parse_certify_key_input x (w:erased _) res
requires
  rel_certifykeyinputargs x w **
  Trade.trade (rel_certifykeyinputargs x w) res
returns x:option (Slice.slice UInt8.t)
ensures is_slice_opt x res
{
  unfold_with_trade (`%rel_certifykeyinputargs) (rel_certifykeyinputargs x w);
  Trade.trade_compose _ _ res;
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ res;

  let rest_6 = fst_pair_concrete _ _ _ _ _;
  let rest_5 = fst_pair_concrete _ _ _ _ _;
  let rest_4 = fst_pair_concrete _ _ _ _ _;
  let rest_3 = fst_pair_concrete _ _ _ _ _;
  let pk = snd_pair_concrete _ _ _ _ _;

  rel_option_cases _ _ _;

  match pk {
    None -> {
      Trade.elim_trade _ _;
      fold (is_slice_opt None res);
      None
    }

    Some _ -> {
      let sl = destruct_rel_option _ _ _;
      Trade.trade_compose _ _ res;
      rewrite each (Tactics.PrettifyType.named "public_key"
            spect_bytes)
        as spect_bytes;
      let sl = extract_bytes _ _;
      Trade.trade_compose _ _ res;
      fold (is_slice_opt (Some sl) res);
      Some sl
    }
  }
}

fn parse_certify_key_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns x:option (Slice.slice UInt8.t)
ensures is_slice_opt x (pts_to s #p w)
{
  let res = validate_and_parse_certifykeyinputargs s;
  match res {
    None -> {
      unfold validate_and_parse_post;
      fold (is_slice_opt None (pts_to s #p w));
      None
    }
    Some xrem -> {
      let (x, rem) = xrem;
      elim_validate_and_parse_post_some x rem;
      Trade.Util.elim_hyp_r _ _ _;
      parse_certify_key_input _ _ _;
    }
  }
}

fn write_certify_key_output
    (out:Slice.slice UInt8.t)
    (pubkey:Slice.slice UInt8.t)
    (cert:Slice.slice UInt8.t)
    (#pk #c:erased _) (#p #q:perm)
requires
  exists* w.
    pts_to pubkey #p pk **
    pts_to pubkey #q c **
    pts_to out w
ensures
  exists* w.
    pts_to pubkey #p pk **
    pts_to pubkey #q c **
    pts_to out w
{
  ()
}
