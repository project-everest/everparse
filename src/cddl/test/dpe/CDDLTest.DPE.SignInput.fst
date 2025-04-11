module CDDLTest.DPE.SignInput
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

fn parse_option_bytes x (w:erased _) res
requires
  rel_option
    rel_evercddl_bytes x w **
  Trade.trade (rel_option rel_evercddl_bytes x w) res
returns x:option (slice UInt8.t)
ensures is_slice_opt x res
{
  rel_option_cases _ _ _;

  match x {
    None -> {
      Trade.elim_trade _ _;
      fold (is_slice_opt None res);
      None
    }

    Some _ -> {
      let sl = destruct_rel_option _ _ _;
      Trade.trade_compose _ _ res;
      let sl = extract_bytes _ _;
      Trade.trade_compose _ _ res;
      fold (is_slice_opt (Some sl) res);
      Some sl
    }
  }
}

fn parse_sign_input x (w:erased _) res
requires
  rel_evercddl_signinputargs x w **
  Trade.trade (rel_evercddl_signinputargs x w) res
returns x:option (slice UInt8.t)
ensures is_slice_opt x res
{
  unfold_with_trade (`%rel_evercddl_signinputargs) (rel_evercddl_signinputargs x w);
  Trade.trade_compose _ _ res;
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ res;

  let rest_5 = fst_pair_concrete _ _ _ _ _;
  let tbs = snd_pair_concrete _ _ _ _ _;

  rewrite each (Tactics.PrettifyType.named "intkey5" evercddl_bytes_pretty)
      as evercddl_bytes_pretty;
  parse_option_bytes _ _ res;
}

fn parse_sign_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns x:option (slice UInt8.t)
ensures is_slice_opt x (pts_to s #p w)
{
  let res = validate_and_parse_signinputargs s;
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
      parse_sign_input _ _ _;
    }
  }
}