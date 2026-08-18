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
open CDDLTest.DPE.Common
open CDDL.Spec.Base
module DC = CDDLTest.DPE.DeriveContextInput
open  CDDLTest.DPE.DeriveContextInput

ghost
fn extract_to_be_signed x w
requires rel_signinputargs x w
ensures 
  rel_bytes x.to_be_signed w.to_be_signed **
  Trade.trade (rel_bytes x.to_be_signed w.to_be_signed)
              (rel_signinputargs x w)
{ 
  unfold_with_trade
    (`%rel_signinputargs) 
    (rel_signinputargs x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_signinputargs x w);
  fold_last_relation (`%tstr_any) tstr_any;  
  let rest_5 = fst_pair _ _ _ _ _;
  let tbs = snd_pair _ _ _ _ _;
  with xx yy. assert (rel_bytes xx yy);
  rewrite each xx as x.to_be_signed, yy as w.to_be_signed;
  ()
}

fn extract_to_be_signed_bytes x (w:erased _)
requires rel_signinputargs x w
returns tbs:Slice.slice UInt8.t
ensures exists* p s.
  pts_to tbs #p s **
  Trade.trade (pts_to tbs #p s)
              (rel_signinputargs x w) **
  pure (bytes_of_bytes s (Mkspect_signinputargs0?.to_be_signed w))
{
  extract_to_be_signed x w;
  let tbs = extract_bytes _ _;
  Trade.trade_compose _ _ (rel_signinputargs x w);
  tbs
}

let is_tbs_bytes (tbs_bytes:Seq.seq UInt8.t) (w:Seq.seq UInt8.t) =
  exists (wx:spect_signinputargs) (wr:Seq.seq UInt8.t).
          validate_and_parse_postcond_some bundle_signinputargs.b_spec.parser w wx wr /\
          wx.to_be_signed == spect_bytes_right (spect_bstr_right tbs_bytes)

let parse_failed (w:Seq.seq UInt8.t) =
  validate_and_parse_postcond_none bundle_signinputargs.b_typ w

fn parse_sign_input_args (s:Slice.slice UInt8.t) (#p:perm) (#w:erased _)
requires pts_to s #p w
returns tbs:option (Slice.slice UInt8.t)
ensures (
  match tbs with
  | None -> 
    pts_to s #p w **
    pure (parse_failed w)
  | Some tbs -> 
    exists* #q tbs_bytes.
      pts_to tbs #q tbs_bytes **
      Trade.trade (pts_to tbs #q tbs_bytes) (pts_to s #p w) **
      pure (is_tbs_bytes tbs_bytes w)
)
{
  let res = validate_and_parse_signinputargs s;
  match res {
    None -> {
      unfold validate_and_parse_post;
      None
    }
    Some xrem -> {
      let (x, rem) = xrem;
      unfold validate_and_parse_post;
      Trade.Util.elim_hyp_r _ _ _;
      let tbs = extract_to_be_signed_bytes _ _;
      Trade.trade_compose _ _ (pts_to s #p w);
      Some tbs
    }
  }
}
