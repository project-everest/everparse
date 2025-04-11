module CDDLTest.DPE.Common
module EqTest = CDDL.Spec.EqTest
open CDDLTest.Test
open Pulse.Lib
open Pulse.Lib.Pervasives
open CDDLTest.Destructors
#lang-pulse
open CDDL.Pulse.Parse.Base
open CDDL.Pulse.Types
open CDDL.Pulse.AST.Bundle
open CBOR.Spec.API.Type
open CDDL.Spec.Base

let tstr_any = 
  rel_either_left (rel_slice_of_table (mk_eq_test_bij spect_aux_env16_type_1_pretty_right
                    spect_aux_env16_type_1_pretty_left
                    spect_aux_env16_type_1_pretty_left_right
                    spect_aux_env16_type_1_pretty_right_left
                    (mk_eq_test_bij spect_evercddl_uint_pretty_right
                        spect_evercddl_uint_pretty_left
                        spect_evercddl_uint_pretty_left_right
                        spect_evercddl_uint_pretty_right_left
                        (EqTest.eqtype_eq UInt64.t)))
                rel_aux_env16_type_1
                rel_aux_env16_type_3)
            (rel_map_iterator CBOR.Pulse.API.Det.C.cbor_det_match
                CBOR.Pulse.API.Det.C.cbor_det_map_iterator_match
                aux_env16_type_1_pretty
                aux_env16_type_3_pretty
                (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env16_type_1)
                (CDDL.Pulse.Iterator.Base.mk_spec rel_aux_env16_type_3))

fn extract_bytes x (y:erased _)
requires rel_evercddl_bytes x y
returns xx:slice UInt8.t
ensures 
  exists* yy. 
    rel_slice_of_seq false xx yy **
    Trade.trade 
      (rel_slice_of_seq false xx yy)
      (rel_evercddl_bytes x y)
{
  unfold (rel_evercddl_bytes x y);
  destruct_rel_fun _ _ _ _ _;
  with xx yy. unfold (rel_evercddl_bstr xx yy);
  destruct_rel_fun _ _ _ _ _;
  with (res:slice UInt8.t) (resy:_). assert (rel_slice_of_seq false res resy);
  Trade.trade_compose _ _ (rel_fun rel_evercddl_bstr
          evercddl_bytes_pretty_left
          spect_evercddl_bytes_pretty_left
          x
          y);
  res
}

fn destruct_evercddl_bytes_head 
    (x:evercddl_bytes_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_bytes x w **
  Trade.trade ((rel_evercddl_bytes x w ** rest) ** done) res
returns xx:slice UInt8.t
ensures
  exists* ws. 
  rel_slice_of_seq false xx ws **
  Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res
{
  Trade.Util.assoc_hyp_r _ _ _ _;
  let xx = extract_bytes x w;
  Trade.Util.trans_hyp_l _ _ _ res;
  slprop_equivs();
  with ws. assert (rel_slice_of_seq false xx ws);
  with p. rewrite Trade.trade p res as Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res;
  xx
}

fn destruct_evercddl_nint_head 
    (x:evercddl_nint_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_nint x w **
  Trade.trade ((rel_evercddl_nint x w ** rest) ** done) res
returns xx:UInt64.t
ensures
  pure (xx == evercddl_nint_pretty_left x /\ xx == spect_evercddl_nint_pretty_left w) **
  Trade.trade (rest ** done) res
{
  rewrite each (rel_evercddl_nint x w) as pure (evercddl_nint_pretty_left x == spect_evercddl_nint_pretty_left w);
  Trade.Util.assoc_hyp_r _ _ _ _;
  Trade.Util.elim_hyp_l (pure _) _ _;
  evercddl_nint_pretty_left x
}

fn destruct_evercddl_tstr_head 
    (x:evercddl_tstr_pretty)
    (w:erased _)
    (rest done res:slprop)
requires
  rel_evercddl_tstr x w **
  Trade.trade ((rel_evercddl_tstr x w ** rest) ** done) res
returns xx:slice UInt8.t
ensures exists* ws. 
  rel_slice_of_seq false xx ws **
  Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res
{
  unfold_with_trade (`%rel_evercddl_tstr) (rel_evercddl_tstr x w);
  destruct_rel_fun _ _ _ _ _;
  Trade.trade_compose _ _ (rel_evercddl_tstr x w);
  Trade.Util.assoc_hyp_r _ _ _ _;
  Trade.Util.trans_hyp_l _ _ _ res;
  slprop_equivs();
  with (xx:slice UInt8.t) ws. assert (rel_slice_of_seq false xx ws);
  with p. rewrite Trade.trade p res as Trade.trade (rest ** (done ** rel_slice_of_seq false xx ws)) res;
  xx
}

let is_slice_opt 
    (sl:option (slice UInt8.t))
    (dflt:slprop)
: slprop
= match sl with
  | None -> dflt
  | Some sl -> 
    exists* b. //relate uds to w?
      rel_slice_of_seq false sl b **
      Trade.trade
        (rel_slice_of_seq false sl b)
        dflt
