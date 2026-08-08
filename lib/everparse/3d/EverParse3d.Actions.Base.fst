module EverParse3d.Actions.Base
#lang-pulse
friend EverParse3d.Kinds
friend EverParse3d.Prelude
open EverParse3d.ErrorCode
open EverParse3d.Prelude
open Pulse.Lib.Pervasives
module I = EverParse3d.InputStream.Base
module CP = EverParse3d.CopyBuffer

module PA = EverParse3d.ProbeActions
module AppCtxt = EverParse3d.AppCtxt

open FStar.FunctionalExtensionality
open EverParse3d.Actions.Common
module U8 = FStar.UInt8
module P = EverParse3d.Prelude
module SZ = FStar.SizeT

open EverParse3d.State

let action
  (extra_state: state_dict)
  (a: Type0)
  (use_error_handler: bool)
=
  ctxt: app_ctxt ->
  error_handler_fn : (if use_error_handler then error_handler else unit) ->
  sl: input_buffer_t ->
  contents_sl: Ghost.erased (Seq.seq U8.t) ->
  v_sl: Ghost.erased (Seq.seq U8.t) ->
  stt a
    (exists* v_ctxt extra .
      pts_to ctxt v_ctxt **
      I.pts_to sl contents_sl v_sl **
      forevery_state extra_state extra
    )
    (fun _ -> exists* v_ctxt' extra' .
      pts_to ctxt v_ctxt' **
      I.pts_to sl contents_sl v_sl **
      forevery_state extra_state extra'
    )

module LP = LowParse.Spec.Base

inline_for_extraction noextract
let validate_with_action_t
     (#nz:bool)
     (#wk: _)
     (#k:parser_kind nz wk)
     (#t:Type0)
     (p:parser k t)
     (extra_state: state_dict)
     (has_action:bool)
     (use_error_handler:bool)
: Type 
= (ctxt: app_ctxt) ->
  (error_handler_fn : (if use_error_handler then error_handler else unit)) ->
  (sl: input_buffer_t) ->
  (extra: forevery_values extra_state) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt U8.t
  (requires exists* v_ctxt .
    pts_to ctxt v_ctxt **
    I.pts_to sl contents_sl v_sl **
    forevery_state extra_state extra
  )
  (ensures fun res -> exists* v_ctxt' v_sl' extra' .
    pts_to ctxt v_ctxt' **
    I.pts_to sl contents_sl v_sl' **
    forevery_state extra_state extra' **
    pure (
      (res == validator_error_action_failed ==> has_action) /\
      (not has_action ==> extra' == extra) /\
      (U8.v res > U8.v validator_error_action_failed ==> None? (LP.parse p v_sl)) /\
      I.seq_is_suffix_of v_sl' v_sl /\
      (res == validator_success ==> (Some? (LP.parse p v_sl) /\ v_sl' == Seq.slice v_sl (snd (Some?.v (LP.parse p v_sl))) (Seq.length v_sl)))
  ))

inline_for_extraction noextract
let validate_with_action_no_read
     (#nz:bool)
     (#wk: _)
     (#k:parser_kind nz wk)
     (#t:Type)
     (p:parser k t)
     (extra_state: state_dict)
     (has_action:bool)
     (use_error_handler:bool)
: Type 
= (ctxt: app_ctxt) ->
  (error_handler_fn : (if use_error_handler then error_handler else unit)) ->
  (sl: input_buffer_t) ->
  (pos: ref SZ.t) ->
  (extra: forevery_values extra_state) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_pos: Ghost.erased SZ.t) ->
  stt U8.t
  (requires exists* v_ctxt .
    pts_to ctxt v_ctxt **
    I.pts_to sl contents_sl v_sl ** // necessary for actions and the error handler
    pts_to pos v_pos **
    forevery_state extra_state extra **
    pure (SZ.v v_pos <= Seq.length v_sl)
  )
  (ensures fun res -> exists* v_ctxt' extra' v_pos' .
    pts_to ctxt v_ctxt' **
    I.pts_to sl contents_sl v_sl **
    pts_to pos v_pos' **
    forevery_state extra_state extra' **
    pure (
      SZ.v v_pos <= Seq.length v_sl /\ (
      let pp = LP.parse p (Seq.slice v_sl (SZ.v v_pos) (Seq.length v_sl)) in
      (res == validator_error_action_failed ==> has_action) /\
      (not has_action ==> extra' == extra) /\
      (U8.v res > U8.v validator_error_action_failed ==> None? pp) /\
      (res == validator_success ==> (Some? pp /\ SZ.v v_pos' == SZ.v v_pos + snd (Some?.v pp)))
  )))

inline_for_extraction noextract
fn validate_eta
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t p extra_state has_action use_error_handler)
: validate_with_action_t p extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  v ctxt error_handler_fn sl extra contents_sl v_sl
}

inline_for_extraction noextract
fn act_with_comment
      (s: string)
      (extra_state: state_dict)
      (#use_error_handler:bool)
      (#res:Type)
      (a: action extra_state res use_error_handler)
: action extra_state res use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (contents_sl: _)
  (v_sl: _)
{
  // TODO: add support for extracting compile-time comments in Pulse
  a ctxt error_handler_fn sl contents_sl v_sl
}

inline_for_extraction
let leaf_reader
  (#nz:bool)
  (#k: parser_kind nz WeakKindStrongPrefix)
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (sl: input_buffer_t) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt t
  (requires (
    I.pts_to sl contents_sl v_sl **
    pure (Some? (LP.parse p v_sl))
  ))
  (ensures (fun res -> exists* v_sl' .
    I.pts_to sl contents_sl v_sl' **
    pure
    begin match LP.parse p v_sl with
    | None -> False
    | Some (y, len) ->
      res == y /\
      v_sl' == Seq.slice v_sl len (Seq.length v_sl)
    end
  ))

inline_for_extraction noextract
fn validate_with_success_action
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#[@@@erasable] t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 extra has_action use_error_handler)
      (a:action extra bool use_error_handler)
  : validate_with_action_t p1 extra true use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let res_validate = v1 ctxt error_handler_fn sl extra contents_sl v_sl;
  if (res_validate = validator_success) {
    let res_action = a ctxt error_handler_fn sl _ _;
    if (res_action) {
      validator_success
    } else {
      validator_error_action_failed
    }
  } else {
    res_validate
  }
}

inline_for_extraction noextract
fn validate_with_error_handler
      (typename: string)
      (fieldname: string)
      (#nz: _)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#[@@@erasable] t1: Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action: _)
      (#use_error_handler:bool)
      (v1:validate_with_action_t p1 extra_state has_action use_error_handler)
  : validate_with_action_t p1 extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let res = v1 ctxt error_handler_fn sl extra contents_sl v_sl;
  if (res = validator_success) { // TODO: turn this `if ... else` into a non-terminal `if (res <> validator_success)` with an `ensures` clause
    res
  } else {
    ((if use_error_handler then error_handler_fn else error_handler_macro) <: error_handler) typename fieldname (error_reason_of_result res) res ctxt sl _ _;
    res
  };
}

inline_for_extraction noextract
fn validate_ret
      (#extra_state: state_dict)
      (#use_error_handler:bool)
  : validate_with_action_t (parse_ret ()) extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  validator_success
}

inline_for_extraction noextract
fn validate_pair
       (typename: string)
       (name1: string)
       (#nz1:_)
       (#k1:parser_kind nz1 WeakKindStrongPrefix)
       (#[@@@erasable] t1:Type)
       (#[@@@erasable] p1:parser k1 t1)
       (k1_const: bool)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action1:bool)
       (#use_error_handler:bool)
       (v1:validate_with_action_t p1 extra_state has_action1 use_error_handler)
       (#nz2:_)
       (#wk2: _)
       (#k2:parser_kind nz2 wk2)
       (#[@@@erasable] t2:Type)
       (#[@@@erasable] p2:parser k2 t2)
       (k2_const: bool)
       (#has_action2:bool)
       (v2:validate_with_action_t p2 extra_state has_action2 use_error_handler)
  : validate_with_action_t
      (p1 `parse_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.nondep_then_eq p1 p2 v_sl;
  let res1 = v1 ctxt error_handler_fn sl _ _ _;
  if (res1 = validator_success) {
    v2 ctxt error_handler_fn sl _ _ _
  } else {
    res1
  }
}


#push-options "--z3rlimit 32"

inline_for_extraction noextract
fn validate_dep_pair_with_refinement_and_action
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader p1)
      (f: t1 -> bool)
      (a:t1 -> action extra_state bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:refine _ f -> Type)
      (#[@@@erasable] p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:refine _ f -> validate_with_action_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_dtuple2_eq (parse_filter p1 f) p2 v_sl;
  LowParse.Spec.Combinators.parse_filter_eq p1 f v_sl;
  let mut pos = 0sz;
  let res_key = v1 ctxt error_handler_fn sl pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r1 sl _ _;
    if (f val_key) {
      let res_action = a val_key ctxt error_handler_fn sl _ _;
      if (res_action) {
      	 v2 val_key ctxt error_handler_fn sl _ _ _;
      } else {
        validator_error_action_failed
      }
    } else {
      validator_error_constraint_failed
    }
  } else {
    res_key
  }
}

#pop-options


noextract
inline_for_extraction
fn action_bind
      (name: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action extra_state a use_error_handler)
      (#b:Type) (g: (a -> action extra_state b use_error_handler))
: action extra_state b use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (contents_sl: _)
  (v_sl: _)
{
  let resf = f ctxt error_handler_fn sl _ _;
  g resf ctxt error_handler_fn sl _ _
}

noextract
inline_for_extraction
fn action_weaken
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action d1 a use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: action d2 a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (contents_sl: _)
  (v_sl: _)
{
  let d3 = state_dict_weaken_sub d2 d1;
  with extra2 . rewrite (forevery_state d2 extra2) as (forevery_state (state_dict_prod d1 d3) extra2);
  forevery_state_dict_prod_unfold () _;
  let res = f ctxt error_handler_fn sl _ _;
  forevery_state_dict_prod_fold d1 d3 ();
  with extra2' . rewrite (forevery_state (state_dict_prod d1 d3) extra2') as (forevery_state d2 extra2');
  res
}

noextract
inline_for_extraction
let action_deref
      (name: string)
      (#a:Type) (x:ref a) (#use_error_handler: bool)
: Tot (action (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler)
= admit ()

noextract
inline_for_extraction
let action_assignment
      (name: string)
      (#a:Type) (x:ref a) (w: a) (#use_error_handler: bool)
: Tot (action (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler)
= admit ()

(*
let external_action t l =
  unit -> Stack t (fun _ -> True) (fun h0 _ h1 -> B.modifies l h0 h1)

noextract
inline_for_extraction
let mk_external_action  #_ f #use_error_handler = fun _ _ _ _ _ _ -> f ()
  
let copy_buffer_inv (x:CP.copy_buffer_t)
: slice_inv
= CP.properties x;
  F.on HS.mem #prop (CP.inv x)
let copy_buffer_loc (x:CP.copy_buffer_t)
: eloc
= CP.loc_of x

inline_for_extraction
noextract
let probe_then_validate 
      (#nz:bool)
      (#maybe_zero_offset:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#inv:slice_inv)
      (#disj:_)
      (#l:eloc)
      (#ha #allow_reading:bool)
      (#ptr_t:Type0)
      (#use_error_handler:bool)
      (typename:string)
      (fieldname:string)
      (v:validate_with_action_t p inv disj l ha allow_reading use_error_handler)
      (src:ptr_t)
      (as_u64:ptr_t -> PA.pure_external_action U64.t)
      (nullable:bool)
      (dest:CP.copy_buffer_t)
      (init:PA.init_probe_dest_t)
      (prep_dest_sz:U64.t)
      (probe:PA.probe_m unit true maybe_zero_offset use_error_handler)
: action (conj_inv inv (copy_buffer_inv dest))
         (conj_disjointness disj (disjoint (copy_buffer_loc dest) l))
         (eloc_union l (copy_buffer_loc dest)) 
          true
           false
           bool
           use_error_handler
  = fun ctxt error_handler_fn input input_length pos posf ->
      CP.properties dest;
      let h0 = HST.get () in
      let src64 = as_u64 src () in
      if nullable && src64 = 0uL
      then (
        //nullable pointers are accepted without probing, if they are null
        true
      )
      else (
        let b = PA.run_probe_m (PA.init_and_probe (typename ^ "." ^ fieldname) init probe) typename fieldname "probe" ctxt error_handler_fn src64 prep_dest_sz dest in
        let h1 = HST.get () in
        modifies_address_liveness_insensitive_unused_in h0 h1;
        if b <> 0uL
        then (
          let result = v ctxt error_handler_fn (CP.stream_of dest) (CP.stream_len dest) 0uL in
          not (LPE.is_error result)
        )
        else (
          (if use_error_handler
           then begin
             [@inline_let] let eh2 : error_handler = error_handler_fn in
             eh2 typename fieldname
               LPE.(error_reason_of_result validator_error_probe_failed)
               LPE.(get_validator_error_kind validator_error_probe_failed)
               ctxt input pos
           end
           else error_handler_macro typename fieldname
             LPE.(error_reason_of_result validator_error_probe_failed)
             LPE.(get_validator_error_kind validator_error_probe_failed)
             ctxt input pos);
          false
        )
      )

#pop-options