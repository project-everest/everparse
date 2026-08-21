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
module U32 = FStar.UInt32
module P = EverParse3d.Prelude
module SZ = FStar.SizeT

open EverParse3d.State

let action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (extra_state: state_dict)
  (a: Type0)
  (use_error_handler: bool)
=
  ctxt: app_ctxt ->
  error_handler_fn : (if use_error_handler then error_handler #base_t #len_t #pos_t else unit) ->
  sl_base: base_t ->
  sl_len: len_t ->
  sl_pos: pos_t ->
  contents_sl: Ghost.erased (Seq.seq U8.t) ->
  v_sl: Ghost.erased (Seq.seq U8.t) ->
  stt a
    (exists* v_ctxt extra .
      pts_to ctxt v_ctxt **
      I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      forevery_state extra_state extra
    )
    (fun _ -> exists* v_ctxt' extra' .
      pts_to ctxt v_ctxt' **
      I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      forevery_state extra_state extra'
    )

module LP = LowParse.Spec.Base

inline_for_extraction noextract
let validate_with_action_t
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
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
  (error_handler_fn : (if use_error_handler then error_handler #base_t #len_t #pos_t else unit)) ->
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (extra: forevery_values extra_state) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt U8.t
  (requires exists* v_ctxt .
    pts_to ctxt v_ctxt **
    I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
    forevery_state extra_state extra
  )
  (ensures fun res -> exists* v_ctxt' v_sl' extra' .
    pts_to ctxt v_ctxt' **
    I.pts_to sl_base sl_len sl_pos contents_sl v_sl' **
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
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
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
  (error_handler_fn : (if use_error_handler then error_handler #base_t #len_t #pos_t else unit)) ->
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (pos: ref SZ.t) ->
  (extra: forevery_values extra_state) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_pos: Ghost.erased SZ.t) ->
  stt U8.t
  (requires exists* v_ctxt .
    pts_to ctxt v_ctxt **
    I.pts_to sl_base sl_len sl_pos contents_sl v_sl ** // necessary for actions and the error handler
    pts_to pos v_pos **
    forevery_state extra_state extra **
    pure (SZ.v v_pos <= Seq.length v_sl)
  )
  (ensures fun res -> exists* v_ctxt' extra' v_pos' .
    pts_to ctxt v_ctxt' **
    I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
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
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  v ctxt error_handler_fn sl_base sl_len sl_pos extra contents_sl v_sl
}

inline_for_extraction noextract
fn act_with_comment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (s: string)
      (extra_state: state_dict)
      (#use_error_handler:bool)
      (#res:Type)
      (a: action #base_t #len_t #pos_t extra_state res use_error_handler)
: action #base_t #len_t #pos_t extra_state res use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  // TODO: add support for extracting compile-time comments in Pulse
  a ctxt error_handler_fn sl_base sl_len sl_pos contents_sl v_sl
}

inline_for_extraction
let leaf_reader
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#nz:bool)
  (#k: parser_kind nz WeakKindStrongPrefix)
  (#t: Type)
  (p: parser k t)
: Tot Type
=
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt t
  (requires (
    I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
    pure (Some? (LP.parse p v_sl))
  ))
  (ensures (fun res -> exists* v_sl' .
    I.pts_to sl_base sl_len sl_pos contents_sl v_sl' **
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
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#[@@@erasable] t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_t #base_t #len_t #pos_t p1 extra has_action use_error_handler)
      (a:action #base_t #len_t #pos_t extra bool use_error_handler)
  : validate_with_action_t #base_t #len_t #pos_t p1 extra true use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let res_validate = v1 ctxt error_handler_fn sl_base sl_len sl_pos extra contents_sl v_sl;
  if (res_validate = validator_success) {
    let res_action = a ctxt error_handler_fn sl_base sl_len sl_pos _ _;
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
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
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
      (v1:validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action use_error_handler)
  : validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let res = v1 ctxt error_handler_fn sl_base sl_len sl_pos extra contents_sl v_sl;
  if (res = validator_success) { // TODO: turn this `if ... else` into a non-terminal `if (res <> validator_success)` with an `ensures` clause
    res
  } else {
    ((if use_error_handler then error_handler_fn else error_handler_macro) <: error_handler #base_t #len_t #pos_t #inst) typename fieldname (error_reason_of_result res) res ctxt sl_base sl_len sl_pos _ _;
    res
  };
}

inline_for_extraction noextract
fn validate_ret
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
  : validate_with_action_t #base_t #len_t #pos_t (parse_ret ()) extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  validator_success
}

inline_for_extraction noextract
fn validate_pair
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
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
       (v1:validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
       (#nz2:_)
       (#wk2: _)
       (#k2:parser_kind nz2 wk2)
       (#[@@@erasable] t2:Type)
       (#[@@@erasable] p2:parser k2 t2)
       (k2_const: bool)
       (#has_action2:bool)
       (v2:validate_with_action_t #base_t #len_t #pos_t p2 extra_state has_action2 use_error_handler)
  : validate_with_action_t
      #base_t #len_t #pos_t
      (p1 `parse_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.nondep_then_eq p1 p2 v_sl;
  let res1 = v1 ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
  if (res1 = validator_success) {
    v2 ctxt error_handler_fn sl_base sl_len sl_pos _ _ _
  } else {
    res1
  }
}


#push-options "--z3rlimit 32"

inline_for_extraction noextract
fn validate_dep_pair_with_refinement_and_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (f: t1 -> bool)
      (a:t1 -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:refine _ f -> Type)
      (#[@@@erasable] p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:refine _ f -> validate_with_action_t #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_t
      #base_t #len_t #pos_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_dtuple2_eq (parse_filter p1 f) p2 v_sl;
  LowParse.Spec.Combinators.parse_filter_eq p1 f v_sl;
  let mut pos = 0sz;
  let res_key = v1 ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r1 sl_base sl_len sl_pos _ _;
    if (f val_key) {
      let res_action = a val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _;
      if (res_action) {
      	 v2 val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
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

inline_for_extraction noextract
fn validate_filter
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (r:leaf_reader #base_t #len_t #pos_t p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
  : validate_with_action_t #base_t #len_t #pos_t (p `parse_filter` f) extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_filter_eq p f v_sl;
  let mut pos = 0sz;
  let res_key = v ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r sl_base sl_len sl_pos _ _;
    if (f val_key) {
      validator_success
    } else {
      validator_error_constraint_failed
    }
  } else {
    res_key
  }
}

inline_for_extraction noextract
fn validate_filter_with_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (r:leaf_reader #base_t #len_t #pos_t p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
       (a: t -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
  : validate_with_action_t
      #base_t #len_t #pos_t
      (p `parse_filter` f)
      extra_state
      true
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_filter_eq p f v_sl;
  let mut pos = 0sz;
  let res_key = v ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r sl_base sl_len sl_pos _ _;
    if (f val_key) {
      let res_action = a val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _;
      if (res_action) {
      	validator_success
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

inline_for_extraction noextract
fn validate_weaken_left
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_t #base_t #len_t #pos_t (parse_weaken_left p k') extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  v ctxt error_handler_fn sl_base sl_len sl_pos _ _ _
}

inline_for_extraction noextract
fn validate_weaken_right
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_t #base_t #len_t #pos_t (parse_weaken_right p k') extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  v ctxt error_handler_fn sl_base sl_len sl_pos _ _ _
}

#push-options "--z3rlimit 32"

noextract
inline_for_extraction
fn validate_weaken
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] d1: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #base_t #len_t #pos_t p d1 has_action use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_t #base_t #len_t #pos_t p d2 has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let d3 = state_dict_weaken_sub d2 d1;
  with extra2 . assert (forevery_state d2 extra2);
  rewrite (forevery_state d2 extra2) as (forevery_state (state_dict_prod d1 d3) extra2);
  forevery_state_dict_prod_unfold () _;
  with extra1 . assert (forevery_state d1 extra1);
  with extra3 . assert (forevery_state d3 extra3);
  forevery_values_ext d2 extra2 (mk_prod_value extra1 extra3 ());
  let res = v ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
  forevery_state_dict_prod_fold d1 d3 ();
  with extra2' . rewrite (forevery_state (state_dict_prod d1 d3) extra2') as (forevery_state d2 extra2');
  res
}

#pop-options

noextract
inline_for_extraction
fn validate_call
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] d': state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #base_t #len_t #pos_t p d' has_action use_error_handler)
      (d: state_dict)
      (#[@@@erasable] f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#[@@@erasable] g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      ([@@@erasable] sq: squash (state_dict_rename_prop d d' f g))
: validate_with_action_t #base_t #len_t #pos_t p d has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  state_dict_rename_call d d' f g sq extra;
  state_dict_rename_values_return_call d d' f g extra;
  let res = v ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
  state_dict_rename_return d d' f g sq extra _;
  res
}

inline_for_extraction noextract
fn validate_impos
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#extra_state: _)
       (#use_error_handler:bool)
       (_:unit)
  : validate_with_action_t #base_t #len_t #pos_t (parse_impos ()) extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  validator_error_impossible
}

noextract inline_for_extraction
fn validate_ite
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (e:bool)
       (#[@@@erasable] a:squash e -> Type)
       (#[@@@erasable] b:squash (not e) -> Type)
       (#[@@@erasable] extra_state: _)
       (#ha1:_)
       (#ha2:_)
       (#use_error_handler:bool)
       ([@@@erasable] p1:squash e -> parser k (a()))
       (v1:(squash e -> validate_with_action_t #base_t #len_t #pos_t (p1()) extra_state ha1 use_error_handler))
       ([@@@erasable] p2:squash (not e) -> parser k (b()))
       (v2:(squash (not e) -> validate_with_action_t #base_t #len_t #pos_t (p2()) extra_state ha2 use_error_handler))
  : validate_with_action_t
      #base_t #len_t #pos_t
      (parse_ite e p1 p2)
      extra_state
      (ha1 || ha2)
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  if (e) {
    v1 () ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
  } else {
    v2 () ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
  }
}

(* [FStar.SizeT.t] is at least as large as [FStar.UInt32.t]. This is
   guaranteed by the `EVERPARSE_STATIC_ASSERT(sizeof(size_t) >= sizeof(uint32_t))`
   emitted by the 3D frontend in the generated Wrapper file. *)
assume val size_t_fits_u32 : squash SZ.fits_u32

module FLD = LowParse.Spec.FLData

(* Unfolding lemmas for the fixed-length-data-based combinators. Those
   hold by computation, so they cost nothing. *)

let parse_fldata_eq
  (#k: LP.parser_kind) (#t: Type) (p: LP.parser k t) (sz: nat) (input: LP.bytes)
: Lemma
  (LP.parse (FLD.parse_fldata p sz) input == (
    if Seq.length input < sz
    then None
    else match LP.parse p (Seq.slice input 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = sz then Some (v, (sz <: LP.consumed_length input)) else None
    | _ -> None
  ))
= ()

let parse_t_exact_eq
  (n: U32.t) (#nz: _) (#wk: _) (#k: parser_kind nz wk) (#t: Type) (p: parser k t) (input: LP.bytes)
: Lemma
  (LP.parse (parse_t_exact n p) input == LP.parse (FLD.parse_fldata p (U32.v n)) input)
= ()

let parse_t_at_most_eq
  (n: U32.t) (#nz: _) (#wk: _) (#k: parser_kind nz wk) (#t: Type) (p: parser k t) (input: LP.bytes)
: Lemma
  (LP.parse (parse_t_at_most n p) input ==
    LP.parse (FLD.parse_fldata (LowParse.Spec.Combinators.nondep_then p parse_all_bytes) (U32.v n)) input)
= ()

let parse_nlist_eq
  (n: U32.t) (n_is_const: option nat { memoizes_n_as_const n_is_const n })
  (#wk: _) (#k: parser_kind true wk) (#t: Type) (p: parser k t) (input: LP.bytes)
: Lemma
  (LP.parse (parse_nlist n n_is_const p) input ==
    LP.parse (FLD.parse_fldata (LowParse.Spec.List.parse_list p) (U32.v n)) input)
= ()

(* [Seq.append v1' v2] is a suffix of [Seq.append v1 v2] whenever [v1'] is a
   suffix of [v1]. This is what lets us relate the state of the truncated
   stream, after validation, back to the state of the enclosing stream. *)
let seq_is_suffix_of_append
  (v1' v1 v2: Seq.seq LP.byte)
: Lemma
  (requires (v1' `I.seq_is_suffix_of` v1))
  (ensures (Seq.append v1' v2 `I.seq_is_suffix_of` Seq.append v1 v2))
= let large = Seq.append v1 v2 in
  let small = Seq.append v1' v2 in
  Seq.lemma_eq_elim
    (Seq.slice large (Seq.length large - Seq.length small) (Seq.length large))
    small

(* The contents of the enclosing stream are recovered by appending the leftover
   suffix to the contents of the truncated stream. This is the pure side
   condition of [I.untruncate]. *)
let seq_truncate_append
  (contents v v1 v2 contents1: Seq.seq LP.byte)
: Lemma
  (requires (
    v `I.seq_is_suffix_of` contents /\
    Seq.equal contents1 (Seq.append (Seq.slice contents 0 (Seq.length contents - Seq.length v)) v1) /\
    v == Seq.append v1 v2
  ))
  (ensures (contents == Seq.append contents1 v2))
= let k = Seq.length contents - Seq.length v in
  Seq.append_assoc (Seq.slice contents 0 k) v1 v2;
  Seq.lemma_eq_elim contents (Seq.append (Seq.slice contents 0 k) v);
  Seq.lemma_eq_elim contents (Seq.append contents1 v2)

(* The bytes remaining in the enclosing stream, after the truncated prefix has
   been fully consumed, are exactly [Seq.slice v_sl (U32.v n) (Seq.length v_sl)]. *)
let seq_append_empty_slice
  (v_sl v1 v2: Seq.seq LP.byte) (n: nat)
: Lemma
  (requires (
    n <= Seq.length v_sl /\
    Seq.equal v1 (Seq.slice v_sl 0 n) /\
    Seq.equal v2 (Seq.slice v_sl n (Seq.length v_sl))
  ))
  (ensures (Seq.equal (Seq.append Seq.empty v2) (Seq.slice v_sl n (Seq.length v_sl))))
= ()

(* [Seq.empty] is a suffix of any sequence. *)
let seq_empty_is_suffix_of
  (v: Seq.seq LP.byte)
: Lemma
  (Seq.empty #LP.byte `I.seq_is_suffix_of` v)
= Seq.lemma_eq_elim (Seq.slice v (Seq.length v) (Seq.length v)) (Seq.empty #LP.byte)

(* [I.seq_is_suffix_of] is reflexive and transitive. *)
let seq_is_suffix_of_refl
  (v: Seq.seq LP.byte)
: Lemma
  (v `I.seq_is_suffix_of` v)
= Seq.lemma_eq_elim (Seq.slice v 0 (Seq.length v)) v

let seq_is_suffix_of_trans
  (v1 v2 v3: Seq.seq LP.byte)
: Lemma
  (requires (v1 `I.seq_is_suffix_of` v2 /\ v2 `I.seq_is_suffix_of` v3))
  (ensures (v1 `I.seq_is_suffix_of` v3))
= Seq.lemma_eq_elim
    (Seq.slice v3 (Seq.length v3 - Seq.length v1) (Seq.length v3))
    v1

(* Same as [seq_append_empty_slice], but for an arbitrary empty sequence. *)
let seq_append_nil_slice
  (v_sl v1 v2 vcur: Seq.seq LP.byte) (n: nat)
: Lemma
  (requires (
    n <= Seq.length v_sl /\
    Seq.equal v1 (Seq.slice v_sl 0 n) /\
    Seq.equal v2 (Seq.slice v_sl n (Seq.length v_sl)) /\
    Seq.length vcur == 0
  ))
  (ensures (Seq.equal (Seq.append vcur v2) (Seq.slice v_sl n (Seq.length v_sl))))
= ()

module LPL = LowParse.Spec.List

(* [LPL.parse_list] has the [ParserConsumesAll] subkind, so whenever it
   succeeds, it consumes the whole input. *)
let parse_list_consumes_all
  (#wk: _) (#k: parser_kind true wk) (#t: Type) (p: parser k t) (b: LP.bytes)
: Lemma
  (match LP.parse (LPL.parse_list p) b with
   | Some (_, consumed) -> (consumed <: nat) == Seq.length b
   | _ -> True)
= LP.parser_kind_prop_equiv (LPL.parse_list_kind k.LP.parser_kind_injective) (LPL.parse_list p)

#push-options "--z3rlimit 32"

noextract inline_for_extraction
fn validate_nlist
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (n:U32.t)
       (n_is_const:option nat { memoizes_n_as_const n_is_const n})
       (#wk: _)
       (#k:parser_kind true wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: _)
       (#ha:bool)
       (#use_error_handler:bool)
       (v: validate_with_action_t #base_t #len_t #pos_t p extra_state ha use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t (parse_nlist n n_is_const p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  parse_nlist_eq n n_is_const p v_sl;
  parse_fldata_eq (LPL.parse_list p) (U32.v n) v_sl;
  let n_sz = SZ.uint32_to_sizet n;
  let hasBytes = I.has sl_base sl_len sl_pos n_sz contents_sl v_sl;
  I.pts_to_is_suffix_of sl_base sl_len sl_pos contents_sl v_sl;
  if (not hasBytes) {
    validator_error_not_enough_data
  } else {
    let tr = I.truncate sl_base sl_len sl_pos n_sz contents_sl v_sl;
    with contents1 v1 v2. assert (
      I.pts_to tr._1 tr._2 tr._3 contents1 v1 **
      I.is_prefix_of tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents_sl v2
    );
    seq_truncate_append contents_sl v_sl v1 v2 contents1;
    parse_list_consumes_all p v1;
    seq_is_suffix_of_refl v1;
    let mut res = validator_success;
    let mut stop = false;
    while (not !stop)
    invariant exists* vres vstop vcur v_ctxt' extra' .
      pts_to res vres **
      pts_to stop vstop **
      pts_to ctxt v_ctxt' **
      I.pts_to tr._1 tr._2 tr._3 contents1 vcur **
      forevery_state extra_state extra' **
      pure (
        vcur `I.seq_is_suffix_of` v1 /\
        (vres == validator_error_action_failed ==> ha) /\
        (not ha ==> extra' == extra) /\
        (U8.v vres > U8.v validator_error_action_failed ==> None? (LP.parse (LPL.parse_list p) v1)) /\
        (vres =!= validator_success ==> vstop == true) /\
        (vres == validator_success ==>
          (Some? (LP.parse (LPL.parse_list p) v1) <==> Some? (LP.parse (LPL.parse_list p) vcur))) /\
        (vres == validator_success /\ vstop == true ==> Seq.length vcur == 0)
      )
    {
      with vcur. assert (I.pts_to tr._1 tr._2 tr._3 contents1 vcur);
      with extra'. assert (forevery_state extra_state extra');
      let hasMore = I.has tr._1 tr._2 tr._3 1sz contents1 vcur;
      if (not hasMore) {
        stop := true;
      } else {
        LPL.parse_list_eq' p vcur;
        let r = v ctxt error_handler_fn tr._1 tr._2 tr._3 extra' contents1 vcur;
        with vcur'. assert (I.pts_to tr._1 tr._2 tr._3 contents1 vcur');
        seq_is_suffix_of_trans vcur' vcur v1;
        if (r = validator_success) {
          ()
        } else {
          res := r;
          stop := true;
        }
      }
    };
    let fres = !res;
    with vcur. assert (I.pts_to tr._1 tr._2 tr._3 contents1 vcur);
    LPL.parse_list_eq p vcur;
    Seq.lemma_eq_elim v1 (Seq.slice v_sl 0 (U32.v n));
    seq_is_suffix_of_append vcur v1 v2;
    I.untruncate tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents1 vcur contents_sl v2;
    if (fres = validator_success) {
      seq_append_nil_slice v_sl v1 v2 vcur (U32.v n);
      fres
    } else {
      fres
    }
  }
}

noextract inline_for_extraction
fn validate_t_at_most
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #base_t #len_t #pos_t p extra_state ha use_error_handler)
  : validate_with_action_t #base_t #len_t #pos_t (parse_t_at_most n p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  parse_t_at_most_eq n p v_sl;
  parse_fldata_eq (LowParse.Spec.Combinators.nondep_then p parse_all_bytes) (U32.v n) v_sl;
  let n_sz = SZ.uint32_to_sizet n;
  let hasBytes = I.has sl_base sl_len sl_pos n_sz contents_sl v_sl;
  I.pts_to_is_suffix_of sl_base sl_len sl_pos contents_sl v_sl;
  if (not hasBytes) {
    validator_error_not_enough_data
  } else {
    LowParse.Spec.Combinators.nondep_then_eq p parse_all_bytes (Seq.slice v_sl 0 (U32.v n));
    let tr = I.truncate sl_base sl_len sl_pos n_sz contents_sl v_sl;
    with contents1 v1 v2. assert (
      I.pts_to tr._1 tr._2 tr._3 contents1 v1 **
      I.is_prefix_of tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents_sl v2
    );
    seq_truncate_append contents_sl v_sl v1 v2 contents1;
    let res = v ctxt error_handler_fn tr._1 tr._2 tr._3 extra _ _;
    if (res = validator_success) {
      with v1'. assert (I.pts_to tr._1 tr._2 tr._3 contents1 v1');
      let unused = I.empty tr._1 tr._2 tr._3 contents1 v1';
      seq_empty_is_suffix_of v1;
      seq_is_suffix_of_append (Seq.empty #LP.byte) v1 v2;
      I.untruncate tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents1 (Seq.empty #LP.byte) contents_sl v2;
      seq_append_empty_slice v_sl v1 v2 (U32.v n);
      validator_success
    } else {
      with v1'. assert (I.pts_to tr._1 tr._2 tr._3 contents1 v1');
      seq_is_suffix_of_append v1' v1 v2;
      I.untruncate tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents1 v1' contents_sl v2;
      res
    }
  }
}

noextract inline_for_extraction
fn validate_t_exact
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #base_t #len_t #pos_t p extra_state ha use_error_handler)
  : validate_with_action_t #base_t #len_t #pos_t (parse_t_exact n p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  parse_t_exact_eq n p v_sl;
  parse_fldata_eq p (U32.v n) v_sl;
  let n_sz = SZ.uint32_to_sizet n;
  let hasBytes = I.has sl_base sl_len sl_pos n_sz contents_sl v_sl;
  I.pts_to_is_suffix_of sl_base sl_len sl_pos contents_sl v_sl;
  if (not hasBytes) {
    validator_error_not_enough_data
  } else {
    let tr = I.truncate sl_base sl_len sl_pos n_sz contents_sl v_sl;
    with contents1 v1 v2. assert (
      I.pts_to tr._1 tr._2 tr._3 contents1 v1 **
      I.is_prefix_of tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents_sl v2
    );
    seq_truncate_append contents_sl v_sl v1 v2 contents1;
    let res = v ctxt error_handler_fn tr._1 tr._2 tr._3 extra _ _;
    if (res = validator_success) {
      with v1'. assert (I.pts_to tr._1 tr._2 tr._3 contents1 v1');
      let stillHasBytes = I.has tr._1 tr._2 tr._3 1sz contents1 v1';
      seq_is_suffix_of_append v1' v1 v2;
      I.untruncate tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents1 v1' contents_sl v2;
      if (stillHasBytes) {
        validator_error_unexpected_padding
      } else {
        seq_append_empty_slice v_sl v1 v2 (U32.v n);
        validator_success
      }
    } else {
      with v1'. assert (I.pts_to tr._1 tr._2 tr._3 contents1 v1');
      seq_is_suffix_of_append v1' v1 v2;
      I.untruncate tr._1 tr._2 tr._3 sl_base sl_len sl_pos contents1 v1' contents_sl v2;
      res
    }
  }
}

#pop-options

inline_for_extraction noextract
fn read_filter
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#k: parser_kind nz WeakKindStrongPrefix)
       (#t: Type0)
       (#[@@@erasable] p: parser k t)
       (p32: leaf_reader #base_t #len_t #pos_t p)
       (f: (t -> bool))
    : leaf_reader #base_t #len_t #pos_t (parse_filter p f)
=
  (sl_base: base_t)
  (sl_len: len_t)
  (sl_pos: pos_t)
  (contents_sl: Ghost.erased (Seq.seq U8.t))
  (v_sl: Ghost.erased (Seq.seq U8.t))
{
  LowParse.Spec.Combinators.parse_filter_eq p f v_sl;
  let res = p32 sl_base sl_len sl_pos _ _;
  assert pure (f res == true);
  res
}

inline_for_extraction noextract
fn read_impos
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
    ()
    : leaf_reader #base_t #len_t #pos_t (parse_impos())
=
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  ()
}

inline_for_extraction
let validator
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t) (#use_error_handler:bool)
  = validate_with_action_no_read #base_t #len_t #pos_t p state_dict_empty false use_error_handler




noextract
inline_for_extraction
fn action_bind
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #base_t #len_t #pos_t extra_state a use_error_handler)
      (#b:Type) (g: (a -> action #base_t #len_t #pos_t extra_state b use_error_handler))
: action #base_t #len_t #pos_t extra_state b use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  let resf = f ctxt error_handler_fn sl_base sl_len sl_pos _ _;
  g resf ctxt error_handler_fn sl_base sl_len sl_pos _ _
}

noextract
inline_for_extraction
fn action_weaken
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #base_t #len_t #pos_t d1 a use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: action #base_t #len_t #pos_t d2 a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  let d3 = state_dict_weaken_sub d2 d1;
  with extra2 . rewrite (forevery_state d2 extra2) as (forevery_state (state_dict_prod d1 d3) extra2);
  forevery_state_dict_prod_unfold () _;
  let res = f ctxt error_handler_fn sl_base sl_len sl_pos _ _;
  forevery_state_dict_prod_fold d1 d3 ();
  with extra2' . rewrite (forevery_state (state_dict_prod d1 d3) extra2') as (forevery_state d2 extra2');
  res
}

noextract
inline_for_extraction
fn action_call
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d': state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (act: action #base_t #len_t #pos_t d' a use_error_handler)
      (d: state_dict)
      (#[@@@erasable] f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#[@@@erasable] g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      ([@@@erasable] sq: squash (state_dict_rename_prop d d' f g))
: action #base_t #len_t #pos_t d a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  state_dict_rename_call d d' f g sq _;
  let res = act ctxt error_handler_fn sl_base sl_len sl_pos _ _;
  state_dict_rename_return d d' f g sq _ _;
  res
}

noextract
inline_for_extraction
fn action_deref
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#a:Type0) (x:ref a) (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  forevery_state_dict_singleton_unfold' _ _ _;
  let res = !x;
  forevery_state_dict_singleton_fold name (pts_to x #1.0R) _;
  res
}

noextract
inline_for_extraction
fn action_assignment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#a:Type) (x:ref a) (w: a) (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  forevery_state_dict_singleton_unfold' _ _ _;
  x := w;
  forevery_state_dict_singleton_fold name (pts_to x #1.0R) _;
  w
}

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

////////////////////////////////////////////////////////////////////////////////
// Group A combinators: actions
////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
fn action_return
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (x: a)
: action #base_t #len_t #pos_t extra_state a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  x
}

noextract
inline_for_extraction
fn action_return_true
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  true
}

noextract
inline_for_extraction
fn action_abort
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  false
}

noextract
inline_for_extraction
fn action_seq
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #base_t #len_t #pos_t extra_state a use_error_handler)
      (#b: Type)
      (g: action #base_t #len_t #pos_t extra_state b use_error_handler)
: action #base_t #len_t #pos_t extra_state b use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  let ignored = f ctxt error_handler_fn sl_base sl_len sl_pos _ _;
  g ctxt error_handler_fn sl_base sl_len sl_pos _ _
}

noextract
inline_for_extraction
fn action_ite
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (guard: bool)
      (then_: (squash (guard == true) -> action #base_t #len_t #pos_t extra_state a use_error_handler))
      (else_: (squash (guard == false) -> action #base_t #len_t #pos_t extra_state a use_error_handler))
: action #base_t #len_t #pos_t extra_state a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  if (guard) {
    then_ () ctxt error_handler_fn sl_base sl_len sl_pos _ _
  } else {
    else_ () ctxt error_handler_fn sl_base sl_len sl_pos _ _
  }
}

////////////////////////////////////////////////////////////////////////////////
// Group A combinators: validators
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
fn validate_with_comment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (c: string)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  // TODO: add support for extracting compile-time comments in Pulse
  v ctxt error_handler_fn sl_base sl_len sl_pos extra contents_sl v_sl
}

inline_for_extraction noextract
fn validate_unit
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_t #base_t #len_t #pos_t parse_unit extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  validator_success
}

inline_for_extraction noextract
fn validate_unit_refinement
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (f: unit -> bool)
      (cf: string)
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_t #base_t #len_t #pos_t (parse_filter parse_unit f) extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_filter_eq parse_unit f v_sl;
  if (f ()) {
    validator_success
  } else {
    validator_error_constraint_failed
  }
}

#push-options "--z3rlimit 32"

inline_for_extraction noextract
fn validate_dep_pair
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:t1 -> Type)
      (#[@@@erasable] p2:(x:t1 -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:t1 -> validate_with_action_t #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_t
      #base_t #len_t #pos_t
      (p1 `parse_dep_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_dtuple2_eq p1 p2 v_sl;
  let mut pos = 0sz;
  let res_key = v1 ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r1 sl_base sl_len sl_pos _ _;
    v2 val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
  } else {
    res_key
  }
}

inline_for_extraction noextract
fn validate_dep_pair_with_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (a:t1 -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:t1 -> Type)
      (#[@@@erasable] p2:(x:t1 -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:t1 -> validate_with_action_t #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_t
      #base_t #len_t #pos_t
      (p1 `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_dtuple2_eq p1 p2 v_sl;
  let mut pos = 0sz;
  let res_key = v1 ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r1 sl_base sl_len sl_pos _ _;
    let res_action = a val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _;
    if (res_action) {
      v2 val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
    } else {
      validator_error_action_failed
    }
  } else {
    res_key
  }
}

inline_for_extraction noextract
fn validate_dep_pair_with_refinement
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (f: t1 -> bool)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:refine _ f -> Type)
      (#[@@@erasable] p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:refine _ f -> validate_with_action_t #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_t
      #base_t #len_t #pos_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_dtuple2_eq (parse_filter p1 f) p2 v_sl;
  LowParse.Spec.Combinators.parse_filter_eq p1 f v_sl;
  let mut pos = 0sz;
  let res_key = v1 ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r1 sl_base sl_len sl_pos _ _;
    if (f val_key) {
      v2 val_key ctxt error_handler_fn sl_base sl_len sl_pos _ _ _;
    } else {
      validator_error_constraint_failed
    }
  } else {
    res_key
  }
}

inline_for_extraction noextract
fn validate_with_dep_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#nz:_)
      (#k:parser_kind nz WeakKindStrongPrefix)
      (#t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
      (r:leaf_reader #base_t #len_t #pos_t p)
      (a: t -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
  : validate_with_action_t #base_t #len_t #pos_t p extra_state true use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let mut pos = 0sz;
  let res = v ctxt error_handler_fn sl_base sl_len sl_pos pos _ _ _ _;
  if (res = validator_success) {
    let field_value = r sl_base sl_len sl_pos _ _;
    let action_result = a field_value ctxt error_handler_fn sl_base sl_len sl_pos _ _;
    if (action_result) {
      validator_success
    } else {
      validator_error_action_failed
    }
  } else {
    res
  }
}

#pop-options

////////////////////////////////////////////////////////////////////////////////
// Group A combinators: leaf validators and readers
////////////////////////////////////////////////////////////////////////////////

module LPP = LowParse.PulseParse.Base

inline_for_extraction noextract
fn validate_total_constant_size_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      ([@@@erasable] p:parser k t)
      (sz: SZ.t)
      ([@@@erasable] u: squash (
        k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
        k.LP.parser_kind_low == SZ.v sz /\
        k.LP.parser_kind_metadata == Some LP.ParserKindMetadataTotal
      ))
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t p extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
  (v_pos: _)
{
  LP.parser_kind_prop_equiv k p;
  let p0 = !pos;
  let hasBytes = I.has_at sl_base sl_len sl_pos p0 sz contents_sl v_sl;
  if (hasBytes) {
    pos := SZ.add p0 sz;
    validator_success
  } else {
    validator_error_not_enough_data
  }
}

inline_for_extraction noextract
fn lift_reader
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#k:parser_kind nz WeakKindStrongPrefix)
      (#[@@@erasable] t:Type0)
      ([@@@erasable] p:parser k t)
      (r: P.reader p)
      (sz: SZ.t)
      ([@@@erasable] u: squash (
        k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
        k.LP.parser_kind_low == SZ.v sz
      ))
: leaf_reader #base_t #len_t #pos_t p
=
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  LP.parser_kind_prop_equiv k p;
  I.read t k p (LPP.leaf_reader_of_reader r) sl_base sl_len sl_pos sz contents_sl v_sl
}

inline_for_extraction noextract
fn validate____UINT8
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT8 extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT8 1sz ()

inline_for_extraction noextract
fn read____UINT8
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT8
= lift_reader parse____UINT8 P.read____UINT8 1sz ()

inline_for_extraction noextract
fn validate____UINT8BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT8BE extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT8BE 1sz ()

inline_for_extraction noextract
fn read____UINT8BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT8BE
= lift_reader parse____UINT8BE P.read____UINT8BE 1sz ()

inline_for_extraction noextract
fn validate____UINT16BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT16BE extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT16BE 2sz ()

inline_for_extraction noextract
fn read____UINT16BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT16BE
= lift_reader parse____UINT16BE P.read____UINT16BE 2sz ()

inline_for_extraction noextract
fn validate____UINT32BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT32BE extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT32BE 4sz ()

inline_for_extraction noextract
fn read____UINT32BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT32BE
= lift_reader parse____UINT32BE P.read____UINT32BE 4sz ()

inline_for_extraction noextract
fn validate____UINT64BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT64BE extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT64BE 8sz ()

inline_for_extraction noextract
fn read____UINT64BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT64BE
= lift_reader parse____UINT64BE P.read____UINT64BE 8sz ()

inline_for_extraction noextract
fn validate____UINT16
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT16 extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT16 2sz ()

inline_for_extraction noextract
fn read____UINT16
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT16
= lift_reader parse____UINT16 P.read____UINT16 2sz ()

inline_for_extraction noextract
fn validate____UINT32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT32 extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT32 4sz ()

inline_for_extraction noextract
fn read____UINT32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT32
= lift_reader parse____UINT32 P.read____UINT32 4sz ()

inline_for_extraction noextract
fn validate____UINT64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT64 extra_state false use_error_handler
= validate_total_constant_size_no_read parse____UINT64 8sz ()

inline_for_extraction noextract
fn read____UINT64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT64
= lift_reader parse____UINT64 P.read____UINT64 8sz ()

inline_for_extraction noextract
fn read_unit
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t (parse_ret ())
=
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  Seq.lemma_eq_elim (Seq.slice (Ghost.reveal v_sl) 0 (Seq.length v_sl)) (Ghost.reveal v_sl);
  ()
}

inline_for_extraction noextract
fn validate_all_bytes
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_t #base_t #len_t #pos_t parse_all_bytes extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let ignored = I.empty sl_base sl_len sl_pos contents_sl v_sl;
  seq_empty_is_suffix_of v_sl;
  Seq.lemma_eq_elim (Seq.slice (Ghost.reveal v_sl) (Seq.length v_sl) (Seq.length v_sl)) (Seq.empty #LP.byte);
  validator_success
}

////////////////////////////////////////////////////////////////////////////////
// Group B: turning a non-consuming (`no_read`) validator into a consuming one
////////////////////////////////////////////////////////////////////////////////

let seq_slice_is_suffix_of
  (v: Seq.seq LP.byte) (i: nat)
: Lemma
  (requires (i <= Seq.length v))
  (ensures (Seq.slice v i (Seq.length v) `I.seq_is_suffix_of` v))
= Seq.lemma_eq_elim
    (Seq.slice v (Seq.length v - (Seq.length v - i)) (Seq.length v))
    (Seq.slice v i (Seq.length v))

inline_for_extraction noextract
fn validate_drop
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  let mut pos = 0sz;
  let res = v ctxt error_handler_fn sl_base sl_len sl_pos pos extra contents_sl v_sl 0sz;
  if (res = validator_success) {
    let consumed = !pos;
    I.skip sl_base sl_len sl_pos consumed contents_sl v_sl;
    seq_slice_is_suffix_of v_sl (SZ.v consumed);
    validator_success
  } else {
    seq_is_suffix_of_refl (Ghost.reveal v_sl);
    res
  }
}

inline_for_extraction noextract
fn validate_without_reading
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action use_error_handler
= validate_drop v

////////////////////////////////////////////////////////////////////////////////
// Group C: field position actions
////////////////////////////////////////////////////////////////////////////////

noextract
inline_for_extraction
fn action_field_pos_64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state U64.t use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  let pos = I.get_position sl_base sl_len sl_pos contents_sl v_sl;
  SZ.sizet_to_uint64 pos
}

noextract
inline_for_extraction
fn action_field_pos_32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state U32.t use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  let pos = I.get_position sl_base sl_len sl_pos contents_sl v_sl;
  SZ.sizet_to_uint32 pos
}

////////////////////////////////////////////////////////////////////////////////
// Group C: field pointer actions.
//
// In Low*, `action_field_ptr` is available only for the `buffer` backend and
// `action_field_ptr_after` only for the `extern` backend, and this is enforced
// by a global `backend_flag`. Here we do not want to depend on linking against
// a particular module, so instead each of these operations is passed in as an
// `option`, and the corresponding action takes a `squash (Some? ...)` witness.
// A backend that does not support an operation simply provides `None`.
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
let field_ptr_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (ptr_t: Type0)
: Type
= (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt ptr_t
    (I.pts_to sl_base sl_len sl_pos contents_sl v_sl)
    (fun _ -> I.pts_to sl_base sl_len sl_pos contents_sl v_sl)

inline_for_extraction noextract
let field_ptr_after_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (ptr_t: Type0)
: Type
= (sz: U64.t) ->
  (write_to: ref ptr_t) ->
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (w: Ghost.erased ptr_t) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to write_to #1.0R w ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl)
    (fun _ -> exists* w' . pts_to write_to #1.0R w' ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl)

noextract
inline_for_extraction
fn action_field_ptr
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#ptr_t: Type0)
      (f: option (field_ptr_t base_t len_t pos_t ptr_t))
      ([@@@erasable] sq: squash (Some? f))
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state ptr_t use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  (Some?.v f) sl_base sl_len sl_pos contents_sl v_sl
}

noextract
inline_for_extraction
fn action_field_ptr_after
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#ptr_t: Type0)
      (f: option (field_ptr_after_t base_t len_t pos_t ptr_t))
      ([@@@erasable] sq: squash (Some? f))
      (name: string)
      (sz: U64.t)
      (write_to: ref ptr_t)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to write_to #1.0R)) bool use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (contents_sl: _)
  (v_sl: _)
{
  forevery_state_dict_singleton_unfold' _ _ _;
  with w . assert (pts_to write_to #1.0R w);
  let res = (Some?.v f) sz write_to sl_base sl_len sl_pos w contents_sl v_sl;
  forevery_state_dict_singleton_fold name (pts_to write_to #1.0R) _;
  res
}

////////////////////////////////////////////////////////////////////////////////
// Lists that consume all the remaining input
////////////////////////////////////////////////////////////////////////////////

inline_for_extraction noextract
fn validate_list
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#wk: _)
      (#k:parser_kind true wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#ha:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state ha use_error_handler)
: validate_with_action_t
    #base_t #len_t #pos_t
    #false #WeakKindConsumesAll
    #(LPL.parse_list_kind k.LP.parser_kind_injective)
    (LPL.parse_list p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  parse_list_consumes_all p v_sl;
  seq_is_suffix_of_refl (Ghost.reveal v_sl);
  let mut res = validator_success;
  let mut stop = false;
  while (not !stop)
  invariant exists* vres vstop vcur v_ctxt' extra' .
    pts_to res vres **
    pts_to stop vstop **
    pts_to ctxt v_ctxt' **
    I.pts_to sl_base sl_len sl_pos contents_sl vcur **
    forevery_state extra_state extra' **
    pure (
      vcur `I.seq_is_suffix_of` v_sl /\
      (vres == validator_error_action_failed ==> ha) /\
      (not ha ==> extra' == extra) /\
      (U8.v vres > U8.v validator_error_action_failed ==> None? (LP.parse (LPL.parse_list p) v_sl)) /\
      (vres =!= validator_success ==> vstop == true) /\
      (vres == validator_success ==>
        (Some? (LP.parse (LPL.parse_list p) v_sl) <==> Some? (LP.parse (LPL.parse_list p) vcur))) /\
      (vres == validator_success /\ vstop == true ==> Seq.length vcur == 0)
    )
  {
    with vcur. assert (I.pts_to sl_base sl_len sl_pos contents_sl vcur);
    with extra'. assert (forevery_state extra_state extra');
    let hasMore = I.has sl_base sl_len sl_pos 1sz contents_sl vcur;
    if (not hasMore) {
      stop := true;
    } else {
      LPL.parse_list_eq' p vcur;
      let r = v ctxt error_handler_fn sl_base sl_len sl_pos extra' contents_sl vcur;
      with vcur'. assert (I.pts_to sl_base sl_len sl_pos contents_sl vcur');
      seq_is_suffix_of_trans vcur' vcur v_sl;
      if (r = validator_success) {
        ()
      } else {
        res := r;
        stop := true;
      }
    }
  };
  let fres = !res;
  with vcur. assert (I.pts_to sl_base sl_len sl_pos contents_sl vcur);
  LPL.parse_list_eq p vcur;
  Seq.lemma_eq_elim vcur (Seq.slice (Ghost.reveal v_sl) (Seq.length v_sl) (Seq.length v_sl));
  fres
}

inline_for_extraction noextract
fn validate_all_zeros
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[@@@erasable] extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_t #base_t #len_t #pos_t parse_all_zeros extra_state false use_error_handler
= validate_list
    (validate_filter "parse_zeros" validate____UINT8 read____UINT8 is_zero "check if zero" "")

////////////////////////////////////////////////////////////////////////////////
// Lists up to a terminator (strings)
////////////////////////////////////////////////////////////////////////////////

module LUT = LowParse.Spec.ListUpTo

(* While the loop has not reached the terminator yet, the amount of input
   consumed so far is exactly [Seq.length v_sl - Seq.length vcur]. *)
let list_up_to_ongoing
  (#k: LP.parser_kind) (#t: Type) (q: LP.parser k t) (v_sl vcur: Seq.seq LP.byte)
: Tot prop
= (Some? (LP.parse q v_sl) <==> Some? (LP.parse q vcur)) /\
  (Some? (LP.parse q v_sl) ==>
    snd (Some?.v (LP.parse q v_sl)) ==
      (Seq.length v_sl - Seq.length vcur) + snd (Some?.v (LP.parse q vcur)))

let list_up_to_done
  (#k: LP.parser_kind) (#t: Type) (q: LP.parser k t) (v_sl vcur: Seq.seq LP.byte)
: Tot prop
= Some? (LP.parse q v_sl) /\
  snd (Some?.v (LP.parse q v_sl)) == Seq.length v_sl - Seq.length vcur

inline_for_extraction noextract
fn validate_list_up_to
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#k: parser_kind true WeakKindStrongPrefix)
      (#t: eqtype)
      (#[@@@erasable] p: parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#ha:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
      (r: leaf_reader #base_t #len_t #pos_t p)
      (terminator: t)
      ([@@@erasable] prf: LUT.consumes_if_not_cond (cond_string_up_to terminator) p)
: validate_with_action_t
    #base_t #len_t #pos_t
    #true #WeakKindStrongPrefix
    #(LUT.parse_list_up_to_kind k)
    (LUT.parse_list_up_to (cond_string_up_to terminator) p prf)
    extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl_base: _)
  (sl_len: _)
  (sl_pos: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  seq_is_suffix_of_refl (Ghost.reveal v_sl);
  let mut res = validator_success;
  let mut stop = false;
  let mut pos = 0sz;
  while (not !stop)
  invariant exists* vres vstop vpos vcur v_ctxt' extra' .
    pts_to res vres **
    pts_to stop vstop **
    pts_to pos vpos **
    pts_to ctxt v_ctxt' **
    I.pts_to sl_base sl_len sl_pos contents_sl vcur **
    forevery_state extra_state extra' **
    pure (
      vcur `I.seq_is_suffix_of` v_sl /\
      (vres == validator_error_action_failed ==> ha) /\
      (not ha ==> extra' == extra) /\
      (U8.v vres > U8.v validator_error_action_failed ==>
        None? (LP.parse (LUT.parse_list_up_to (cond_string_up_to terminator) p prf) v_sl)) /\
      (vres =!= validator_success ==> vstop == true) /\
      (vres == validator_success ==>
        (if vstop
         then list_up_to_done (LUT.parse_list_up_to (cond_string_up_to terminator) p prf) v_sl vcur
         else list_up_to_ongoing (LUT.parse_list_up_to (cond_string_up_to terminator) p prf) v_sl vcur))
    )
  {
    with vcur. assert (I.pts_to sl_base sl_len sl_pos contents_sl vcur);
    with extra'. assert (forevery_state extra_state extra');
    LUT.parse_list_up_to_eq (cond_string_up_to terminator) p prf vcur;
    pos := 0sz;
    let r0 = v ctxt error_handler_fn sl_base sl_len sl_pos pos extra' contents_sl vcur 0sz;
    if (r0 = validator_success) {
      let x = r sl_base sl_len sl_pos contents_sl vcur;
      with vcur'. assert (I.pts_to sl_base sl_len sl_pos contents_sl vcur');
      seq_slice_is_suffix_of vcur (Seq.length vcur - Seq.length vcur');
      seq_is_suffix_of_trans vcur' vcur v_sl;
      if (x = terminator) {
        stop := true;
      } else {
        ()
      }
    } else {
      res := r0;
      stop := true;
    }
  };
  let fres = !res;
  with vcur. assert (I.pts_to sl_base sl_len sl_pos contents_sl vcur);
  Seq.lemma_eq_elim vcur (Seq.slice (Ghost.reveal v_sl) (Seq.length v_sl - Seq.length vcur) (Seq.length v_sl));
  fres
}

inline_for_extraction noextract
fn validate_string
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#k: parser_kind true WeakKindStrongPrefix)
      (#t: eqtype)
      (#[@@@erasable] p: parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#ha:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
      (r: leaf_reader #base_t #len_t #pos_t p)
      (terminator: t)
: validate_with_action_t #base_t #len_t #pos_t (parse_string p terminator) extra_state ha use_error_handler
= validate_weaken (validate_list_up_to v r terminator (fun _ _ _ -> ())) parse_string_kind

(* In Low*, when the payload has a total constant size, this combinator picks a
   specialized validator that merely checks that enough bytes are available,
   instead of iterating over the elements. This is only an optimization; here we
   always take the general path for now.
   TODO: port validate_nlist_total_constant_size{,_mod_ok,_mod_ko}. *)
inline_for_extraction noextract
fn validate_nlist_constant_size_without_actions
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (n:U32.t)
      (n_is_const:option nat { memoizes_n_as_const n_is_const n})
      (payload_is_constant_size: bool)
      (#wk: _)
      (#k:parser_kind true wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state false use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t (parse_nlist n n_is_const p) extra_state false use_error_handler
= validate_nlist n n_is_const v
