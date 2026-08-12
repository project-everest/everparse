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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
  (extra_state: state_dict)
  (a: Type0)
  (use_error_handler: bool)
=
  ctxt: app_ctxt ->
  error_handler_fn : (if use_error_handler then error_handler #input_buffer_t else unit) ->
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
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
  (error_handler_fn : (if use_error_handler then error_handler #input_buffer_t else unit)) ->
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
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
  (error_handler_fn : (if use_error_handler then error_handler #input_buffer_t else unit)) ->
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#[@@@erasable] t:Type)
      (#[@@@erasable] p:parser k t)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #input_buffer_t p extra_state has_action use_error_handler)
: validate_with_action_t #input_buffer_t p extra_state has_action use_error_handler
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (s: string)
      (extra_state: state_dict)
      (#use_error_handler:bool)
      (#res:Type)
      (a: action #input_buffer_t extra_state res use_error_handler)
: action #input_buffer_t extra_state res use_error_handler
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#[@@@erasable] t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_t #input_buffer_t p1 extra has_action use_error_handler)
      (a:action #input_buffer_t extra bool use_error_handler)
  : validate_with_action_t #input_buffer_t p1 extra true use_error_handler
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
  (error_handler_macro: error_handler #input_buffer_t)
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
      (v1:validate_with_action_t #input_buffer_t p1 extra_state has_action use_error_handler)
  : validate_with_action_t #input_buffer_t p1 extra_state has_action use_error_handler
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
    ((if use_error_handler then error_handler_fn else error_handler_macro) <: error_handler #input_buffer_t #inst) typename fieldname (error_reason_of_result res) res ctxt sl _ _;
    res
  };
}

inline_for_extraction noextract
fn validate_ret
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
  : validate_with_action_t #input_buffer_t (parse_ret ()) extra_state false use_error_handler
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
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
       (v1:validate_with_action_t #input_buffer_t p1 extra_state has_action1 use_error_handler)
       (#nz2:_)
       (#wk2: _)
       (#k2:parser_kind nz2 wk2)
       (#[@@@erasable] t2:Type)
       (#[@@@erasable] p2:parser k2 t2)
       (k2_const: bool)
       (#has_action2:bool)
       (v2:validate_with_action_t #input_buffer_t p2 extra_state has_action2 use_error_handler)
  : validate_with_action_t
      #input_buffer_t
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#[@@@erasable] p1:parser k1 t1)
      (#[@@@erasable] extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #input_buffer_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #input_buffer_t p1)
      (f: t1 -> bool)
      (a:t1 -> action #input_buffer_t extra_state bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#[@@@erasable] t2:refine _ f -> Type)
      (#[@@@erasable] p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:refine _ f -> validate_with_action_t #input_buffer_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_t
      #input_buffer_t
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

inline_for_extraction noextract
fn validate_filter
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #input_buffer_t p extra_state has_action use_error_handler)
       (r:leaf_reader #input_buffer_t p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
  : validate_with_action_t #input_buffer_t (p `parse_filter` f) extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  LowParse.Spec.Combinators.parse_filter_eq p f v_sl;
  let mut pos = 0sz;
  let res_key = v ctxt error_handler_fn sl pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r sl _ _;
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #input_buffer_t p extra_state has_action use_error_handler)
       (r:leaf_reader #input_buffer_t p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
       (a: t -> action #input_buffer_t extra_state bool use_error_handler)
  : validate_with_action_t
      #input_buffer_t
      (p `parse_filter` f)
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
  LowParse.Spec.Combinators.parse_filter_eq p f v_sl;
  let mut pos = 0sz;
  let res_key = v ctxt error_handler_fn sl pos _ _ _ _;
  if (res_key = validator_success) {
    let val_key = r sl _ _;
    if (f val_key) {
      let res_action = a val_key ctxt error_handler_fn sl _ _;
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #input_buffer_t p extra_state has_action use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_t #input_buffer_t (parse_weaken_left p k') extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  v ctxt error_handler_fn sl _ _ _
}

inline_for_extraction noextract
fn validate_weaken_right
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #input_buffer_t p extra_state has_action use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_t #input_buffer_t (parse_weaken_right p k') extra_state has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  v ctxt error_handler_fn sl _ _ _
}

#push-options "--z3rlimit 32"

noextract
inline_for_extraction
fn validate_weaken
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] d1: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #input_buffer_t p d1 has_action use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_t #input_buffer_t p d2 has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
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
  let res = v ctxt error_handler_fn sl _ _ _;
  forevery_state_dict_prod_fold d1 d3 ();
  with extra2' . rewrite (forevery_state (state_dict_prod d1 d3) extra2') as (forevery_state d2 extra2');
  res
}

#pop-options

noextract
inline_for_extraction
fn validate_call
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] d': state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #input_buffer_t p d' has_action use_error_handler)
      (d: state_dict)
      (#[@@@erasable] f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#[@@@erasable] g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      ([@@@erasable] sq: squash (state_dict_rename_prop d d' f g))
: validate_with_action_t #input_buffer_t p d has_action use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  state_dict_rename_call d d' f g sq extra;
  state_dict_rename_values_return_call d d' f g extra;
  let res = v ctxt error_handler_fn sl _ _ _;
  state_dict_rename_return d d' f g sq extra _;
  res
}

inline_for_extraction noextract
fn validate_impos
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (#extra_state: _)
       (#use_error_handler:bool)
       (_:unit)
  : validate_with_action_t #input_buffer_t (parse_impos ()) extra_state false use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  validator_error_impossible
}

noextract inline_for_extraction
fn validate_ite
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
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
       (v1:(squash e -> validate_with_action_t #input_buffer_t (p1()) extra_state ha1 use_error_handler))
       ([@@@erasable] p2:squash (not e) -> parser k (b()))
       (v2:(squash (not e) -> validate_with_action_t #input_buffer_t (p2()) extra_state ha2 use_error_handler))
  : validate_with_action_t
      #input_buffer_t
      (parse_ite e p1 p2)
      extra_state
      (ha1 || ha2)
      use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  if (e) {
    v1 () ctxt error_handler_fn sl _ _ _;
  } else {
    v2 () ctxt error_handler_fn sl _ _ _;
  }
}

noextract inline_for_extraction
fn validate_nlist
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (n:U32.t)
       (n_is_const:option nat { memoizes_n_as_const n_is_const n})
       (#wk: _)
       (#k:parser_kind true wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: _)
       (#ha:bool)
       (#use_error_handler:bool)
       (v: validate_with_action_t #input_buffer_t p extra_state ha use_error_handler)
: validate_with_action_t #input_buffer_t (parse_nlist n n_is_const p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  admit ()
}

noextract inline_for_extraction
fn validate_t_at_most
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #input_buffer_t p extra_state ha use_error_handler)
  : validate_with_action_t #input_buffer_t (parse_t_at_most n p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  admit ()
}

noextract inline_for_extraction
fn validate_t_exact
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#[@@@erasable] t:Type)
       (#[@@@erasable] p:parser k t)
       (#[@@@erasable] extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (v:validate_with_action_t #input_buffer_t p extra_state ha use_error_handler)
  : validate_with_action_t #input_buffer_t (parse_t_exact n p) extra_state ha use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (extra: _)
  (contents_sl: _)
  (v_sl: _)
{
  admit ()
}

inline_for_extraction noextract
fn read_filter
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
       (#nz:_)
       (#k: parser_kind nz WeakKindStrongPrefix)
       (#t: Type0)
       (#[@@@erasable] p: parser k t)
       (p32: leaf_reader #input_buffer_t p)
       (f: (t -> bool))
    : leaf_reader #input_buffer_t (parse_filter p f)
=
  (sl: input_buffer_t)
  (contents_sl: Ghost.erased (Seq.seq U8.t))
  (v_sl: Ghost.erased (Seq.seq U8.t))
{
  LowParse.Spec.Combinators.parse_filter_eq p f v_sl;
  let res = p32 sl _ _;
  assert pure (f res == true);
  res
}

inline_for_extraction noextract
fn read_impos
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
    ()
    : leaf_reader #input_buffer_t (parse_impos())
=
  (sl: _)
  (contents_sl: _)
  (v_sl: _)
{
  ()
}

inline_for_extraction
let validator
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
  #nz #wk (#k:parser_kind nz wk) (#t:Type) (p:parser k t) (#use_error_handler:bool)
  = validate_with_action_no_read #input_buffer_t p state_dict_empty false use_error_handler




noextract
inline_for_extraction
fn action_bind
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (name: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #input_buffer_t extra_state a use_error_handler)
      (#b:Type) (g: (a -> action #input_buffer_t extra_state b use_error_handler))
: action #input_buffer_t extra_state b use_error_handler
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #input_buffer_t d1 a use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: action #input_buffer_t d2 a use_error_handler
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
fn action_call
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (#d': state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (act: action #input_buffer_t d' a use_error_handler)
      (d: state_dict)
      (#[@@@erasable] f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#[@@@erasable] g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      ([@@@erasable] sq: squash (state_dict_rename_prop d d' f g))
: action #input_buffer_t d a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
  (contents_sl: _)
  (v_sl: _)
{
  state_dict_rename_call d d' f g sq _;
  let res = act ctxt error_handler_fn sl _ _;
  state_dict_rename_return d d' f g sq _ _;
  res
}

noextract
inline_for_extraction
fn action_deref
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (name: string)
      (#a:Type0) (x:ref a) (#use_error_handler: bool)
: action #input_buffer_t (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
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
  (#input_buffer_t: Type0)
  {| inst: I.input_stream_inst input_buffer_t  |}
      (name: string)
      (#a:Type) (x:ref a) (w: a) (#use_error_handler: bool)
: action #input_buffer_t (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler
=
  (ctxt: _)
  (error_handler_fn: _)
  (sl: _)
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
