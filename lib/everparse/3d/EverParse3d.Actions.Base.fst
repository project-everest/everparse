module EverParse3d.Actions.Base
friend EverParse3d.Kinds
friend EverParse3d.Prelude
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
  (use_error_handler: bool)
  (a: Type0)
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

[@@CMacro]
let success = 0uy

[@@CMacro]
let action_failed = 1uy

inline_for_extraction noextract
let validate_with_action_t
     (#k:LP.parser_kind)
     (#t:Type)
     (p:LP.parser k t)
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
      (res == action_failed ==> has_action) /\
      (not has_action ==> extra' == extra) /\
      (U8.v res > U8.v action_failed ==> None? (LP.parse p v_sl)) /\
      I.seq_is_suffix_of v_sl' v_sl /\
      (res == success ==> (Some? (LP.parse p v_sl) /\ v_sl' == Seq.slice v_sl (snd (Some?.v (LP.parse p v_sl))) (Seq.length v_sl)))
  ))

inline_for_extraction noextract
let validate_with_action_no_read
     (#k:LP.parser_kind)
     (#t:Type)
     (p:LP.parser k t)
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
      (res == action_failed ==> has_action) /\
      (not has_action ==> extra' == extra) /\
      (U8.v res > U8.v action_failed ==> None? pp /\
      (res == success ==> (Some? pp /\ SZ.v v_pos' == SZ.v v_pos + snd (Some?.v pp)))
  ))))

inline_for_extraction
let leaf_reader
  #nz
  #k
  (#t: Type)
  (p: LP.parser k t)
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


noextract
inline_for_extraction
let action_bind
      (name: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action extra_state use_error_handler a)
      (#b:Type) (g: (a -> action extra_state use_error_handler b))
: Tot (action extra_state use_error_handler b)
= admit ()

noextract
inline_for_extraction
let action_weaken
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action d1 use_error_handler a)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: Tot (action d2 use_error_handler a)
= admit ()

noextract
inline_for_extraction
let action_deref
      (name: string)
      (#a:Type) (x:ref a) (#use_error_handler: bool)
: Tot (action (state_dict_singleton name (pts_to x #1.0R)) use_error_handler a)
= admit ()

noextract
inline_for_extraction
let action_assignment
      (name: string)
      (#a:Type) (x:ref a) (w: a) (#use_error_handler: bool)
: Tot (action (state_dict_singleton name (pts_to x #1.0R)) use_error_handler a)
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