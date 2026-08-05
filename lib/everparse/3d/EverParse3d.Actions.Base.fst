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

let action
  (#extra_state_value: Type0)
  (extra_state: extra_state_value -> slprop)
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
      extra_state extra
    )
    (fun _ -> exists* v_ctxt' extra' .
      pts_to ctxt v_ctxt' **
      I.pts_to sl contents_sl v_sl **
      extra_state extra'
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
     (#extra_state_value: Type0)
     (extra_state: extra_state_value -> slprop)
     (has_action:bool)
     (use_error_handler:bool)
: Type 
= (ctxt: app_ctxt) ->
  (error_handler_fn : (if use_error_handler then error_handler else unit)) ->
  (sl: input_buffer_t) ->
  (extra: Ghost.erased extra_state_value) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt U8.t
  (requires exists* v_ctxt .
    pts_to ctxt v_ctxt **
    I.pts_to sl contents_sl v_sl **
    extra_state extra
  )
  (ensures fun res -> exists* v_ctxt' v_sl' extra' .
    pts_to ctxt v_ctxt' **
    I.pts_to sl contents_sl v_sl' **
    extra_state extra' **
    pure (
      (res == action_failed ==> has_action) /\
      (not has_action ==> extra' == Ghost.reveal extra) /\
      (U8.v res > U8.v action_failed ==> None? (LP.parse p v_sl)) /\
      (res == success ==> (Some? (LP.parse p v_sl) /\ v_sl' == Seq.slice v_sl (snd (Some?.v (LP.parse p v_sl))) (Seq.length v_sl)))
  ))

inline_for_extraction noextract
let validate_with_action_no_read
     (#k:LP.parser_kind)
     (#t:Type)
     (p:LP.parser k t)
     (#extra_state_value: Type0)
     (extra_state: extra_state_value -> slprop)
     (has_action:bool)
     (use_error_handler:bool)
: Type 
= (ctxt: app_ctxt) ->
  (error_handler_fn : (if use_error_handler then error_handler else unit)) ->
  (sl: input_buffer_t) ->
  (pos: ref SZ.t) ->
  (extra: Ghost.erased extra_state_value) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_pos: Ghost.erased SZ.t) ->
  stt U8.t
  (requires exists* v_ctxt .
    pts_to ctxt v_ctxt **
    I.pts_to sl contents_sl v_sl ** // necessary for actions and the error handler
    pts_to pos v_pos **
    extra_state extra **
    pure (SZ.v v_pos <= Seq.length v_sl)
  )
  (ensures fun res -> exists* v_ctxt' extra' v_pos' .
    pts_to ctxt v_ctxt' **
    I.pts_to sl contents_sl v_sl **
    pts_to pos v_pos' **
    extra_state extra' **
    pure (
      SZ.v v_pos <= Seq.length v_sl /\ (
      let pp = LP.parse p (Seq.slice v_sl (SZ.v v_pos) (Seq.length v_sl)) in
      (res == action_failed ==> has_action) /\
      (not has_action ==> extra' == Ghost.reveal extra) /\
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


(*

noextract
inline_for_extraction
let action_bind
      (name: string)
      (#extra_state_value: Type0)
      (#extra_state: extra_state_value -> slprop)
      (#use_error_handler:bool)
      (f: action extra_state use_error_handler)
      (#invg:slice_inv) #disjg (#lg:eloc) #bg #rtg
      (#b:Type) (g: (a -> action invg disjg lg bg rtg b use_error_handler))
= admit ()

noextract
inline_for_extraction
let action_seq
      (#invf:slice_inv) #disjf (#lf:eloc)
      #bf #rtf (#a:Type)
      (#use_error_handler:bool)
      (f: action invf disjf lf bf rtf a use_error_handler)
      (#invg:slice_inv) #disjg (#lg:eloc) #bg #rtg
      (#b:Type) (g: action invg disjg lg bg rtg b use_error_handler)
= fun ctxt error_handler_fn input input_length pos posf ->
    let h0 = HST.get () in
    let _ = f ctxt error_handler_fn input input_length pos posf in
    let h1 = HST.get () in
    modifies_address_liveness_insensitive_unused_in h0 h1;
    g ctxt error_handler_fn input input_length pos posf

noextract
inline_for_extraction
let action_ite
      (#invf:slice_inv) #disjf (#lf:eloc)
      (guard:bool)
      #bf #rtf (#a:Type)
      (#use_error_handler:bool)
      (then_: squash guard -> action invf disjf lf bf rtf a use_error_handler)
      (#invg:slice_inv) #disjg (#lg:eloc) #bg #rtg
      (else_: squash (not guard) -> action invg disjg lg bg rtg a use_error_handler)
= fun ctxt error_handler_fn input input_length pos posf ->
    if guard 
    then then_ () ctxt error_handler_fn input input_length pos posf
    else else_ () ctxt error_handler_fn input input_length pos posf

noextract
inline_for_extraction
let action_abort #use_error_handler
= fun _ _ _ _ _ _ -> false

noextract
inline_for_extraction
let action_field_pos_64 #use_error_handler
= fun _ _ _ _ pos _ -> pos

(* FIXME: this is now unsound in general (only valid for flat buffer)
noextract
inline_for_extraction
let action_field_ptr
      #nz #wk (#k:parser_kind nz wk) (#t:Type) (#p:parser k t) (u:unit)
   : action p true_inv eloc_none true LPL.puint8
   = fun input startPosition _ ->
       let open LowParse.Slice in
       LPL.offset input (LPL.uint64_to_uint32 startPosition)
*)
module T = FStar.Tactics
let ptr_inv_elim (x:B.pointer 'a)
: Lemma
  (ensures forall h. ptr_inv x h ==> B.live h x)
= introduce forall h. ptr_inv x h ==> B.live h x
       with assert (ptr_inv x h ==> B.live h x)
                by (T.norm [delta])

noextract
inline_for_extraction
let action_deref
      (#a:_) (x:B.pointer a) #use_error_handler
= fun _ _ _ _ _ _ -> 
    ptr_inv_elim x;
    !*x

noextract
inline_for_extraction
let action_assignment
      (#a:_) (x:B.pointer a) (v:a) #use_error_handler
= fun _ _ _ _ _ _ ->
    ptr_inv_elim x;
    x *= v

noextract
inline_for_extraction
let action_weaken #inv #disj #l #b #a #use_error_handler act #inv' #disj' #l' = act

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