module EverParse3d.Actions.Base
#lang-pulse
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
module U64 = FStar.UInt64
module P = EverParse3d.Prelude
module SZ = FStar.SizeT
open EverParse3d.State
module LP = LowParse.Spec.Base
module FLD = LowParse.Spec.FLData
module LPL = LowParse.Spec.List
module LPP = LowParse.PulseParse.Base
module LUT = LowParse.Spec.ListUpTo

let is_range_okay = EverParse3d.ErrorCode.is_range_okay

(* The type of non-null byte pointers manipulated by `field_ptr`-style
   actions. The 3D frontend emits this name unqualified. *)
let ___PUINT8 : Type0 = Pulse.Lib.ArrayPtr.ptr FStar.UInt8.t

val action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (extra_state: state_dict)
  (a: Type0)
  (use_error_handler: bool)
: Type0

inline_for_extraction noextract
val validate_with_action_read
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
: Type0

inline_for_extraction noextract
val validate_with_action_no_read
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
: Type0


(* The `allow_reading` index of the Low* validators: `allow_reading = true`
   means that the validator does not consume the input stream, so that a leaf
   reader can subsequently read the value it validated. *)
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
     (allow_reading:bool)
     (use_error_handler:bool)
: Type0
= if allow_reading
  then validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler
  else validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_eta
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

inline_for_extraction noextract
val act_with_comment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (s: string)
      (extra_state: state_dict)
      (#use_error_handler:bool)
      (#res:Type)
      (a: action #base_t #len_t #pos_t extra_state res use_error_handler)
: action #base_t #len_t #pos_t extra_state res use_error_handler

inline_for_extraction
val leaf_reader
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#nz:bool)
  (#k: parser_kind nz WeakKindStrongPrefix)
  (#t: Type)
  (p: parser k t)
: Tot Type0

inline_for_extraction noextract
val validate_with_success_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_read #base_t #len_t #pos_t p1 extra has_action use_error_handler)
      (a:action #base_t #len_t #pos_t extra bool use_error_handler)
  : validate_with_action_read #base_t #len_t #pos_t p1 extra true use_error_handler

inline_for_extraction noextract
val validate_with_error_handler
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
      (typename: string)
      (fieldname: string)
      (#nz: _)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1: Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action: _)
      (#use_error_handler:bool)
      (v1:validate_with_action_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler)
  : validate_with_action_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_ret
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
  : validate_with_action_read #base_t #len_t #pos_t (parse_ret ()) extra_state false use_error_handler

inline_for_extraction noextract
val validate_pair
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (typename: string)
       (name1: string)
       (#nz1:_)
       (#k1:parser_kind nz1 WeakKindStrongPrefix)
       (#t1:Type)
       (#p1:parser k1 t1)
       (k1_const: bool)
       (#extra_state: state_dict)
       (#has_action1:bool)
       (#use_error_handler:bool)
       (v1:validate_with_action_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
       (#nz2:_)
       (#wk2: _)
       (#k2:parser_kind nz2 wk2)
       (#t2:Type)
       (#p2:parser k2 t2)
       (k2_const: bool)
       (#has_action2:bool)
       (v2:validate_with_action_read #base_t #len_t #pos_t p2 extra_state has_action2 use_error_handler)
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p1 `parse_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair_with_refinement_and_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (f: t1 -> bool)
      (a:t1 -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:refine _ f -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_read
      #base_t #len_t #pos_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler

inline_for_extraction noextract
val validate_filter
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (r:leaf_reader #base_t #len_t #pos_t p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
  : validate_with_action_read #base_t #len_t #pos_t (p `parse_filter` f) extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_filter_with_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (r:leaf_reader #base_t #len_t #pos_t p)
       (f:t -> bool)
       (cr:string)
       (cf:string)
       (a: t -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p `parse_filter` f)
      extra_state
      true
      use_error_handler

inline_for_extraction noextract
val validate_weaken_left
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_read #base_t #len_t #pos_t (parse_weaken_left p k') extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_weaken_right
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_read #base_t #len_t #pos_t (parse_weaken_right p k') extra_state has_action use_error_handler

noextract
inline_for_extraction
val validate_weaken
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#d1: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_read #base_t #len_t #pos_t p d1 has_action use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_read #base_t #len_t #pos_t p d2 has_action use_error_handler

noextract
inline_for_extraction
val validate_call
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#d': state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_read #base_t #len_t #pos_t p d' has_action use_error_handler)
      (d: state_dict)
      (#f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      (sq: squash (state_dict_rename_prop d d' f g))
: validate_with_action_read #base_t #len_t #pos_t p d has_action use_error_handler

inline_for_extraction noextract
val validate_impos
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#extra_state: _)
       (#use_error_handler:bool)
       (_:unit)
  : validate_with_action_read #base_t #len_t #pos_t (parse_impos ()) extra_state false use_error_handler

noextract inline_for_extraction
val validate_ite
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#wk: _)
       (#k:parser_kind nz wk)
       (e:bool)
       (#a:squash e -> Type)
       (#b:squash (not e) -> Type)
       (#extra_state: _)
       (#ha1:_)
       (#ha2:_)
       (#use_error_handler:bool)
       (p1:squash e -> parser k (a()))
       (v1:(squash e -> validate_with_action_read #base_t #len_t #pos_t (p1()) extra_state ha1 use_error_handler))
       (p2:squash (not e) -> parser k (b()))
       (v2:(squash (not e) -> validate_with_action_read #base_t #len_t #pos_t (p2()) extra_state ha2 use_error_handler))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (parse_ite e p1 p2)
      extra_state
      (ha1 || ha2)
      use_error_handler

noextract inline_for_extraction
val validate_nlist
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (n:U32.t)
       (n_is_const:option nat { memoizes_n_as_const n_is_const n})
       (#wk: _)
       (#k:parser_kind true wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: _)
       (#ha:bool)
       (#use_error_handler:bool)
       (v: validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t (parse_nlist n n_is_const p) extra_state ha use_error_handler

noextract inline_for_extraction
val validate_t_at_most
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
  : validate_with_action_read #base_t #len_t #pos_t (parse_t_at_most n p) extra_state ha use_error_handler

noextract inline_for_extraction
val validate_t_exact
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
  : validate_with_action_read #base_t #len_t #pos_t (parse_t_exact n p) extra_state ha use_error_handler

inline_for_extraction noextract
val read_filter
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#nz:_)
       (#k: parser_kind nz WeakKindStrongPrefix)
       (#t: Type0)
       (#p: parser k t)
       (p32: leaf_reader #base_t #len_t #pos_t p)
       (f: (t -> bool))
    : leaf_reader #base_t #len_t #pos_t (parse_filter p f)

inline_for_extraction noextract
val read_impos
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
    ()
    : leaf_reader #base_t #len_t #pos_t (parse_impos())

noextract
inline_for_extraction
val action_bind
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #base_t #len_t #pos_t extra_state a use_error_handler)
      (#b:Type) (g: (a -> action #base_t #len_t #pos_t extra_state b use_error_handler))
: action #base_t #len_t #pos_t extra_state b use_error_handler

noextract
inline_for_extraction
val action_weaken
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #base_t #len_t #pos_t d1 a use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: action #base_t #len_t #pos_t d2 a use_error_handler

noextract
inline_for_extraction
val action_call
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d': state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (act: action #base_t #len_t #pos_t d' a use_error_handler)
      (d: state_dict)
      (#f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      (sq: squash (state_dict_rename_prop d d' f g))
: action #base_t #len_t #pos_t d a use_error_handler

noextract
inline_for_extraction
val action_deref
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: Ghost.erased string)
      (#a:Type0) (x:ref a) (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler

noextract
inline_for_extraction
val action_assignment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: Ghost.erased string)
      (#a:Type) (x:ref a) (w: a) (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) unit use_error_handler

noextract
inline_for_extraction
val action_return
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (x: a)
: action #base_t #len_t #pos_t extra_state a use_error_handler

noextract
inline_for_extraction
val action_return_true
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler

noextract
inline_for_extraction
val action_abort
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler

noextract
inline_for_extraction
val action_seq
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (f: action #base_t #len_t #pos_t extra_state a use_error_handler)
      (#b: Type)
      (g: action #base_t #len_t #pos_t extra_state b use_error_handler)
: action #base_t #len_t #pos_t extra_state b use_error_handler

noextract
inline_for_extraction
val action_ite
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (guard: bool)
      (then_: (squash (guard == true) -> action #base_t #len_t #pos_t extra_state a use_error_handler))
      (else_: (squash (guard == false) -> action #base_t #len_t #pos_t extra_state a use_error_handler))
: action #base_t #len_t #pos_t extra_state a use_error_handler

inline_for_extraction noextract
val validate_with_comment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (c: string)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_unit
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t parse_unit extra_state false use_error_handler

inline_for_extraction noextract
val validate_unit_refinement
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (f: unit -> bool)
      (cf: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t (parse_filter parse_unit f) extra_state false use_error_handler

inline_for_extraction noextract
val validate_dep_pair
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:t1 -> Type)
      (#p2:(x:t1 -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:t1 -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p1 `parse_dep_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair_with_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (a:t1 -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:t1 -> Type)
      (#p2:(x:t1 -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:t1 -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p1 `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler

inline_for_extraction noextract
val validate_dep_pair_with_refinement
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (f: t1 -> bool)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (v2:(x:refine _ f -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler))
  : validate_with_action_read
      #base_t #len_t #pos_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler

inline_for_extraction noextract
val validate_with_dep_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#nz:_)
      (#k:parser_kind nz WeakKindStrongPrefix)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
      (r:leaf_reader #base_t #len_t #pos_t p)
      (a: t -> action #base_t #len_t #pos_t extra_state bool use_error_handler)
  : validate_with_action_read #base_t #len_t #pos_t p extra_state true use_error_handler

inline_for_extraction noextract
val validate____UINT8
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT8 extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT8
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT8

inline_for_extraction noextract
val validate____UINT8BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT8BE extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT8BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT8BE

inline_for_extraction noextract
val validate____UINT16BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT16BE extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT16BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT16BE

inline_for_extraction noextract
val validate____UINT32BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT32BE extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT32BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT32BE

inline_for_extraction noextract
val validate____UINT64BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT64BE extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT64BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT64BE

inline_for_extraction noextract
val validate____UINT16
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT16 extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT16
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT16

inline_for_extraction noextract
val validate____UINT32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT32 extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT32

inline_for_extraction noextract
val validate____UINT64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT64 extra_state false use_error_handler

inline_for_extraction noextract
val read____UINT64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t parse____UINT64

inline_for_extraction noextract
val read_unit
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: leaf_reader #base_t #len_t #pos_t (parse_ret ())

inline_for_extraction noextract
val validate_all_bytes
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t parse_all_bytes extra_state false use_error_handler

inline_for_extraction noextract
val validate_drop
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_without_reading
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

noextract
inline_for_extraction
val action_field_pos_64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state U64.t use_error_handler

noextract
inline_for_extraction
val action_field_pos_32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state U32.t use_error_handler

inline_for_extraction noextract
let field_ptr_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (ptr_t: Type0)
: Type0
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
: Type0
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
val action_field_ptr
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#ptr_t: Type0)
      (f: option (field_ptr_t base_t len_t pos_t ptr_t))
      (sq: squash (Some? f))
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state ptr_t use_error_handler

noextract
inline_for_extraction
val action_field_ptr_after
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#ptr_t: Type0)
      (f: option (field_ptr_after_t base_t len_t pos_t ptr_t))
      (sq: squash (Some? f))
      (name: Ghost.erased string)
      (sz: U64.t)
      (write_to: ref ptr_t)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to write_to #1.0R)) bool use_error_handler

inline_for_extraction noextract
val validate_all_zeros
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t parse_all_zeros extra_state false use_error_handler

inline_for_extraction noextract
val validate_string
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#k: parser_kind true WeakKindStrongPrefix)
      (#t: eqtype)
      (#p: parser k t)
      (#extra_state: state_dict)
      (#ha:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
      (r: leaf_reader #base_t #len_t #pos_t p)
      (terminator: t)
: validate_with_action_read #base_t #len_t #pos_t (parse_string p terminator) extra_state ha use_error_handler

inline_for_extraction noextract
val validate_nlist_constant_size_without_actions
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (n:U32.t)
      (n_is_const:option nat { memoizes_n_as_const n_is_const n})
      (payload_is_constant_size: bool)
      (#wk: _)
      (#k:parser_kind true wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state false use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t (parse_nlist n n_is_const p) extra_state false use_error_handler

inline_for_extraction noextract
let external_action
  (extra_state: state_dict)
  (a: Type0)
: Type0
= unit ->
  stt a
    (exists* extra . forevery_state extra_state extra)
    (fun _ -> exists* extra' . forevery_state extra_state extra')


inline_for_extraction noextract
let field_ptr_after_setter_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (extra_state: state_dict)
  (ptr_t: Type0)
: Type0
= (sz: U64.t) ->
  (write_to: (ptr_t -> external_action extra_state unit)) ->
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      (exists* extra . forevery_state extra_state extra))
    (fun _ -> I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      (exists* extra' . forevery_state extra_state extra'))


inline_for_extraction noextract
let copy_buffer_state
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (c: copy_buffer_t)
  (cv: (Seq.seq U8.t & Seq.seq U8.t))
: slprop
= CP.pts_to #_ #base_t #len_t #pos_t c (fst cv) (snd cv)

inline_for_extraction noextract
let copy_buffer_state_dict
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (name: string)
  (c: copy_buffer_t)
: state_dict
= state_dict_singleton name (copy_buffer_state #_ #base_t #len_t #pos_t c)

noextract
inline_for_extraction
val mk_external_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#a: Type0)
      (f: external_action extra_state a)
      (#use_error_handler: bool)
: action #base_t #len_t #pos_t extra_state a use_error_handler

noextract
inline_for_extraction
val action_field_ptr_after_with_setter
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#ptr_t: Type0)
      (f: option (field_ptr_after_setter_t base_t len_t pos_t extra_state ptr_t))
      (sq: squash (Some? f))
      (sz: U64.t)
      (write_to: (ptr_t -> external_action extra_state unit))
      (#use_error_handler: bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler

noextract
inline_for_extraction
val probe_then_validate
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#copy_buffer_t: Type0)
  {| cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t  |}
      (error_handler_macro: error_handler #base_t #len_t #pos_t)
      (typename: string)
      (fieldname: string)
      (#nz: bool)
      (#wk: _)
      (#k: parser_kind nz wk)
      (#t: Type0)
      (#p: parser k t)
      (#extra_state: state_dict)
      (#ha: bool)
      (#use_error_handler: bool)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler)
      (#ptr_t: Type0)
      (src: ptr_t)
      (as_u64: (ptr_t -> PA.pure_external_action U64.t))
      (nullable: bool)
      (dest_name: Ghost.erased string)
      (dest: copy_buffer_t)
      (init: PA.init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t)
      (prep_dest_sz: U64.t)
      (#mz: bool)
      (probe: PA.probe_m #_ #_ #_ #_ #inst #cb_inst unit true mz use_error_handler)
      (sq: squash (forall x .
        ~ (extra_state.state_p x /\
           (copy_buffer_state_dict #_ #base_t #len_t #pos_t dest_name dest).state_p x)))
: action #base_t #len_t #pos_t
    (state_dict_prod extra_state (copy_buffer_state_dict #_ #base_t #len_t #pos_t dest_name dest))
    bool
    use_error_handler

inline_for_extraction noextract
val validate_impos_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#extra_state: _)
       (#use_error_handler:bool)
       (_:unit)
: validate_with_action_no_read #base_t #len_t #pos_t (parse_impos ()) extra_state false use_error_handler

inline_for_extraction noextract
val validate_eta_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_with_comment_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (c: string)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler

inline_for_extraction noextract
val validate_with_error_handler_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
      (typename: string)
      (fieldname: string)
      (#nz: _)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1: Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action: _)
      (#use_error_handler:bool)
      (v1: validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler)
: validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler

(* Versions polymorphic in `allow_reading`, for the interpreter. The `match ...
   returns` makes the choice reduce definitionally, so no SMT reasoning about
   type equality is involved. *)

inline_for_extraction noextract
let validate_eta_gen
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (allow_reading:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler
= match allow_reading
  returns validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler
  with
  | true -> validate_eta_no_read #base_t #len_t #pos_t v
  | false -> validate_eta #base_t #len_t #pos_t v

inline_for_extraction noextract
let validate_with_comment_gen
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (c: string)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (allow_reading:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler
= match allow_reading
  returns validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler
  with
  | true -> validate_with_comment_no_read #base_t #len_t #pos_t c v
  | false -> validate_with_comment #base_t #len_t #pos_t c v

inline_for_extraction noextract
let validate_with_error_handler_gen
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
      (typename: string)
      (fieldname: string)
      (#nz: _)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1: Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action: _)
      (allow_reading: bool)
      (#use_error_handler:bool)
      (v1: validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action allow_reading use_error_handler)
: validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action allow_reading use_error_handler
= match allow_reading
  returns validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action allow_reading use_error_handler
  with
  | true -> validate_with_error_handler_no_read #base_t #len_t #pos_t error_handler_macro typename fieldname v1
  | false -> validate_with_error_handler #base_t #len_t #pos_t error_handler_macro typename fieldname v1

inline_for_extraction noextract
let validate_without_reading_gen
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (allow_reading:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler
= match allow_reading
  returns (validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler)
  with
  | true -> validate_without_reading #base_t #len_t #pos_t v
  | false -> v

inline_for_extraction noextract
val validate_unit_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse_unit extra_state false use_error_handler

noextract
inline_for_extraction
val validate_weaken_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (name: string)
       (#nz:_)
       (#wk:_)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#d1: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p d1 has_action use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_no_read #base_t #len_t #pos_t p d2 has_action use_error_handler

inline_for_extraction noextract
let validate_weaken_gen
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#d1: state_dict)
      (#has_action:bool)
      (allow_reading:bool)
      (#use_error_handler:bool)
      (v: validate_with_action_t #base_t #len_t #pos_t p d1 has_action allow_reading use_error_handler)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_t #base_t #len_t #pos_t p d2 has_action allow_reading use_error_handler
= match allow_reading
  returns (validate_with_action_t #base_t #len_t #pos_t p d2 has_action allow_reading use_error_handler)
  with
  | true -> validate_weaken_no_read #base_t #len_t #pos_t name v d2 d2_extends
  | false -> validate_weaken #base_t #len_t #pos_t name v d2 d2_extends
