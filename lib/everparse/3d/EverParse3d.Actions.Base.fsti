module EverParse3d.Actions.Base
#lang-pulse
open EverParse3d.ErrorCode
open EverParse3d.Prelude
open Pulse.Lib.Pervasives
module I = EverParse3d.InputStream.Base
module PM = EverParse3d.PtrModel
module CP = EverParse3d.CopyBuffer
module PA = EverParse3d.ProbeActions
module Bool = EverParse3d.Boolean
module AppCtxt = EverParse3d.AppCtxt
open FStar.FunctionalExtensionality
open EverParse3d.Actions.Common
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module P = EverParse3d.Prelude
module SZ = FStar.SizeT
open EverParse3d.State
module S = EverParse3d.Actions.Spec
module LP = LowParse.Spec.Base
module FLD = LowParse.Spec.FLData
module LPL = LowParse.Spec.List
module LPP = LowParse.PulseParse.Base
module LUT = LowParse.Spec.ListUpTo

(* Inline this forwarding alias at its call sites rather than exposing a
   separate runtime global for the function reference. *)
inline_for_extraction
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
  (sp: S.action_spec extra_state a)
: Type0

(* A validating action: a boolean action whose failure makes validation fail
   (e.g. a probe), so that its final action state need not be specified on
   failure. *)
inline_for_extraction noextract
val vaction
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (extra_state: state_dict)
  (use_error_handler: bool)
  (sp: S.vaction_spec extra_state)
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
     (s: S.vspec extra_state)
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
     (s: S.vspec extra_state)
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
     (s: S.vspec extra_state)
: Type0
= if allow_reading
  then validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s
  else validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

inline_for_extraction noextract
val act_with_comment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (s: string)
      (extra_state: state_dict)
      (#use_error_handler:bool)
      (#res:Type)
      (#[@@@erasable] sp: S.action_spec extra_state res)
      (a: action #base_t #len_t #pos_t extra_state res use_error_handler sp)
: action #base_t #len_t #pos_t extra_state res use_error_handler sp

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
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (name: string)
      (#nz:bool)
      (#wk: _)
      (#k1:parser_kind nz wk)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s1: S.vspec extra)
      (v1:validate_with_action_read #base_t #len_t #pos_t p1 extra has_action use_error_handler s1)
      (#[@@@erasable] sa: S.action_spec extra bool)
      (a:action #base_t #len_t #pos_t extra bool use_error_handler sa)
  : validate_with_action_read #base_t #len_t #pos_t p1 extra true use_error_handler (S.vspec_with_success_action p1 s1 sa)

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v1:validate_with_action_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler s)
  : validate_with_action_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler s

inline_for_extraction noextract
val validate_ret
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
  : validate_with_action_read #base_t #len_t #pos_t (parse_ret ()) extra_state false use_error_handler (S.vspec_of_parser (parse_ret ()))


inline_for_extraction noextract
val validate_dep_pair_with_refinement_and_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (p1_is_constant_size_without_actions: bool)
      (name1: string)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s1: S.vspec extra_state)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler s1)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (f: t1 -> bool)
      (err: t1 -> constraint_error_code)
      (#[@@@erasable] sa: t1 -> S.action_spec extra_state bool)
      (a:(x: t1 -> action #base_t #len_t #pos_t extra_state bool use_error_handler (sa x)))
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (#[@@@erasable] s2: refine _ f -> S.vspec extra_state)
      (v2:(x:refine _ f -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler (s2 x)))
  : validate_with_action_read
      #base_t #len_t #pos_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler
      (S.vspec_dep_pair_with_refinement_gen p1_is_constant_size_without_actions p1 s1 f (Some sa) s2)

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
       (#[@@@erasable] s: S.vspec extra_state)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
       (r:leaf_reader #base_t #len_t #pos_t p)
       (f:t -> bool)
       (err: t -> constraint_error_code)
       (cr:string)
       (cf:string)
  : validate_with_action_read #base_t #len_t #pos_t (p `parse_filter` f) extra_state has_action use_error_handler (S.vspec_filter p s f None)

inline_for_extraction noextract
val validate_filter_with_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
       (name: string)
       (#nz:_)
       (#k:parser_kind nz WeakKindStrongPrefix)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: state_dict)
       (#has_action:_)
       (#use_error_handler:bool)
       (#[@@@erasable] s: S.vspec extra_state)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
       (r:leaf_reader #base_t #len_t #pos_t p)
       (f:t -> bool)
       (err: t -> constraint_error_code)
       (cr:string)
       (cf:string)
       (#[@@@erasable] sa: t -> S.action_spec extra_state bool)
       (a: (x: t -> action #base_t #len_t #pos_t extra_state bool use_error_handler (sa x)))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p `parse_filter` f)
      extra_state
      true
      use_error_handler
      (S.vspec_filter p s f (Some sa))

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
       (#[@@@erasable] s: S.vspec extra_state)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_read #base_t #len_t #pos_t (parse_weaken_left p k') extra_state has_action use_error_handler s

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
       (#[@@@erasable] s: S.vspec extra_state)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
       (#nz':_)
       (#wk': _)
       (k':parser_kind nz' wk')
  : validate_with_action_read #base_t #len_t #pos_t (parse_weaken_right p k') extra_state has_action use_error_handler s

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
       (#[@@@erasable] s: S.vspec d1)
       (v:validate_with_action_read #base_t #len_t #pos_t p d1 has_action use_error_handler s)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_read #base_t #len_t #pos_t p d2 has_action use_error_handler (S.vspec_weaken s d2 d2_extends)

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
       (#[@@@erasable] s: S.vspec d')
       (v:validate_with_action_read #base_t #len_t #pos_t p d' has_action use_error_handler s)
      (d: state_dict)
      (#f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      (sq: squash (state_dict_rename_prop d d' f g))
: validate_with_action_read #base_t #len_t #pos_t p d has_action use_error_handler (S.vspec_call s d f g sq)

inline_for_extraction noextract
val validate_impos
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#extra_state: _)
       (#use_error_handler:bool)
       (_:unit)
  : validate_with_action_read #base_t #len_t #pos_t (parse_impos ()) extra_state false use_error_handler (S.vspec_of_parser (parse_impos ()))

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
       (#[@@@erasable] s1: squash e -> S.vspec extra_state)
       (#[@@@erasable] s2: squash (not e) -> S.vspec extra_state)
       (p1:squash e -> parser k (a()))
       (v1:(x_: squash e -> validate_with_action_read #base_t #len_t #pos_t (p1()) extra_state ha1 use_error_handler (s1 x_)))
       (p2:squash (not e) -> parser k (b()))
       (v2:(x_: squash (not e) -> validate_with_action_read #base_t #len_t #pos_t (p2()) extra_state ha2 use_error_handler (s2 x_)))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (parse_ite e p1 p2)
      extra_state
      (ha1 || ha2)
      use_error_handler
      (S.vspec_ite e s1 s2)

noextract inline_for_extraction
val validate_nlist
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
       (n:U32.t)
       (n_is_const:option nat { memoizes_n_as_const n_is_const n})
       (#wk: _)
       (#k:parser_kind true wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: _)
       (#ha:bool)
       (#use_error_handler:bool)
       (#[@@@erasable] s: S.vspec extra_state)
       (v: validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t (parse_nlist n n_is_const p) extra_state ha use_error_handler (S.vspec_nlist ha n n_is_const p s)

noextract inline_for_extraction
val validate_t_at_most
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (#[@@@erasable] s: S.vspec extra_state)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler s)
  : validate_with_action_read #base_t #len_t #pos_t (parse_t_at_most n p) extra_state ha use_error_handler (S.vspec_t_at_most n s)

noextract inline_for_extraction
val validate_t_exact
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
       (n:U32.t)
       (#nz: _)
       (#wk: _)
       (#k:parser_kind nz wk)
       (#t:Type)
       (#p:parser k t)
       (#extra_state: _)
       (#ha:_)
       (#use_error_handler:bool)
       (#[@@@erasable] s: S.vspec extra_state)
       (v:validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler s)
  : validate_with_action_read #base_t #len_t #pos_t (parse_t_exact n p) extra_state ha use_error_handler (S.vspec_t_exact n p s)

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
      (#[@@@erasable] sf: S.action_spec extra_state a)
      (f: action #base_t #len_t #pos_t extra_state a use_error_handler sf)
      (#b:Type)
      (#[@@@erasable] sg: a -> S.action_spec extra_state b)
      (g: (x: a -> action #base_t #len_t #pos_t extra_state b use_error_handler (sg x)))
: action #base_t #len_t #pos_t extra_state b use_error_handler (S.aspec_bind sf sg)

noextract
inline_for_extraction
val action_weaken
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (#[@@@erasable] sf: S.action_spec d1 a)
      (f: action #base_t #len_t #pos_t d1 a use_error_handler sf)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: action #base_t #len_t #pos_t d2 a use_error_handler (S.aspec_weaken sf d2 d2_extends)

noextract
inline_for_extraction
val vaction_weaken
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d1: state_dict)
      (#use_error_handler:bool)
      (#[@@@erasable] sf: S.vaction_spec d1)
      (f: vaction #base_t #len_t #pos_t d1 use_error_handler sf)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: vaction #base_t #len_t #pos_t d2 use_error_handler (S.vaspec_weaken sf d2 d2_extends)

noextract
inline_for_extraction
val action_call
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#d': state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (#[@@@erasable] sf: S.action_spec d' a)
      (act: action #base_t #len_t #pos_t d' a use_error_handler sf)
      (d: state_dict)
      (#f: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p)))) // TODO: change to GTot once we switch to ghost bijections
      (#g: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
      (sq: squash (state_dict_rename_prop d d' f g))
: action #base_t #len_t #pos_t d a use_error_handler (S.aspec_call sf d f g sq)

noextract
inline_for_extraction
val action_deref
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: Ghost.erased string)
      (#a:Type0) (x:ref a) (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) a use_error_handler (S.aspec_deref name (pts_to x #1.0R))

noextract
inline_for_extraction
val action_assignment
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (name: Ghost.erased string)
      (#a:Type) (x:ref a) (w: a) (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) unit use_error_handler (S.aspec_assignment name (pts_to x #1.0R) w)

noextract
inline_for_extraction
val action_deref_map
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t |}
  (#a #b: Type0)
  (decode: a -> Tot b)
  (name: Ghost.erased string)
  (x: ref a)
  (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name (pts_to x #1.0R)) b use_error_handler (S.aspec_deref_map decode name (pts_to x #1.0R))

noextract
inline_for_extraction
val action_return
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (x: a)
: action #base_t #len_t #pos_t extra_state a use_error_handler (S.aspec_return x)

noextract
inline_for_extraction
val action_return_true
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler (S.aspec_return true)

noextract
inline_for_extraction
val action_abort
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state bool use_error_handler (S.aspec_return false)

noextract
inline_for_extraction
val action_seq
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (#[@@@erasable] sf: S.action_spec extra_state a)
      (f: action #base_t #len_t #pos_t extra_state a use_error_handler sf)
      (#b: Type)
      (#[@@@erasable] sg: S.action_spec extra_state b)
      (g: action #base_t #len_t #pos_t extra_state b use_error_handler sg)
: action #base_t #len_t #pos_t extra_state b use_error_handler (S.aspec_seq sf sg)

noextract
inline_for_extraction
val action_ite
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#a: Type)
      (guard: bool)
      (#[@@@erasable] st: squash (guard == true) -> S.action_spec extra_state a)
      (then_: (sq: squash (guard == true) -> action #base_t #len_t #pos_t extra_state a use_error_handler (st sq)))
      (#[@@@erasable] se: squash (guard == false) -> S.action_spec extra_state a)
      (else_: (sq: squash (guard == false) -> action #base_t #len_t #pos_t extra_state a use_error_handler (se sq)))
: action #base_t #len_t #pos_t extra_state a use_error_handler (S.aspec_ite guard st se)

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

inline_for_extraction noextract
val validate_unit
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t parse_unit extra_state false use_error_handler (S.vspec_of_parser parse_unit)

inline_for_extraction noextract
val validate_unit_refinement
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (f: unit -> bool)
      (cf: string)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t (parse_filter parse_unit f) extra_state false use_error_handler (S.vspec_of_parser (parse_filter parse_unit f))

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
      (#[@@@erasable] s1: S.vspec extra_state)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler s1)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:t1 -> Type)
      (#p2:(x:t1 -> parser k2 (t2 x)))
      (#has_action2:bool)
      (#[@@@erasable] s2: t1 -> S.vspec extra_state)
      (v2:(x:t1 -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler (s2 x)))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p1 `parse_dep_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
      (S.vspec_dep_pair p1 s1 s2)

inline_for_extraction noextract
val validate_dep_pair_with_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#nz1:_)
      (#k1:parser_kind nz1 WeakKindStrongPrefix)
      (#t1:Type)
      (#p1:parser k1 t1)
      (#extra_state: state_dict)
      (#has_action1:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s1: S.vspec extra_state)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler s1)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (#[@@@erasable] sa: t1 -> S.action_spec extra_state bool)
      (a:(x: t1 -> action #base_t #len_t #pos_t extra_state bool use_error_handler (sa x)))
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:t1 -> Type)
      (#p2:(x:t1 -> parser k2 (t2 x)))
      (#has_action2:bool)
      (#[@@@erasable] s2: t1 -> S.vspec extra_state)
      (v2:(x:t1 -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler (s2 x)))
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p1 `parse_dep_pair` p2)
      extra_state
      true
      use_error_handler
      (S.vspec_dep_pair_with_action p1 s1 sa s2)

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
      (#[@@@erasable] s1: S.vspec extra_state)
      (v1:validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler s1)
      (r1: leaf_reader #base_t #len_t #pos_t p1)
      (f: t1 -> bool)
      (err: t1 -> constraint_error_code)
      (#nz2:_)
      (#wk2: _)
      (#k2:parser_kind nz2 wk2)
      (#t2:refine _ f -> Type)
      (#p2:(x:refine _ f -> parser k2 (t2 x)))
      (#has_action2:bool)
      (#[@@@erasable] s2: refine _ f -> S.vspec extra_state)
      (v2:(x:refine _ f -> validate_with_action_read #base_t #len_t #pos_t (p2 x) extra_state has_action2 use_error_handler (s2 x)))
  : validate_with_action_read
      #base_t #len_t #pos_t
      ((p1 `parse_filter` f) `parse_dep_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
      (S.vspec_dep_pair_with_refinement_gen p1_is_constant_size_without_actions p1 s1 f None s2)

inline_for_extraction noextract
val validate_with_dep_action
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (name: string)
      (#nz:_)
      (#k:parser_kind nz WeakKindStrongPrefix)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s: S.vspec extra_state)
      (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
      (r:leaf_reader #base_t #len_t #pos_t p)
      (#[@@@erasable] sa: t -> S.action_spec extra_state bool)
      (a: (x: t -> action #base_t #len_t #pos_t extra_state bool use_error_handler (sa x)))
  : validate_with_action_read #base_t #len_t #pos_t p extra_state true use_error_handler (S.vspec_with_dep_action p s sa)

inline_for_extraction noextract
val validate_with_dep_vaction
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (name: string)
      (#nz:_)
      (#k:parser_kind nz WeakKindStrongPrefix)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s: S.vspec extra_state)
      (v:validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
      (r:leaf_reader #base_t #len_t #pos_t p)
      (#[@@@erasable] sa: t -> S.vaction_spec extra_state)
      (a: (x: t -> vaction #base_t #len_t #pos_t extra_state use_error_handler (sa x)))
  : validate_with_action_read #base_t #len_t #pos_t p extra_state true use_error_handler (S.vspec_with_dep_vaction p s sa)

inline_for_extraction noextract
val validate____UINT8
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT8 extra_state false use_error_handler (S.vspec_of_parser parse____UINT8)

inline_for_extraction noextract
val read____UINT8
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT8

inline_for_extraction noextract
val validate____UINT8BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT8BE extra_state false use_error_handler (S.vspec_of_parser parse____UINT8BE)

inline_for_extraction noextract
val read____UINT8BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT8BE

inline_for_extraction noextract
val validate____UINT16BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT16BE extra_state false use_error_handler (S.vspec_of_parser parse____UINT16BE)

inline_for_extraction noextract
val read____UINT16BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT16BE

inline_for_extraction noextract
val validate____UINT32BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT32BE extra_state false use_error_handler (S.vspec_of_parser parse____UINT32BE)

inline_for_extraction noextract
val read____UINT32BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT32BE

inline_for_extraction noextract
val validate____UINT64BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT64BE extra_state false use_error_handler (S.vspec_of_parser parse____UINT64BE)

inline_for_extraction noextract
val read____UINT64BE
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT64BE

inline_for_extraction noextract
val validate____UINT16
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT16 extra_state false use_error_handler (S.vspec_of_parser parse____UINT16)

inline_for_extraction noextract
val read____UINT16
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT16

inline_for_extraction noextract
val validate____UINT32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT32 extra_state false use_error_handler (S.vspec_of_parser parse____UINT32)

inline_for_extraction noextract
val read____UINT32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
: leaf_reader #base_t #len_t #pos_t parse____UINT32

inline_for_extraction noextract
val validate____UINT64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (name: string)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse____UINT64 extra_state false use_error_handler (S.vspec_of_parser parse____UINT64)

inline_for_extraction noextract
val read____UINT64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
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
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t parse_all_bytes extra_state false use_error_handler (S.vspec_of_parser parse_all_bytes)

inline_for_extraction noextract
val validate_drop
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

inline_for_extraction noextract
val validate_pair
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (error_handler_macro: error_handler #base_t #len_t #pos_t)
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
       (#[@@@erasable] s1: S.vspec extra_state)
       (v1:validate_with_action_read #base_t #len_t #pos_t p1 extra_state has_action1 use_error_handler s1)
       (#nz2:_)
       (#wk2: _)
       (#k2:parser_kind nz2 wk2)
       (#t2:Type)
       (#p2:parser k2 t2)
       (k2_const: bool)
       (#has_action2:bool)
       (#[@@@erasable] s2: S.vspec extra_state)
       (v2:validate_with_action_read #base_t #len_t #pos_t p2 extra_state has_action2 use_error_handler s2)
  : validate_with_action_read
      #base_t #len_t #pos_t
      (p1 `parse_pair` p2)
      extra_state
      (has_action1 || has_action2)
      use_error_handler
      (S.vspec_pair p1 k1_const has_action1 s1 p2 k2_const has_action2 s2)

inline_for_extraction noextract
val validate_without_reading
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

noextract
inline_for_extraction
val action_field_pos_64
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state U64.t use_error_handler S.aspec_field_pos_64

noextract
inline_for_extraction
val action_field_pos_32
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state U32.t use_error_handler S.aspec_field_pos_32

inline_for_extraction noextract
let field_ptr_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: Type0
= (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  (start_pos: U64.t) ->
  stt PM.ptr
    (I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      pure (U64.v start_pos + Seq.length v_sl <= Seq.length contents_sl))
    (fun res -> I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      pure (res == PM.ptr_at (I.origin #base_t #len_t #pos_t sl_base) (U64.v start_pos)))

(* The peep world: a prophecy of the outcomes of all future calls to the
   client-provided primitive behind `field_ptr_after` (see
   `S.aspec_field_ptr_after`.) Nothing is assumed about that primitive: the
   prophecy is resolved with what it actually did, by `resolve_peep_world`.

   Introducing a fresh peep world is always sound, since the tape is
   arbitrary. Resolving it is sound since `resolve_peep_world` is not ghost:
   its arguments are computationally relevant, so they cannot depend on the
   (ghost) tape; and `peep_world` is not duplicable, so each outcome is
   resolved at most once. *)
val peep_world (w: S.peep_tape) : slprop

val prophesy_peep_world (_: unit)
: stt_ghost (Ghost.erased S.peep_tape) emp_inames emp (fun w -> peep_world w)

inline_for_extraction noextract
val resolve_peep_world
  (ok: bool)
  (r: ref PM.ptr)
  (#v: Ghost.erased PM.ptr)
  (#w: Ghost.erased S.peep_tape)
: stt unit
    (pts_to r #1.0R v ** peep_world w)
    (fun _ -> pts_to r #1.0R v ** peep_world (S.peep_tail w) **
      pure (S.peep_head w == (if ok then Some (Ghost.reveal v) else None)))

inline_for_extraction noextract
val resolve_peep_world_ptr
  (ok: bool)
  (p: PM.ptr)
  (#w: Ghost.erased S.peep_tape)
: stt unit
    (peep_world w)
    (fun _ -> peep_world (S.peep_tail w) **
      pure (S.peep_head w == (if ok then Some p else None)))

(* Resolving with a constant does not depend on the tape, so it can be ghost. *)
val resolve_peep_world_none
  (#w: Ghost.erased S.peep_tape)
  (_: unit)
: stt_ghost unit emp_inames
    (peep_world w)
    (fun _ -> peep_world (S.peep_tail w) ** pure (S.peep_head w == None))

let peep_world_dict : state_dict = state_dict_singleton S.world_key peep_world

inline_for_extraction noextract
let field_ptr_after_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
: Type0
= (* Explicit, not a `solve_from_ctx` implicit: this arrow is *stored* (in the
     `option (field_ptr_after_t ...)` that each backend exports), so the tactic
     would have to run where the binders are not yet in scope. *)
  (_extra: inst.extra_t) ->
  (sz: U64.t) ->
  (write_to: ref PM.ptr) ->
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (w: Ghost.erased PM.ptr) ->
  (pw: Ghost.erased S.peep_tape) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to write_to #1.0R w ** I.pts_to sl_base sl_len sl_pos contents_sl v_sl ** peep_world pw)
    (fun res -> pts_to write_to #1.0R (S.peep_result (S.peep_head pw) w) **
      I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      peep_world (S.peep_tail pw) **
      pure (res == Some? (S.peep_head pw)))

noextract
inline_for_extraction
val action_field_ptr
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (f: field_ptr_t base_t len_t pos_t)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t extra_state PM.ptr use_error_handler S.aspec_field_ptr

noextract
inline_for_extraction
val action_field_ptr_after
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (f: field_ptr_after_t base_t len_t pos_t)
      (name: Ghost.erased string)
      (sz: U64.t)
      (write_to: ref PM.ptr)
      (sq: squash (forall x . ~ ((state_dict_singleton name (pts_to write_to #1.0R)).state_p x /\ peep_world_dict.state_p x)))
      (#use_error_handler:bool)
: action #base_t #len_t #pos_t
    (state_dict_prod (state_dict_singleton name (pts_to write_to #1.0R)) peep_world_dict)
    bool use_error_handler
    (S.aspec_field_ptr_after name (pts_to write_to #1.0R) peep_world sq)

inline_for_extraction noextract
val validate_all_zeros
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
  (#extra_state: state_dict)
  (#use_error_handler:bool)
: validate_with_action_read #base_t #len_t #pos_t parse_all_zeros extra_state false use_error_handler (S.vspec_of_parser parse_all_zeros)

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state ha use_error_handler s)
      (r: leaf_reader #base_t #len_t #pos_t p)
      (terminator: t)
: validate_with_action_read #base_t #len_t #pos_t (parse_string p terminator) extra_state ha use_error_handler (S.vspec_string ha p terminator s)

inline_for_extraction noextract
val validate_nlist_constant_size_without_actions
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (n:U32.t)
      (n_is_const:option nat { memoizes_n_as_const n_is_const n})
      (payload_is_constant_size: bool)
      (#wk: _)
      (#k:parser_kind true wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#use_error_handler:bool)
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state false use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t (parse_nlist n n_is_const p) extra_state false use_error_handler (S.vspec_nlist false n n_is_const p s)

(* The probe world: a prophecy of the outcomes of all future probes (see
   `S.vaspec_probe_then_validate`). It absorbs everything a probe depends on
   but that is not modeled (the contents of the probed memory, concurrent
   modifications, allocation failures in the client's probe functions.)

   Soundness relies on `probe_world` being non-duplicable, and on each outcome
   being resolved (in `probe_then_validate`) at most once, with values
   determined by the actual run of the probe, which cannot depend on the tape
   since the tape is ghost. A fresh world can always be introduced, so
   theorems about validators hold for every initial tape. *)
val probe_world (w: S.probe_tape) : slprop

val prophesy_probe_world (_: unit)
: stt_ghost (Ghost.erased S.probe_tape) emp_inames emp (fun w -> probe_world w)

(* The state of a copy buffer, as seen by the actions: its contents are only
   relevant within a probe, so only its probe world is exposed. *)
inline_for_extraction noextract
let copy_buffer_state
  (#copy_buffer_t: Type0)
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  {| cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (c: copy_buffer_t)
  (w: S.probe_tape)
: slprop
= (exists* contents v . CP.pts_to #_ #base_t #len_t #pos_t c contents v) ** probe_world w

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

(* An external action (written in C) with a functional specification: `spec`
   is uninterpreted and lawless (typically an abstract `val` generated in the
   ExternalAPI module), so this type does not constrain the C code beyond
   footprint: `vt` and `spec` can always be realized by a prophecy of all the
   outcomes of the C function, provided `state` is not duplicable. *)
inline_for_extraction noextract
let external_action_spec
  (#vt: Type0)
  (name: string)
  (state: vt -> slprop)
  (a: Type0)
  (spec: vt -> Tot (a & vt))
: Type0
= unit ->
  (#w: Ghost.erased vt) ->
  stt a
    (state w)
    (fun res -> state (snd (spec w)) ** pure (res == fst (spec w)))

inline_for_extraction noextract
let field_ptr_after_setter_t
  (base_t len_t pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#vt: Type0)
  (name: string)
  (state: vt -> slprop)
  (sp: PM.ptr -> vt -> Tot (unit & vt))
: Type0
= (* Explicit for the same reason as `field_ptr_after_t`: this arrow is stored,
     so `solve_from_ctx` cannot run with the binders in scope. *)
  (_extra: inst.extra_t) ->
  (sz: U64.t) ->
  (write_to: (p: PM.ptr -> external_action_spec name state unit (sp p))) ->
  (sl_base: base_t) ->
  (sl_len: len_t) ->
  (sl_pos: pos_t) ->
  (pw: Ghost.erased S.peep_tape) ->
  (w: Ghost.erased vt) ->
  (contents_sl: Ghost.erased (Seq.seq U8.t)) ->
  (v_sl: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      state w **
      peep_world pw)
    (fun res -> I.pts_to sl_base sl_len sl_pos contents_sl v_sl **
      state (S.setter_peep_result sp (S.peep_head pw) w) **
      peep_world (S.peep_tail pw) **
      pure (res == Some? (S.peep_head pw)))

noextract
inline_for_extraction
val mk_external_action_spec
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#vt: Type0)
      (#name: string)
      (#state: vt -> slprop)
      (#a: Type0)
      (#spec: vt -> Tot (a & vt))
      (f: external_action_spec name state a spec)
      (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_singleton name state) a use_error_handler
    (S.aspec_extern name state spec)

noextract
inline_for_extraction
val action_field_ptr_after_with_setter
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#vt: Type0)
      (#name: string)
      (#state: vt -> slprop)
      (#sp: PM.ptr -> vt -> Tot (unit & vt))
      (f: field_ptr_after_setter_t base_t len_t pos_t name state sp)
      (sz: U64.t)
      (write_to: (p: PM.ptr -> external_action_spec name state unit (sp p)))
      (sq: squash (forall x . ~ ((state_dict_singleton name state).state_p x /\ peep_world_dict.state_p x)))
      (#use_error_handler: bool)
: action #base_t #len_t #pos_t (state_dict_prod (state_dict_singleton name state) peep_world_dict) bool use_error_handler
    (S.aspec_field_ptr_after_with_setter name state sp peep_world sq)

noextract
inline_for_extraction
val probe_then_validate
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#copy_buffer_t: Type0)
  {| cb_inst: CP.copy_buffer copy_buffer_t base_t len_t pos_t  |}
  (#boolean_t: Type0)
  {| boolean_inst: Bool.boolean_repr boolean_t |}
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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_read #base_t #len_t #pos_t p extra_state ha use_error_handler s)
      (#ptr_t: Type0)
      (src: ptr_t)
      (as_u64: (ptr_t -> PA.pure_external_action U64.t))
      (nullable: bool)
      (dest_name: Ghost.erased string)
      (dest: copy_buffer_t)
      (init: PA.init_probe_dest_t #copy_buffer_t #base_t #len_t #pos_t #inst #cb_inst #boolean_t #boolean_inst)
      (prep_dest_sz: U64.t)
      (#mz: bool)
      (probe: PA.probe_m #_ #_ #_ #_ #inst #cb_inst #boolean_t #boolean_inst unit true mz use_error_handler)
      (sq: squash (forall x .
        ~ (extra_state.state_p x /\
           (copy_buffer_state_dict #_ #base_t #len_t #pos_t dest_name dest).state_p x)))
: vaction #base_t #len_t #pos_t
    (state_dict_prod extra_state (copy_buffer_state_dict #_ #base_t #len_t #pos_t dest_name dest))
    use_error_handler
    (S.vaspec_probe_then_validate s nullable dest_name (copy_buffer_state #_ #base_t #len_t #pos_t dest) sq)

inline_for_extraction noextract
val validate_impos_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
       (#extra_state: _)
       (#use_error_handler:bool)
       (_:unit)
: validate_with_action_no_read #base_t #len_t #pos_t (parse_impos ()) extra_state false use_error_handler (S.vspec_of_parser (parse_impos ()))

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
: validate_with_action_no_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v1: validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler s)
: validate_with_action_no_read #base_t #len_t #pos_t p1 extra_state has_action use_error_handler s

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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s
= match allow_reading
  returns validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s
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
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s)
: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s
= match allow_reading
  returns validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s
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
      (#[@@@erasable] s: S.vspec extra_state)
      (v1: validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action allow_reading use_error_handler s)
: validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action allow_reading use_error_handler s
= match allow_reading
  returns validate_with_action_t #base_t #len_t #pos_t p1 extra_state has_action allow_reading use_error_handler s
  with
  | true -> validate_with_error_handler_no_read #base_t #len_t #pos_t error_handler_macro typename fieldname v1
  | false -> validate_with_error_handler #base_t #len_t #pos_t error_handler_macro typename fieldname v1

inline_for_extraction noextract
let validate_without_reading_gen
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
  (#[EverParse3d.Util.solve_from_ctx ()] _extra: inst.extra_t)
      (#nz:bool)
      (#wk: _)
      (#k:parser_kind nz wk)
      (#t:Type)
      (#p:parser k t)
      (#extra_state: state_dict)
      (#has_action:bool)
      (allow_reading:bool)
      (#use_error_handler:bool)
      (#[@@@erasable] s: S.vspec extra_state)
      (v: validate_with_action_t #base_t #len_t #pos_t p extra_state has_action allow_reading use_error_handler s)
: validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s
= match allow_reading
  returns (validate_with_action_read #base_t #len_t #pos_t p extra_state has_action use_error_handler s)
  with
  | true -> validate_without_reading #base_t #len_t #pos_t v
  | false -> v

inline_for_extraction noextract
val validate_unit_no_read
  (#base_t #len_t #pos_t: Type0)
  {| inst: I.input_stream_inst base_t len_t pos_t  |}
      (#extra_state: state_dict)
      (#use_error_handler:bool)
: validate_with_action_no_read #base_t #len_t #pos_t parse_unit extra_state false use_error_handler (S.vspec_of_parser parse_unit)

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
       (#[@@@erasable] s: S.vspec d1)
       (v:validate_with_action_no_read #base_t #len_t #pos_t p d1 has_action use_error_handler s)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_no_read #base_t #len_t #pos_t p d2 has_action use_error_handler (S.vspec_weaken s d2 d2_extends)

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
      (#[@@@erasable] s: S.vspec d1)
      (v: validate_with_action_t #base_t #len_t #pos_t p d1 has_action allow_reading use_error_handler s)
      (d2: state_dict)
      (d2_extends: squash (state_dict_weaken_prop d1 d2))
: validate_with_action_t #base_t #len_t #pos_t p d2 has_action allow_reading use_error_handler (S.vspec_weaken s d2 d2_extends)
= match allow_reading
  returns (validate_with_action_t #base_t #len_t #pos_t p d2 has_action allow_reading use_error_handler (S.vspec_weaken s d2 d2_extends))
  with
  | true -> validate_weaken_no_read #base_t #len_t #pos_t name v d2 d2_extends
  | false -> validate_weaken #base_t #len_t #pos_t name v d2 d2_extends
