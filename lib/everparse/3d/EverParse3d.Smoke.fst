module EverParse3d.Smoke
#lang-pulse
(* A smoke test: check that the combinators exported by
   EverParse3d.Actions.Base can actually be applied by a client module, at the
   `buffer` backend instance. *)
open Pulse.Lib.Pervasives
open EverParse3d.Prelude
open EverParse3d.State
module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.Buffer

inline_for_extraction noextract
let smoke_v
: A.validate_with_action_t
    #B.base_t #B.len_t #B.pos_t
    (parse____UINT8 `parse_pair` parse____UINT16)
    state_dict_empty
    false
    false
= A.validate_pair "smoke" "fst" true (A.validate_without_reading A.validate____UINT8) true (A.validate_without_reading A.validate____UINT16)

inline_for_extraction noextract
let smoke_r
: A.leaf_reader #B.base_t #B.len_t #B.pos_t parse____UINT32
= A.read____UINT32

(* The same, at the `extern` backend. The instance has to be given explicitly,
   since `extern` and `static` share the same base type. *)
module E = EverParse3d.InputStream.Extern

inline_for_extraction noextract
let smoke_extern
: A.validate_with_action_t
    #E.base_t #E.len_t #E.pos_t #E.input_stream_extern
    (parse____UINT8 `parse_pair` parse____UINT16)
    state_dict_empty
    false
    false
= A.validate_pair #_ #_ #_ #E.input_stream_extern "smoke" "fst" true
    (A.validate_without_reading A.validate____UINT8) true
    (A.validate_without_reading A.validate____UINT16)

(* And at the `static` backend. *)
module St = EverParse3d.InputStream.Static

inline_for_extraction noextract
let smoke_static
: A.validate_with_action_t
    #St.base_t #St.len_t #St.pos_t #St.input_stream_static
    parse____UINT32
    state_dict_empty
    false
    false
= A.validate_without_reading #_ #_ #_ #St.input_stream_static A.validate____UINT32

(* Probe combinators, at the `buffer` backend. As above, this is here to make
   sure the definitions of EverParse3d.ProbeActions are really applicable by a
   client (and, in particular, that they are not hidden inside a comment). *)
module P = EverParse3d.ProbeActions

inline_for_extraction noextract
let smoke_probe
  (f: P.probe_fn_incremental #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t)
  (init: P.init_probe_dest_t #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t)
: P.probe_m #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t unit false false false
= P.init_and_probe "smoke"
    init
    (P.seq_probe_m B.error_handler_macro "smoke" ()
      (P.probe_and_copy_init_sz B.error_handler_macro f)
      (P.probe_array B.error_handler_macro 8uL
        (P.seq_probe_m B.error_handler_macro "elem" ()
          (P.skip_read 4uL)
          (P.skip_write 4uL))))

inline_for_extraction noextract
fn smoke_run_probe
  (m: P.probe_m #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t unit false false false)
  (ctxt: EverParse3d.Actions.Common.app_ctxt)
  (src: FStar.UInt64.t)
  (sz: FStar.UInt64.t)
  (dest: B.copy_buffer_t)
  (#v_ctxt: Ghost.erased FStar.UInt8.t)
  (#contents_dest #v_dest: Ghost.erased (Seq.seq FStar.UInt8.t))
requires
    pts_to ctxt v_ctxt ** EverParse3d.CopyBuffer.pts_to #_ #B.base_t #B.len_t #B.pos_t dest contents_dest v_dest
returns b: FStar.UInt64.t
ensures
    (exists* v_ctxt' contents_dest' v_dest' .
      pts_to ctxt v_ctxt' **
      EverParse3d.CopyBuffer.pts_to #_ #B.base_t #B.len_t #B.pos_t dest contents_dest' v_dest' **
      pure (b <> 0uL ==> contents_dest' == v_dest')
    )
{
  P.run_probe_m B.error_handler_macro m "smoke" "smoke" "smoke" ctxt () src sz dest
}

(* Generic external actions, field_ptr_after with a setter, and
   probe_then_validate, at the `buffer` backend. *)
module A = EverParse3d.Actions.Base

inline_for_extraction noextract
let smoke_external_action
  (d: state_dict)
  (f: A.external_action d unit)
: A.action #B.base_t #B.len_t #B.pos_t d unit false
= A.mk_external_action f

inline_for_extraction noextract
let smoke_field_ptr_after_with_setter
  (d: state_dict)
  (#ptr_t: Type0)
  (f: option (A.field_ptr_after_setter_t B.base_t B.len_t B.pos_t d ptr_t))
  (sq: squash (Some? f))
  (sz: FStar.UInt64.t)
  (write_to: (ptr_t -> A.external_action d unit))
: A.action #B.base_t #B.len_t #B.pos_t d bool false
= A.action_field_ptr_after_with_setter f sq sz write_to

inline_for_extraction noextract
let smoke_probe_then_validate
  (#nz: bool) (#wk: _) (#k: EverParse3d.Kinds.parser_kind nz wk)
  (#t: Type0) (#p: EverParse3d.Prelude.parser k t)
  (d: state_dict)
  (v: A.validate_with_action_t #B.base_t #B.len_t #B.pos_t p d false false)
  (#ptr_t: Type0)
  (src: ptr_t)
  (as_u64: (ptr_t -> P.pure_external_action FStar.UInt64.t))
  (dest: B.copy_buffer_t)
  (init: P.init_probe_dest_t #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t)
  (probe: P.probe_m #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t unit true false false)
  (sq: squash (forall x .
    ~ (d.state_p x /\ (A.copy_buffer_state_dict #_ #B.base_t #B.len_t #B.pos_t "smoke_cb" dest).state_p x)))
: A.action #B.base_t #B.len_t #B.pos_t
    (state_dict_prod d (A.copy_buffer_state_dict #_ #B.base_t #B.len_t #B.pos_t "smoke_cb" dest))
    bool false
= A.probe_then_validate B.error_handler_macro "T" "f" v src as_u64 true "smoke_cb" dest init 0uL probe sq
