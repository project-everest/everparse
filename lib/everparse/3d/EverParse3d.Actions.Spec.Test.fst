module EverParse3d.Actions.Spec.Test
(* A client of the functional specification of 3d validators
   (EverParse3d.Actions.Spec, EverParse3d.Interpreter.as_vspec): prove, from
   the spec alone, what a validator with actions does to its action state.

   The type below is what 3d generates for

     typedef struct _T (mutable UINT32 *out) {
       UINT32 x {:act *out = x; };
     } T;

   and the lemma says that its validator succeeds if, and only if, the input
   starts with a 32-bit integer, in which case it stores that integer into
   `*out`. Since the validator of `T` is typed by `as_vspec "T" (t k out)`,
   this lemma transfers to the validator itself. *)
open Pulse.Lib.Pervasives
open EverParse3d.State
module S = EverParse3d.Actions.Spec
module I = EverParse3d.Interpreter
module P = EverParse3d.Prelude
module B = EverParse3d.InputStream.Buffer
module U32 = FStar.UInt32
module T = FStar.Tactics.V2

let d (k: Ghost.erased string) (out: ref U32.t) : state_dict =
  state_dict_singleton k (pts_to out #1.0R)

let t (k: Ghost.erased string) (out: ref U32.t)
: I.typ B.base_t B.len_t B.pos_t B.input_stream_buffer (d k out) false _ true false
= I.T_with_dep_action "x" (I.DT_IType I.UInt32)
    (fun _ x -> I.Action_act (I.Atomic_action (I.Action_assignment k out x ())))

let t_spec_correct
  (k: Ghost.erased string) (out: ref U32.t)
  (i: S.vinput) (s: forevery_values (d k out))
: Lemma (
    let r = I.as_vspec "T" (t k out) i s in
    match P.parse P.parse____UINT32 i.rest with
    | None -> r == S.VErr
    | Some (x, _) -> S.VOk? r /\ (S.VOk?.final r) (Ghost.reveal k) == x
  )
= assert (I.as_vspec "T" (t k out) ==
    S.vspec_with_dep_action P.parse____UINT32 (S.vspec_of_parser P.parse____UINT32)
      (fun x -> S.aspec_seq
        (S.aspec_weaken (S.aspec_assignment k (pts_to out #1.0R) x) (d k out) ())
        (S.aspec_return true)))
    by (T.norm [delta_only [`%t; `%I.as_vspec; `%I.dtyp_as_vspec; `%I.dtyp_as_parser;
                            `%I.itype_as_parser; `%I.action_as_spec; `%I.atomic_action_as_spec];
                zeta; iota];
        T.trefl ());
  match P.parse P.parse____UINT32 i.rest with
  | None -> ()
  | Some (x, _) ->
    let s1 = mk_singleton_value k (pts_to out #1.0R) x in
    S.mk_singleton_value_eq k (pts_to out #1.0R) x;
    S.weaken_update_in (d k out) (d k out) () s s1 k
