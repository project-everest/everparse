module SpecPeep.Lemmas
friend SpecPeep
open Pulse.Lib.Pervasives
open EverParse3d.State
open SpecPeep
module S = EverParse3d.Actions.Spec
module VS = EverParse3d.Actions.ValueSpec
module I = EverParse3d.Interpreter
module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.Static
module PM = EverParse3d.PtrModel
module U32 = FStar.UInt32
module T = FStar.Tactics.V2

#set-options "--z3rlimit 50 --fuel 2 --max_fuel 2 --ifuel 1 --max_ifuel 1"

let d_k (k: Ghost.erased string) (out: ref PM.ptr) : state_dict =
  state_dict_singleton k (pts_to out #1.0R)

let d_peep (k: Ghost.erased string) (out: ref PM.ptr) (sq: squash (Ghost.reveal k =!= S.world_key)) : state_dict =
  state_dict_prod (d_k k out) A.peep_world_dict

(* The components of the action state. *)
let out_of (#k: Ghost.erased string) (#out: ref PM.ptr) (#sq: squash (Ghost.reveal k =!= S.world_key))
  (s: forevery_values (d_peep k out sq)) : GTot PM.ptr =
  mk_proj_value s (d_k k out) () k

let world_of (#k: Ghost.erased string) (#out: ref PM.ptr) (#sq: squash (Ghost.reveal k =!= S.world_key))
  (s: forevery_values (d_peep k out sq)) : GTot S.peep_tape =
  mk_proj_value s A.peep_world_dict () S.world_key

(* Peep: whatever the client's Peep callback does, its outcome is the head of
   the peep world (a prophecy of the outcomes of all its future calls): the
   validator succeeds exactly when the head is `Some p`, in which case `p` is
   stored; in both cases, the world advances. *)
val peep_value
  (k: Ghost.erased string) (out: ref PM.ptr) (sq: squash (Ghost.reveal k =!= S.world_key))
  (extra: B.extra_t)
  (pos: S.aenv) (v: U32.t & U32.t) (s: forevery_values (d_peep k out sq))
: Lemma (
    let w = world_of s in
    match I.as_value_spec "Peep" (def'__Peep k out sq #extra) pos v s with
    | S.VOk s' -> Some? (S.peep_head w) /\ out_of s' == Some?.v (S.peep_head w) /\
      world_of s' == S.peep_tail w
    | S.VErr -> None? (S.peep_head w))

let peep_value k out sq extra pos v s =
  assert (
    let w = world_of s in
    match I.as_value_spec "Peep" (def'__Peep k out sq #extra) pos v s with
    | S.VOk s' -> Some? (S.peep_head w) /\ out_of s' == Some?.v (S.peep_head w) /\
      world_of s' == S.peep_tail w
    | S.VErr -> None? (S.peep_head w))
  by (T.norm [delta_namespace ["SpecPeep"];
              delta_only [`%I.as_value_spec; `%I.dtyp_as_value_spec; `%I.action_as_spec; `%I.atomic_action_as_spec;
                          `%I.coerce];
              zeta; iota; primops];
      T.smt ())

(* Non-vacuity: the Peep callback may fail, and then so does the validator. *)
#push-options "--z3rlimit 20"
[@@expect_failure [19]]
let peep_value_wrong
  (k: Ghost.erased string) (out: ref PM.ptr) (sq: squash (Ghost.reveal k =!= S.world_key))
  (extra: B.extra_t)
  (pos: S.aenv) (v: U32.t & U32.t) (s: forevery_values (d_peep k out sq))
: Lemma (S.VOk? (I.as_value_spec "Peep" (def'__Peep k out sq #extra) pos v s))
= peep_value k out sq extra pos v s
#pop-options
