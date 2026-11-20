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

let t_vspec (k: Ghost.erased string) (out: ref U32.t) : S.vspec (d k out) =
  S.vspec_with_dep_action P.parse____UINT32 (S.vspec_of_parser P.parse____UINT32)
    (fun x -> S.aspec_seq
      (S.aspec_weaken (S.aspec_assignment k (pts_to out #1.0R) x) (d k out) ())
      (S.aspec_return true))

let t_vspec_eq (tn: string) (k: Ghost.erased string) (out: ref U32.t)
: Lemma (I.as_vspec tn (t k out) == t_vspec k out)
= assert (I.as_vspec tn (t k out) == t_vspec k out)
    by (T.norm [delta_only [`%t; `%t_vspec; `%I.as_vspec; `%I.dtyp_as_vspec; `%I.dtyp_as_parser;
                            `%I.itype_as_parser; `%I.action_as_spec; `%I.atomic_action_as_spec];
                zeta; iota];
        T.trefl ())

let t_vspec_correct
  (k: Ghost.erased string) (out: ref U32.t)
  (i: S.vinput) (s: forevery_values (d k out))
: Lemma (
    let r = t_vspec k out i s in
    match P.parse P.parse____UINT32 i.rest with
    | None -> r == S.VErr
    | Some (x, _) -> S.VOk? r /\ (S.VOk?.final r) (Ghost.reveal k) == x
  )
= match P.parse P.parse____UINT32 i.rest with
  | None -> ()
  | Some (x, _) ->
    let s1 = mk_singleton_value k (pts_to out #1.0R) x in
    S.mk_singleton_value_eq k (pts_to out #1.0R) x;
    S.weaken_update_in (d k out) (d k out) () s s1 k

let t_spec_correct
  (k: Ghost.erased string) (out: ref U32.t)
  (i: S.vinput) (s: forevery_values (d k out))
: Lemma (
    let r = I.as_vspec "T" (t k out) i s in
    match P.parse P.parse____UINT32 i.rest with
    | None -> r == S.VErr
    | Some (x, _) -> S.VOk? r /\ (S.VOk?.final r) (Ghost.reveal k) == x
  )
= t_vspec_eq "T" k out;
  t_vspec_correct k out i s

(* An array of two such elements, as generated for

     typedef struct _TA (mutable UINT32 *out) {
       T(out) a[:byte-size 8];
     } TA;

   Its spec is a fold of the spec of `T` over the array: the action of each
   element runs in turn, so `*out` ends up holding the last element. *)
let ta (k: Ghost.erased string) (out: ref U32.t)
: I.typ B.base_t B.len_t B.pos_t B.input_stream_buffer (d k out) false _ true false
= I.T_nlist "a" 8ul (Some 8) true (t k out)

let ta_vspec_eq (tn: string) (k: Ghost.erased string) (out: ref U32.t)
: Lemma (I.as_vspec tn (ta k out) == S.vspec_nlist true 8ul (Some 8) P.parse____UINT32 (t_vspec k out))
= assert (I.as_vspec tn (ta k out) == S.vspec_nlist true 8ul (Some 8) P.parse____UINT32 (t_vspec k out))
    by (T.norm [delta_only [`%ta; `%t; `%t_vspec; `%I.as_vspec; `%I.as_parser; `%I.dtyp_as_vspec; `%I.dtyp_as_parser;
                            `%I.itype_as_parser; `%I.action_as_spec; `%I.atomic_action_as_spec];
                zeta; iota];
        T.trefl ())

#push-options "--fuel 4 --ifuel 2 --z3rlimit 32"
let ta_spec_correct
  (k: Ghost.erased string) (out: ref U32.t)
  (i: S.vinput) (s: forevery_values (d k out))
  (x0 x1: U32.t)
: Lemma
  (requires (
    Seq.length i.rest >= 8 /\
    P.parse P.parse____UINT32 (Seq.slice i.rest 0 8) == Some (x0, 4) /\
    P.parse P.parse____UINT32 (Seq.slice i.rest 4 8) == Some (x1, 4)
  ))
  (ensures (
    let r = I.as_vspec "TA" (ta k out) i s in
    S.VOk? r /\ (S.VOk?.final r) (Ghost.reveal k) == x1
  ))
= ta_vspec_eq "TA" k out;
  let i' = S.vtruncate i 8 in
  t_vspec_correct k out i' s;
  let S.VOk s1 = t_vspec k out i' s in
  let rest2 = Seq.slice i'.S.rest 4 8 in
  Seq.lemma_eq_elim rest2 (Seq.slice i.rest 4 8);
  let i2 = { S.contents = i'.S.contents; S.rest = rest2 } in
  t_vspec_correct k out i2 s1;
  assert (Seq.length (Seq.slice rest2 4 4) == 0)
#pop-options
