module EverParse3d.Actions.Spec

(* Purely functional specifications of 3d actions and validators.

   A validator for a parser `p` with action state `d` (a `state_dict`) is
   indexed by a `vspec d`: a ghost function that, given the input and the
   *values* of the action state before validation, says whether validation
   succeeds (`VOk`, along with the final values of the action state), fails
   (`VErr`), or is left unspecified (`VUnknown`, e.g. when it depends on an
   external action or a probe).

   Likewise, an action is indexed by an `action_spec d a`: given the position
   of the field it is attached to and the values of the action state, it
   returns the result of the action along with the final values of the action
   state (`SOk`), or `SUnknown`.

   The spec combinators below mirror the control flow of the validator
   combinators of `EverParse3d.Actions.Base` exactly, including their
   optimizations (fast paths), so that the spec of a 3d type is obtained by the
   same specialization process as its validator. *)

open EverParse3d.State
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
open EverParse3d.ErrorCode

(* The input of a validator: the contents of the (possibly truncated) input
   stream, and the bytes that remain to be validated. *)
noeq
type vinput = {
  contents: Seq.seq U8.t;
  rest: Seq.seq U8.t;
}

(* The current position in the input stream. *)
let vpos (i: vinput) : GTot nat =
  if Seq.length i.rest <= Seq.length i.contents
  then Seq.length i.contents - Seq.length i.rest
  else 0

let vadvance (i: vinput) (n: nat { n <= Seq.length i.rest }) : GTot vinput =
  { i with rest = Seq.slice i.rest n (Seq.length i.rest) }

(* The input of a validator run on a stream truncated to its `n` next bytes, as
   done by `T_exact`, `T_at_most` and `T_nlist`. *)
let vtruncate (i: vinput) (n: nat { n <= Seq.length i.rest }) : GTot vinput =
  {
    contents = Seq.append (Seq.slice i.contents 0 (vpos i)) (Seq.slice i.rest 0 n);
    rest = Seq.slice i.rest 0 n;
  }

noeq
type vres (d: state_dict) =
| VOk: (final: forevery_values d) -> vres d
| VErr: vres d
| VUnknown: vres d

let vspec (d: state_dict) : Type0 =
  vinput -> forevery_values d -> GTot (vres d)

(* How a validator result relates to its spec. On error, the final state of
   the actions is left unspecified, since actions may have been partially
   executed. *)
let vres_rel (#d: state_dict) (r: vres d) (res: U8.t) (final: forevery_values d) : Tot prop =
  match r with
  | VOk final' -> res == validator_success /\ final == final'
  | VErr -> ~ (res == validator_success)
  | VUnknown -> True

(* The environment of an action: the position at which the field it is
   attached to starts, and the stream after that field. *)
noeq
type aenv = {
  a_start: nat;
  a_contents: Seq.seq U8.t;
  a_rest: Seq.seq U8.t;
}

noeq
type spec_res (d: state_dict) (a: Type0) =
| SOk: (res: a) -> (final: forevery_values d) -> spec_res d a
| SUnknown: spec_res d a

let action_spec (d: state_dict) (a: Type0) : Type0 =
  aenv -> forevery_values d -> GTot (spec_res d a)

let spec_res_rel (#d: state_dict) (#a: Type0) (r: spec_res d a) (res: a) (final: forevery_values d) : Tot prop =
  match r with
  | SOk res' final' -> res == res' /\ final == final'
  | SUnknown -> True

(* The environment of an action attached to a field that started at `i` and
   that consumed `n` bytes. *)
let aenv_of (i: vinput) (n: nat { n <= Seq.length i.rest }) : GTot aenv = {
  a_start = vpos i;
  a_contents = i.contents;
  a_rest = Seq.slice i.rest n (Seq.length i.rest);
}

(** Action specs *)

let aspec_unknown (#d: state_dict) (#a: Type0) : action_spec d a =
  fun _ _ -> SUnknown

let aspec_return (#d: state_dict) (#a: Type0) (x: a) : action_spec d a =
  fun _ s -> SOk x s

let aspec_bind (#d: state_dict) (#a #b: Type0) (f: action_spec d a) (g: a -> action_spec d b) : action_spec d b =
  fun e s -> match f e s with
  | SOk x s' -> g x e s'
  | SUnknown -> SUnknown

let aspec_seq (#d: state_dict) (#a #b: Type0) (f: action_spec d a) (g: action_spec d b) : action_spec d b =
  fun e s -> match f e s with
  | SOk _ s' -> g e s'
  | SUnknown -> SUnknown

let aspec_ite (#d: state_dict) (#a: Type0) (guard: bool)
  (then_: squash (guard == true) -> action_spec d a)
  (else_: squash (guard == false) -> action_spec d a)
: action_spec d a
= fun e s -> if guard then then_ () e s else else_ () e s

let aspec_field_pos_64 (#d: state_dict) : action_spec d U64.t =
  fun e s -> SOk (U64.uint_to_t (e.a_start % pow2 64)) s

let aspec_field_pos_32 (#d: state_dict) : action_spec d U32.t =
  fun e s -> SOk (U32.uint_to_t (e.a_start % pow2 32)) s

let aspec_deref
  (name: string) (#a: Type0) (state: a -> Pulse.Lib.Core.slprop)
: action_spec (state_dict_singleton name state) a
= fun _ s -> SOk (s name) s

let aspec_deref_map
  (#a #b: Type0) (decode: a -> Tot b)
  (name: string) (state: a -> Pulse.Lib.Core.slprop)
: action_spec (state_dict_singleton name state) b
= fun _ s -> SOk (decode (s name)) s

let aspec_assignment
  (name: string) (#a: Type0) (state: a -> Pulse.Lib.Core.slprop) (w: a)
: action_spec (state_dict_singleton name state) unit
= fun _ _ -> SOk () (mk_singleton_value name state w)

(* A value of the action state of `d2` with its `d1` part replaced. *)
let weaken_update
  (d1 d2: state_dict)
  (sq: squash (state_dict_weaken_prop d1 d2))
  (s2: forevery_values d2)
  (s1': forevery_values d1)
: GTot (forevery_values d2)
= let d3 = state_dict_weaken_sub d2 d1 in
  coerce_eq () (mk_prod_value s1' (mk_proj_value s2 d3 ()) ())

(* Value-level lemmas, for clients reasoning about the final action state. *)

let mk_singleton_value_eq
  (name: string) (#a: Type0) (state: a -> Pulse.Lib.Core.slprop) (w: a)
: Lemma (mk_singleton_value name state w name == w)
= ()

let weaken_update_in
  (d1 d2: state_dict)
  (sq: squash (state_dict_weaken_prop d1 d2))
  (s2: forevery_values d2)
  (s1': forevery_values d1)
  (x: string)
: Lemma
  (requires (state_p d1 x))
  (ensures (
    state_p d2 x /\
    d2.state_values x == d1.state_values x /\
    weaken_update d1 d2 sq s2 s1' x == coerce_eq #(d1.state_values x) #(d2.state_values x) () (s1' x)
  ))
= reveal_state_dict_weaken_prop ();
  reveal_opaque (`%state_dict_prod) state_dict_prod

let weaken_update_out
  (d1 d2: state_dict)
  (sq: squash (state_dict_weaken_prop d1 d2))
  (s2: forevery_values d2)
  (s1': forevery_values d1)
  (x: string)
: Lemma
  (requires (state_p d2 x /\ ~ (state_p d1 x)))
  (ensures (weaken_update d1 d2 sq s2 s1' x == s2 x))
= reveal_state_dict_weaken_prop ();
  reveal_opaque (`%state_dict_prod) state_dict_prod

let aspec_weaken
  (#d1: state_dict) (#a: Type0) (f: action_spec d1 a)
  (d2: state_dict) (sq: squash (state_dict_weaken_prop d1 d2))
: action_spec d2 a
= fun e s2 -> match f e (mk_proj_value s2 d1 sq) with
  | SOk x s1' -> SOk x (weaken_update d1 d2 sq s2 s1')
  | SUnknown -> SUnknown

let aspec_call
  (#d': state_dict) (#a: Type0) (f: action_spec d' a)
  (d: state_dict)
  (rf: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p))))
  (rg: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
  (sq: squash (state_dict_rename_prop d d' rf rg))
: action_spec d a
= fun e s -> match f e (state_dict_rename_values_call d d' rf rg s) with
  | SOk x s' -> SOk x (state_dict_rename_values_return d d' rf rg s s')
  | SUnknown -> SUnknown

(** Validator specs *)

let vspec_unknown (#d: state_dict) : vspec d =
  fun _ _ -> VUnknown

(* The spec of a validator without actions: it succeeds iff the parser
   succeeds, and leaves the action state unchanged. *)
let vspec_of_parser (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t) : vspec d =
  fun i s -> match P.parse p i.rest with
  | Some _ -> VOk s
  | None -> VErr

(* The spec of a validator about which we know nothing but whether it has
   actions. Only used by `validate_list`, which is never used with actions. *)
let vspec_default (#d: state_dict) (ha: bool) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t) : vspec d =
  if ha then vspec_unknown else vspec_of_parser p

(* The result of running an action that returns a boolean, used as a
   validation result. *)
let vres_of_action (#d: state_dict) (r: spec_res d bool) (k: forevery_values d -> GTot (vres d)) : GTot (vres d) =
  match r with
  | SOk true s -> k s
  | SOk false _ -> VErr
  | SUnknown -> VUnknown

let vspec_with_success_action
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t)
  (s: vspec d) (a: action_spec d bool)
: vspec d
= fun i x -> match s i x with
  | VOk x1 ->
    begin match P.parse p i.rest with
    | Some (_, n) -> vres_of_action (a (aenv_of i n) x1) VOk
    | None -> VUnknown
    end
  | r -> r

let vspec_pair_slow
  (#d: state_dict) (#nz1: bool) (#wk1: P.weak_kind) (#k1: P.parser_kind nz1 wk1) (#t1: Type) (p1: P.parser k1 t1)
  (s1: vspec d) (s2: vspec d)
: vspec d
= fun i x -> match s1 i x with
  | VOk x1 ->
    begin match P.parse p1 i.rest with
    | Some (_, n) -> s2 (vadvance i n) x1
    | None -> VUnknown
    end
  | r -> r

let vspec_dep_pair
  (#d: state_dict) (#nz1: bool) (#wk1: P.weak_kind) (#k1: P.parser_kind nz1 wk1) (#t1: Type) (p1: P.parser k1 t1)
  (s1: vspec d) (s2: t1 -> vspec d)
: vspec d
= fun i x -> match s1 i x with
  | VOk x1 ->
    begin match P.parse p1 i.rest with
    | Some (v, n) -> s2 v (vadvance i n) x1
    | None -> VUnknown
    end
  | r -> r

let vspec_dep_pair_with_action
  (#d: state_dict) (#nz1: bool) (#wk1: P.weak_kind) (#k1: P.parser_kind nz1 wk1) (#t1: Type) (p1: P.parser k1 t1)
  (s1: vspec d) (a: t1 -> action_spec d bool) (s2: t1 -> vspec d)
: vspec d
= fun i x -> match s1 i x with
  | VOk x1 ->
    begin match P.parse p1 i.rest with
    | Some (v, n) -> vres_of_action (a v (aenv_of i n) x1) (s2 v (vadvance i n))
    | None -> VUnknown
    end
  | r -> r

(* The second component of a refined dependent pair, once the first component
   `v` has been parsed and has consumed `n` bytes from `i`, starting from the
   action state `x1`. *)
let vspec_refine_then
  (#d: state_dict) (#t1: Type) (f: t1 -> bool)
  (a: option (t1 -> action_spec d bool))
  (s2: P.refine t1 f -> vspec d)
  (i: vinput) (v: t1) (n: nat { n <= Seq.length i.rest }) (x1: forevery_values d)
: GTot (vres d)
= if f v
  then match a with
    | None -> s2 v (vadvance i n) x1
    | Some a -> vres_of_action (a v (aenv_of i n) x1) (s2 v (vadvance i n))
  else VErr

(* The fast path of `validate_dep_pair_with_refinement*`: when `p1` is total and
   consumes no input, its validator is skipped. *)
let vspec_dep_pair_with_refinement_total_zero
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix)
  (#t1: Type) (p1: P.parser k1 t1)
  (f: t1 -> bool)
  (a: option (t1 -> action_spec d bool))
  (s2: P.refine t1 f -> vspec d)
: vspec d
= fun i x -> match P.parse p1 i.rest with
  | Some (v, n) -> vspec_refine_then f a s2 i v n x
  | None -> VUnknown

let vspec_dep_pair_with_refinement_slow
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix)
  (#t1: Type) (p1: P.parser k1 t1)
  (s1: vspec d) (f: t1 -> bool)
  (a: option (t1 -> action_spec d bool))
  (s2: P.refine t1 f -> vspec d)
: vspec d
= fun i x -> match s1 i x with
  | VOk x1 ->
    begin match P.parse p1 i.rest with
    | Some (v, n) -> vspec_refine_then f a s2 i v n x1
    | None -> VUnknown
    end
  | r -> r

let vspec_dep_pair_with_refinement_gen
  (p1_is_constant_size_without_actions: bool)
  (#d: state_dict) (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix)
  (#t1: Type) (p1: P.parser k1 t1)
  (s1: vspec d) (f: t1 -> bool)
  (a: option (t1 -> action_spec d bool))
  (s2: P.refine t1 f -> vspec d)
: vspec d
= if p1_is_constant_size_without_actions &&
     (k1.LP.parser_kind_high = Some 0) &&
     (k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal)
  then vspec_dep_pair_with_refinement_total_zero p1 f a s2
  else vspec_dep_pair_with_refinement_slow p1 s1 f a s2

let vspec_filter
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t)
  (s: vspec d) (f: t -> bool) (a: option (t -> action_spec d bool))
: vspec d
= fun i x -> match s i x with
  | VOk x1 ->
    begin match P.parse p i.rest with
    | Some (v, n) ->
      if f v
      then match a with
        | None -> VOk x1
        | Some a -> vres_of_action (a v (aenv_of i n) x1) VOk
      else VErr
    | None -> VUnknown
    end
  | r -> r

let vspec_with_dep_action
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t)
  (s: vspec d) (a: t -> action_spec d bool)
: vspec d
= fun i x -> match s i x with
  | VOk x1 ->
    begin match P.parse p i.rest with
    | Some (v, n) -> vres_of_action (a v (aenv_of i n) x1) VOk
    | None -> VUnknown
    end
  | r -> r

let vspec_ite
  (#d: state_dict) (e: bool)
  (s1: squash e -> vspec d) (s2: squash (not e) -> vspec d)
: vspec d
= fun i x -> if e then s1 () i x else s2 () i x

let vspec_weaken
  (#d1: state_dict) (s: vspec d1)
  (d2: state_dict) (sq: squash (state_dict_weaken_prop d1 d2))
: vspec d2
= fun i x2 -> match s i (mk_proj_value x2 d1 sq) with
  | VOk x1' -> VOk (weaken_update d1 d2 sq x2 x1')
  | VErr -> VErr
  | VUnknown -> VUnknown

let vspec_call
  (#d': state_dict) (s: vspec d')
  (d: state_dict)
  (rf: Ghost.erased ((x: refine_bool_t string d.state_p) -> Tot (option (refine_bool_t string d'.state_p))))
  (rg: Ghost.erased (refine_bool_t string d'.state_p -> Tot (refine_bool_t string d.state_p)))
  (sq: squash (state_dict_rename_prop d d' rf rg))
: vspec d
= fun i x -> match s i (state_dict_rename_values_call d d' rf rg x) with
  | VOk x' -> VOk (state_dict_rename_values_return d d' rf rg x x')
  | VErr -> VErr
  | VUnknown -> VUnknown

let vspec_t_exact
  (#d: state_dict) (n: U32.t) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t)
  (s: vspec d)
: vspec d
= fun i x ->
  if Seq.length i.rest < U32.v n
  then VErr
  else match s (vtruncate i (U32.v n)) x with
  | VOk x' ->
    begin match P.parse p (Seq.slice i.rest 0 (U32.v n)) with
    | Some (_, m) -> if (m <: nat) = U32.v n then VOk x' else VErr
    | None -> VUnknown
    end
  | r -> r

let vspec_t_at_most
  (#d: state_dict) (n: U32.t) (s: vspec d)
: vspec d
= fun i x ->
  if Seq.length i.rest < U32.v n
  then VErr
  else s (vtruncate i (U32.v n)) x

(** Loops *)

(* The spec of a loop over the elements of a list that consumes all of its
   input, as done by `validate_nlist`: a left fold of the spec `s` of the
   element over the input, stopping at the first failure. Each step runs `s`
   on the remaining input `rest`, then continues after the bytes consumed by
   the element. *)
let rec vspec_list_fold
  (#d: state_dict) (#nz: bool) (#wk: P.weak_kind) (#k: P.parser_kind nz wk) (#t: Type) (p: P.parser k t)
  (s: vspec d) (contents rest: Seq.seq U8.t) (x: forevery_values d)
: GTot (vres d) (decreases (Seq.length rest))
= if Seq.length rest = 0
  then VOk x
  else match s ({ contents = contents; rest = rest }) x with
  | VOk x' ->
    begin match P.parse p rest with
    | Some (_, n) ->
      if n > 0
      then vspec_list_fold p s contents (Seq.slice rest n (Seq.length rest)) x'
      else VUnknown
    | None -> VUnknown
    end
  | r -> r

(* The spec of `validate_nlist`. Without actions, it is the spec of the parser,
   which also covers the fast paths of `validate_nlist_constant_size_without_actions`. *)
let vspec_nlist
  (#d: state_dict) (ha: bool)
  (n: U32.t) (n_is_const: option nat { P.memoizes_n_as_const n_is_const n })
  (#wk: P.weak_kind) (#k: P.parser_kind true wk) (#t: Type) (p: P.parser k t)
  (s: vspec d)
: vspec d
= if ha
  then fun i x ->
    if Seq.length i.rest < U32.v n
    then VErr
    else
      let i' = vtruncate i (U32.v n) in
      vspec_list_fold p s i'.contents i'.rest x
  else vspec_of_parser (P.parse_nlist n n_is_const p)

(* The spec of a loop over the elements of a list up to a terminator, as done
   by `validate_string`: like `vspec_list_fold`, but stops after the
   terminator. *)
let rec vspec_string_fold
  (#d: state_dict) (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (s: vspec d) (contents rest: Seq.seq U8.t) (x: forevery_values d)
: GTot (vres d) (decreases (Seq.length rest))
= match s ({ contents = contents; rest = rest }) x with
  | VOk x' ->
    begin match P.parse p rest with
    | Some (y, n) ->
      if y = terminator
      then VOk x'
      else if n > 0
      then vspec_string_fold p terminator s contents (Seq.slice rest n (Seq.length rest)) x'
      else VUnknown
    | None -> VUnknown
    end
  | r -> r

let vspec_string_gen
  (#d: state_dict) (ha: bool)
  (#nzq: bool) (#wkq: P.weak_kind) (#kq: P.parser_kind nzq wkq) (#tq: Type) (q: P.parser kq tq)
  (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (s: vspec d)
: vspec d
= if ha
  then fun i x -> vspec_string_fold p terminator s i.contents i.rest x
  else vspec_of_parser q

let vspec_string
  (#d: state_dict) (ha: bool)
  (#k: P.parser_kind true P.WeakKindStrongPrefix) (#t: eqtype) (p: P.parser k t)
  (terminator: t) (s: vspec d)
: vspec d
= vspec_string_gen ha (P.parse_string p terminator) p terminator s

(* The dispatcher of `validate_pair`. *)
let vspec_pair
  (#d: state_dict)
  (#nz1: bool) (#k1: P.parser_kind nz1 P.WeakKindStrongPrefix) (#t1: Type) (p1: P.parser k1 t1)
  (k1_const: bool) (has_action1: bool) (s1: vspec d)
  (#nz2: bool) (#wk2: P.weak_kind) (#k2: P.parser_kind nz2 wk2) (#t2: Type) (p2: P.parser k2 t2)
  (k2_const: bool) (has_action2: bool) (s2: vspec d)
: vspec d
= if k1_const && k2_const &&
     (not has_action1) && (not has_action2) &&
     k1.LP.parser_kind_high = Some k1.LP.parser_kind_low &&
     k1.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal &&
     k2.LP.parser_kind_high = Some k2.LP.parser_kind_low &&
     k2.LP.parser_kind_metadata = Some LP.ParserKindMetadataTotal &&
     k1.LP.parser_kind_low + k2.LP.parser_kind_low < 4294967296
  then vspec_of_parser (P.parse_pair p1 p2)
  else vspec_pair_slow p1 s1 s2

(** Lemmas *)

let singleton_value_eta
  (name: string) (#t: Type0) (state: t -> Pulse.Lib.Core.slprop)
  (v: forevery_values (state_dict_singleton name state))
: Lemma (mk_singleton_value name state (v name) == v)
= forevery_values_ext (state_dict_singleton name state) (mk_singleton_value name state (v name)) v
