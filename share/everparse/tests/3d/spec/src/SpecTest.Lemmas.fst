module SpecTest.Lemmas
friend SpecTest
open Pulse.Lib.Pervasives
open EverParse3d.State
open SpecTest
module S = EverParse3d.Actions.Spec
module VS = EverParse3d.Actions.ValueSpec
module I = EverParse3d.Interpreter
module P = EverParse3d.Prelude
module PM = EverParse3d.PtrModel
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module T = FStar.Tactics.V2
module U64 = FStar.UInt64
module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.Buffer
module X = SpecTest.ExternalAPI

#set-options "--z3rlimit 50 --fuel 2 --max_fuel 2 --ifuel 1 --max_ifuel 1"

let d_out (#t: Type0) (k: Ghost.erased string) (out: ref t) : state_dict =
  state_dict_singleton k (pts_to out #1.0R)

(* Store: the parsed value is stored. *)
val store_value
  (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (x: U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Store" (def'__Store k out ()) pos x s with
    | S.VOk s' -> s' (Ghost.reveal k) == x
    | _ -> False)

(* The same, on bytes: the validator fails if and only if parsing fails, and
   otherwise stores the parsed value. *)
val store_correct
  (k: Ghost.erased string) (out: ref U32.t)
  (i: S.vinput) (s: forevery_values (d_out k out))
: Lemma
  (requires (VS.vinput_ok i))
  (ensures (
    let r = I.as_vspec "Store" (def'__Store k out ()) i s in
    match P.parse (I.as_parser (def'__Store k out ())) i.S.rest with
    | None -> r == S.VErr
    | Some (x, _) -> S.VOk? r /\ (S.VOk?.final r) (Ghost.reveal k) == x))

(* Pos: field_pos_32 is the position where the annotated field starts, i.e.
   after the 2-byte padding. *)
val pos_value
  (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (v: U16.t & U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Pos" (def'__Pos k out ()) pos v s with
    | S.VOk s' -> s' (Ghost.reveal k) == U32.uint_to_t ((pos.S.a_start + 2) % pow2 32)
    | _ -> False)

(* Check: a :check action failing after a write makes the validator fail. *)
val check_value
  (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (v: U32.t & U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Check" (def'__Check k out ()) pos v s with
    | S.VOk s' -> fst v <> 0ul /\ s' (Ghost.reveal k) == fst v
    | S.VErr -> fst v == 0ul)

(* Arr: the actions of the array elements run in order, so the last element
   is stored. *)
val arr_value
  (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (l: P.nlist 8ul U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Arr" (def'__Arr k out ()) pos l s with
    | S.VOk s' -> (match VS.nlist_as_list l with
      | [] -> s' == s
      | l' -> s' (Ghost.reveal k) == List.Tot.last l')
    | _ -> False)

(* Ptr: field_ptr points to the start of the annotated field, i.e. after the
   2-byte padding, relative to the start of the input. *)
val ptr_value
  (k: Ghost.erased string) (out: ref PM.ptr)
  (pos: S.aenv) (v: U16.t & U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Ptr" (def'__Ptr k out ()) pos v s with
    | S.VOk s' -> s' (Ghost.reveal k) == PM.ptr_at pos.S.a_origin (pos.S.a_start + 2)
    | _ -> False)

(* Log: an extern action is specified by its uninterpreted spec `X.___spec____Push`
   on the abstract values of the output state: the final output state is that
   of the sequence of calls, in order. *)
val log_value
  (k: Ghost.erased string) (vec: ref X.___Vec)
  (pos: S.aenv) (v: U32.t & U32.t) (s: forevery_values X.___output_state)
: Lemma (match I.as_value_spec "Log" (def'__Log k vec ()) pos v s with
    | S.VOk s' -> s' "#output" ==
      snd (X.___spec____Push vec (snd v) (snd (X.___spec____Push vec (fst v) (s "#output"))))
    | _ -> False)

(* Set: an output setter is specified by its uninterpreted spec. *)
val set_value
  (k: Ghost.erased string) (out: SpecTest.ExternalTypes.p____OPAIR)
  (pos: S.aenv) (x: U32.t) (s: forevery_values X.___output_state)
: Lemma (match I.as_value_spec "Set" (def'__Set k out ()) pos x s with
    | S.VOk s' -> s' "#output" == X.___spec_set_OPAIR_deref_fst out x (s "#output")
    | _ -> False)

let d_probe (k: Ghost.erased string) (dest: B.copy_buffer_t) : state_dict =
  A.copy_buffer_state_dict #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t #B.input_stream_buffer #B.copy_buffer_buffer
    (Ghost.reveal k) dest

(* Probed: whatever the client C code does, the outcome of the probe is the
   head of the probe tape of `dest`: validation succeeds if and only if the
   probe succeeded and the copied bytes start with a valid `Inner`
   (double-fetch freedom), and the tape advances. *)
val probed_value
  (k: Ghost.erased string) (dest: B.copy_buffer_t)
  (pos: S.aenv) (x: U64.t) (s: forevery_values (d_probe k dest))
: Lemma (
    let w : S.probe_tape = s (Ghost.reveal k) in
    let o = S.ptape_head w in
    let ok = o.S.p_ok /\ Some? (P.parse (I.as_parser (def'__Inner ())) o.S.p_bytes) in
    match I.as_value_spec "Probed" (def'__Probed k dest ()) pos x s with
    | S.VOk s' -> ok /\ s' (Ghost.reveal k) == S.ptape_tail w
    | S.VErr -> ~ ok)


(* Unfold the generated definitions and the interpreter, leaving the spec
   combinators for SMT. *)
let unfold_value_spec () : T.Tac unit =
  T.norm [delta_namespace ["SpecTest"];
          delta_only [`%I.as_value_spec; `%I.dtyp_as_value_spec; `%I.action_as_spec; `%I.atomic_action_as_spec;
                      `%I.as_parser; `%I.dtyp_as_parser; `%I.itype_as_parser; `%I.coerce];
          zeta; iota; primops]

(* The facts SMT needs about writing `v` to `out`. *)
let write_lemma (#t: Type0) (k: Ghost.erased string) (out: ref t) (v: t) (s: forevery_values (d_out k out))
: Lemma (
    let s1 = mk_singleton_value k (pts_to out #1.0R) v in
    s1 (Ghost.reveal k) == v /\
    S.weaken_update (d_out k out) (d_out k out) () s s1 (Ghost.reveal k) == s1 (Ghost.reveal k))
= let s1 = mk_singleton_value k (pts_to out #1.0R) v in
  S.mk_singleton_value_eq k (pts_to out #1.0R) v;
  S.weaken_update_in (d_out k out) (d_out k out) () s s1 k

let store_value_tn (tn: string) (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (x: U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec tn (def'__Store k out ()) pos x s with
    | S.VOk s' -> s' (Ghost.reveal k) == x
    | _ -> False)
= write_lemma k out x s;
  assert (match I.as_value_spec tn (def'__Store k out ()) pos x s with
    | S.VOk s' -> s' (Ghost.reveal k) == x
    | _ -> False) by (unfold_value_spec (); T.smt ())

let store_value k out pos x s = store_value_tn "Store" k out pos x s

let store_correct k out i s =
  I.as_vspec_value_spec "Store" (def'__Store k out ()) i s;
  match P.parse (I.as_parser (def'__Store k out ())) i.S.rest with
  | None -> ()
  | Some (x, _) -> store_value k out (S.venv i) x s

let pos_value k out pos v s =
  VS.vsize_UINT16 (fst v);
  assert_norm (pow2 32 == 4294967296);
  write_lemma k out (U32.uint_to_t ((pos.S.a_start + 2) % pow2 32)) s;
  assert (match I.as_value_spec "Pos" (def'__Pos k out ()) pos v s with
    | S.VOk s' -> s' (Ghost.reveal k) == U32.uint_to_t ((pos.S.a_start + 2) % pow2 32)
    | _ -> False) by (unfold_value_spec (); T.smt ())

let check_value k out pos v s =
  write_lemma k out (fst v) s;
  assert (match I.as_value_spec "Check" (def'__Check k out ()) pos v s with
    | S.VOk s' -> fst v <> 0ul /\ s' (Ghost.reveal k) == fst v
    | S.VErr -> fst v == 0ul) by (unfold_value_spec (); T.smt ())

(* `Store` as an array element: its value spec weakened to the state of `Arr`. *)
let store_elem (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (x: U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec_weaken "_Store" (def'__Store k out ()) (d_out k out) () pos x s with
    | S.VOk s' -> s' (Ghost.reveal k) == x
    | _ -> False)
= let s0 = mk_proj_value s (d_out k out) () in
  store_value_tn "_Store" k out pos x s0;
  match I.as_value_spec "_Store" (def'__Store k out ()) pos x s0 with
  | S.VOk s1 -> S.weaken_update_in (d_out k out) (d_out k out) () s s1 k
  | _ -> ()

let rec last_stored
  (#nz: bool) (#wk: P.weak_kind) (#pk: P.parser_kind nz wk) (p: P.parser pk U32.t)
  (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (l: list U32.t) (s: forevery_values (d_out k out))
: Lemma
  (ensures (match VS.vs_list p (I.as_value_spec_weaken "_Store" (def'__Store k out ()) (d_out k out) ()) pos l s with
    | S.VOk s' -> (match l with [] -> s' == s | _ -> s' (Ghost.reveal k) == List.Tot.last l)
    | _ -> False))
  (decreases l)
= match l with
  | [] -> ()
  | x :: tl ->
    store_elem k out pos x s;
    match I.as_value_spec_weaken "_Store" (def'__Store k out ()) (d_out k out) () pos x s with
    | S.VOk s1 -> last_stored p k out (S.aenv_adv pos (VS.vsize p x)) tl s1
    | _ -> ()

let arr_aux
  (#nz: bool) (#wk: P.weak_kind) (#pk: P.parser_kind nz wk) (p: P.parser pk U32.t)
  (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (l: P.nlist 8ul U32.t) (s: forevery_values (d_out k out))
: Lemma (match VS.vs_nlist 8ul p (I.as_value_spec_weaken "_Store" (def'__Store k out ()) (d_out k out) ()) pos l s with
    | S.VOk s' -> (match VS.nlist_as_list l with
      | [] -> s' == s
      | l' -> s' (Ghost.reveal k) == List.Tot.last l')
    | _ -> False)
= VS.vs_nlist_eq 8ul p (I.as_value_spec_weaken "_Store" (def'__Store k out ()) (d_out k out) ()) pos l s;
  last_stored p k out pos (VS.nlist_as_list l) s

let arr_value k out pos l s =
  assert (match I.as_value_spec "Arr" (def'__Arr k out ()) pos l s with
    | S.VOk s' -> (match VS.nlist_as_list l with
      | [] -> s' == s
      | l' -> s' (Ghost.reveal k) == List.Tot.last l')
    | _ -> False)
  by (T.norm [delta_only [`%def'__Arr; `%def__Arr; `%dtyp__Store; `%I.coerce; `%I.as_value_spec; `%I.dtyp_as_value_spec;
                          `%I.mk_dtyp_app; `%I.value_spec_of_binding]; zeta; iota; primops];
      T.apply_lemma (`arr_aux))

let ptr_value k out pos v s =
  VS.vsize_UINT16 (fst v);
  write_lemma k out (PM.ptr_at pos.S.a_origin (pos.S.a_start + 2)) s;
  assert (match I.as_value_spec "Ptr" (def'__Ptr k out ()) pos v s with
    | S.VOk s' -> s' (Ghost.reveal k) == PM.ptr_at pos.S.a_origin (pos.S.a_start + 2)
    | _ -> False) by (unfold_value_spec (); T.smt ())

(* The facts SMT needs about a singleton state, for all values. *)
let singleton_lemmas (#t: Type0) (name: string) (state: t -> slprop)
: Lemma (forall (v: t) (s: forevery_values (state_dict_singleton name state)) .
    let s1 = mk_singleton_value name state v in
    s1 name == v /\
    S.weaken_update (state_dict_singleton name state) (state_dict_singleton name state) () s s1 name == s1 name)
= let aux (v: t) (s: forevery_values (state_dict_singleton name state))
  : Lemma (let s1 = mk_singleton_value name state v in
    s1 name == v /\
    S.weaken_update (state_dict_singleton name state) (state_dict_singleton name state) () s s1 name == s1 name)
  = let s1 = mk_singleton_value name state v in
    S.mk_singleton_value_eq name state v;
    S.weaken_update_in (state_dict_singleton name state) (state_dict_singleton name state) () s s1 name
  in
  Classical.forall_intro_2 aux

let log_value k vec pos v s =
  singleton_lemmas "#output" X.___output_state_slprop;
  assert (match I.as_value_spec "Log" (def'__Log k vec ()) pos v s with
    | S.VOk s' -> s' "#output" ==
      snd (X.___spec____Push vec (snd v) (snd (X.___spec____Push vec (fst v) (s "#output"))))
    | _ -> False) by (unfold_value_spec (); T.smt ())

let set_value k out pos x s =
  singleton_lemmas "#output" X.___output_state_slprop;
  assert (match I.as_value_spec "Set" (def'__Set k out ()) pos x s with
    | S.VOk s' -> s' "#output" == X.___spec_set_OPAIR_deref_fst out x (s "#output")
    | _ -> False) by (unfold_value_spec (); T.smt ())

(* Inner has no actions: its validator succeeds if and only if it parses. *)
let inner_ok (i: S.vinput) (x: forevery_values state_dict_empty)
: Lemma (requires (VS.vinput_ok i))
  (ensures (S.VOk? (S.vspec_weaken (I.as_vspec "_Inner" (def'__Inner ())) state_dict_empty () i x) <==>
    Some? (P.parse (I.as_parser (def'__Inner ())) i.S.rest)))
= let x0 = mk_proj_value x state_dict_empty () in
  I.as_vspec_value_spec "_Inner" (def'__Inner ()) i x0;
  I.as_vspec_wf "_Inner" (def'__Inner ());
  match P.parse (I.as_parser (def'__Inner ())) i.S.rest with
  | None -> ()
  | Some (v, _) -> assert (VS.pure_at (I.as_value_spec "_Inner" (def'__Inner ())) (S.venv i) v x0)

(* There is only one value of the empty action state. *)
let empty_values_eq (x1 x2: forevery_values state_dict_empty)
: Lemma (x1 == x2)
= forevery_values_ext state_dict_empty x1 x2

(* Projections and products of action states, at a key. *)
let proj_at (#d: state_dict) (f: forevery_values d) (d': state_dict) (sq: squash (state_dict_weaken_prop d' d))
  (x: string)
: Lemma (requires (state_p d' x))
  (ensures (state_p d x /\ d'.state_values x == d.state_values x /\
    mk_proj_value f d' sq x == coerce_eq #(d.state_values x) #(d'.state_values x) () (f x)))
= reveal_state_dict_weaken_prop ()

let prod_at (#d1 #d2: state_dict) (f1: forevery_values d1) (f2: forevery_values d2)
  (sq: squash (forall x . ~ (d1.state_p x /\ d2.state_p x))) (x: string)
: Lemma (requires (state_p d2 x))
  (ensures ((state_dict_prod d1 d2).state_values x == d2.state_values x /\
    mk_prod_value f1 f2 sq x == coerce_eq #(d2.state_values x) #((state_dict_prod d1 d2).state_values x) () (f2 x)))
= reveal_opaque (`%state_dict_prod) state_dict_prod

(* A probe whose probed type has no action state: the outcome is the head
   of the probe tape, and the tape advances. *)
let probe_alone
  (sp: S.vspec state_dict_empty) (name: string) (state: S.probe_tape -> slprop)
  (sq: squash (forall x . ~ (state_dict_empty.state_p x /\ (state_dict_singleton name state).state_p x)))
  (sq': squash (state_dict_weaken_prop (state_dict_prod state_dict_empty (state_dict_singleton name state)) (state_dict_singleton name state)))
  (e: S.aenv) (s: forevery_values (state_dict_singleton name state)) (x0: forevery_values state_dict_empty)
: Lemma (
    let w : S.probe_tape = s name in
    let o = S.ptape_head w in
    let ok = o.S.p_ok /\ S.VOk? (sp (S.probe_vinput o) x0) in
    match S.vaspec_weaken (S.vaspec_probe_then_validate sp false name state sq) (state_dict_singleton name state) sq' e s with
    | S.VOk s' -> ok /\ s' name == S.ptape_tail w
    | S.VErr -> ~ ok)
= let dc = state_dict_singleton name state in
  let d = state_dict_prod state_dict_empty dc in
  let st = mk_proj_value s d sq' in
  proj_at s d sq' name;
  proj_at st dc () name;
  Classical.forall_intro (empty_values_eq x0);
  let w : S.probe_tape = s name in
  let w' = mk_singleton_value name state (S.ptape_tail w) in
  S.mk_singleton_value_eq name state (S.ptape_tail w);
  match sp (S.probe_vinput (S.ptape_head w)) (mk_proj_value st state_dict_empty ()) with
  | S.VOk sx' ->
    prod_at sx' w' () name;
    S.weaken_update_in d dc sq' s (mk_prod_value sx' w' ()) name
  | _ -> ()

let probed_value k dest pos x s =
  let w : S.probe_tape = s (Ghost.reveal k) in
  let x0 = mk_proj_value s state_dict_empty () in
  inner_ok (S.probe_vinput (S.ptape_head w)) x0;
  probe_alone (S.vspec_weaken (I.as_vspec "_Inner" (def'__Inner ())) state_dict_empty ()) k
    (A.copy_buffer_state #B.copy_buffer_t #B.base_t #B.len_t #B.pos_t #B.input_stream_buffer #B.copy_buffer_buffer dest)
    () () pos s x0;
  assert (
    let w : S.probe_tape = s (Ghost.reveal k) in
    let o = S.ptape_head w in
    let ok = o.S.p_ok /\ Some? (P.parse (I.as_parser (def'__Inner ())) o.S.p_bytes) in
    match I.as_value_spec "Probed" (def'__Probed k dest ()) pos x s with
    | S.VOk s' -> ok /\ s' (Ghost.reveal k) == S.ptape_tail w
    | S.VErr -> ~ ok)
  by (T.norm [delta_only [`%def'__Probed; `%def__Probed; `%dtyp__Inner; `%I.coerce;
                          `%I.as_value_spec; `%I.dtyp_as_value_spec;
                          `%I.t_probe_then_validate_alt_gen; `%I.t_probe_then_validate_gen;
                          `%I.mk_dtyp_app; `%I.dtyp_as_vspec; `%I.spec_of_binding];
              zeta; iota; primops];
      T.smt ())

(* Non-vacuity: the spec is precise enough to rule out wrong behaviours. Each
   of the following claims is false, so its proof, which is the same as that
   of the corresponding true claim above, must fail. *)
#push-options "--z3rlimit 20"

(* Store does not store a constant. *)
[@@expect_failure [19]]
let store_value_wrong (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (x: U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Store" (def'__Store k out ()) pos x s with
    | S.VOk s' -> s' (Ghost.reveal k) == 0ul
    | _ -> False)
= write_lemma k out x s;
  assert (match I.as_value_spec "Store" (def'__Store k out ()) pos x s with
    | S.VOk s' -> s' (Ghost.reveal k) == 0ul
    | _ -> False) by (unfold_value_spec (); T.smt ())

(* field_pos_32 is not the position where the annotated field ends. *)
[@@expect_failure [19]]
let pos_value_wrong (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (v: U16.t & U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Pos" (def'__Pos k out ()) pos v s with
    | S.VOk s' -> s' (Ghost.reveal k) == U32.uint_to_t ((pos.S.a_start + 6) % pow2 32)
    | _ -> False)
= VS.vsize_UINT16 (fst v);
  assert_norm (pow2 32 == 4294967296);
  write_lemma k out (U32.uint_to_t ((pos.S.a_start + 2) % pow2 32)) s;
  assert (match I.as_value_spec "Pos" (def'__Pos k out ()) pos v s with
    | S.VOk s' -> s' (Ghost.reveal k) == U32.uint_to_t ((pos.S.a_start + 6) % pow2 32)
    | _ -> False) by (unfold_value_spec (); T.smt ())

(* The failing :check of Check is not ignored. *)
[@@expect_failure [19]]
let check_value_wrong (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (v: U32.t & U32.t) (s: forevery_values (d_out k out))
: Lemma (S.VOk? (I.as_value_spec "Check" (def'__Check k out ()) pos v s))
= write_lemma k out (fst v) s;
  assert (S.VOk? (I.as_value_spec "Check" (def'__Check k out ()) pos v s))
    by (unfold_value_spec (); T.smt ())

(* Arr does not store its first element. *)
[@@expect_failure [19]]
let arr_value_wrong (k: Ghost.erased string) (out: ref U32.t)
  (pos: S.aenv) (l: P.nlist 8ul U32.t) (s: forevery_values (d_out k out))
: Lemma (match I.as_value_spec "Arr" (def'__Arr k out ()) pos l s with
    | S.VOk s' -> (match VS.nlist_as_list l with
      | [] -> s' == s
      | l' -> s' (Ghost.reveal k) == List.Tot.hd l')
    | _ -> False)
= arr_value k out pos l s

(* The calls of Log are not reordered (the extern specs have no laws.) *)
[@@expect_failure [19]]
let log_value_wrong (k: Ghost.erased string) (vec: ref X.___Vec)
  (pos: S.aenv) (v: U32.t & U32.t) (s: forevery_values X.___output_state)
: Lemma (match I.as_value_spec "Log" (def'__Log k vec ()) pos v s with
    | S.VOk s' -> s' "#output" ==
      snd (X.___spec____Push vec (fst v) (snd (X.___spec____Push vec (snd v) (s "#output"))))
    | _ -> False)
= singleton_lemmas "#output" X.___output_state_slprop;
  assert (match I.as_value_spec "Log" (def'__Log k vec ()) pos v s with
    | S.VOk s' -> s' "#output" ==
      snd (X.___spec____Push vec (fst v) (snd (X.___spec____Push vec (snd v) (s "#output"))))
    | _ -> False) by (unfold_value_spec (); T.smt ())

(* The setter of Set is not ignored. *)
[@@expect_failure [19]]
let set_value_wrong (k: Ghost.erased string) (out: SpecTest.ExternalTypes.p____OPAIR)
  (pos: S.aenv) (x: U32.t) (s: forevery_values X.___output_state)
: Lemma (match I.as_value_spec "Set" (def'__Set k out ()) pos x s with
    | S.VOk s' -> s' "#output" == s "#output"
    | _ -> False)
= singleton_lemmas "#output" X.___output_state_slprop;
  assert (match I.as_value_spec "Set" (def'__Set k out ()) pos x s with
    | S.VOk s' -> s' "#output" == s "#output"
    | _ -> False) by (unfold_value_spec (); T.smt ())

(* The probed bytes are validated: a successful probe is not enough. *)
[@@expect_failure [19]]
let probed_value_wrong (k: Ghost.erased string) (dest: B.copy_buffer_t)
  (pos: S.aenv) (x: U64.t) (s: forevery_values (d_probe k dest))
: Lemma (
    let o = S.ptape_head (s (Ghost.reveal k)) in
    o.S.p_ok ==> S.VOk? (I.as_value_spec "Probed" (def'__Probed k dest ()) pos x s))
= probed_value k dest pos x s
#pop-options
