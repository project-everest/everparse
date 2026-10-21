module ArithParse.Impl
#lang-pulse
include ArithParse.Spec
open LowParse.Spec.Base
open LowParse.Pulse.Base
open LowParse.Pulse.Combinators
open LowParse.Pulse.Int
open LowParse.Pulse.VCList
open LowParse.Pulse.Recursive
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Slice

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module PM = Pulse.Lib.SeqMatch

(* Validation *)

inline_for_extraction noextract [@@noextract_to "krml"]
let validate_header_rhs (lhs: U8.t) : validator (parse_header_rhs lhs) =
  ifthenelse_validator
    (parse_header_rhs lhs)
    (lhs = 255uy)
    (fun _ -> validate_weaken parse_header_rhs_kind (validate_synth (validate_u64) (HValue #lhs ())))
    (fun _ -> validate_weaken parse_header_rhs_kind (validate_synth validate_empty (HUnit #lhs ())))

inline_for_extraction noextract [@@noextract_to "krml"]
let validate_header : validator parse_header =
  validate_dtuple2 validate_u8 (leaf_reader_of_reader read_u8) validate_header_rhs

inline_for_extraction noextract [@@noextract_to "krml"]
let jump_header_rhs (lhs: U8.t) : jumper (parse_header_rhs lhs) =
  ifthenelse_jumper
    (parse_header_rhs lhs)
    (lhs = 255uy)
    (fun _ -> jump_ext (jump_synth jump_u64 (HValue #lhs ())) (parse_header_rhs lhs))
    (fun _ -> jump_ext (jump_synth jump_empty (HUnit #lhs ())) (parse_header_rhs lhs))

inline_for_extraction noextract [@@noextract_to "krml"]
let jump_header : jumper parse_header =
  jump_dtuple2 jump_u8 (leaf_reader_of_reader read_u8) jump_header_rhs

module SZ = FStar.SizeT

#push-options "--ifuel 4"

module Trade = Pulse.Lib.Trade.Util

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_validate_count_payload () : validate_recursive_step_count #_ serialize_expr_param =
  (#va: _)
  (#pm: _)
  (a: _)
  (bound: _)
  (#rem: _)
  (prem: _)
{
  parse_header_eq ();
  pts_to_serialized_ext_trade (serializer_of_tot_serializer tot_serialize_header) serialize_header a;
  let a1 = dtuple2_dfst _ jump_u8 _ a;
  Trade.trans _ _ (pts_to_serialized (serializer_of_tot_serializer tot_serialize_header) a #pm va);
  let kd = leaf_reader_of_reader read_u8 a1;
  Trade.elim _ _;
  if (kd = 255uy) {
    prem := 0sz;
    false
  }
  else if (kd = 254uy) {
    prem := 2sz;
    false
  } else {
    let len16 = FStar.Int.Cast.uint8_to_uint16 kd;
    prem := SZ.uint16_to_sizet len16;
    false
  }
}

let validate_expr : validator tot_parse_expr =
  [@@inline_let] let _ = parse_header_eq () in
  validate_recursive serialize_expr_param validate_header (impl_validate_count_payload ())

inline_for_extraction noextract [@@noextract_to "krml"]
fn impl_jump_count_payload () : jump_recursive_step_count #_ serialize_expr_param =
  (#va: _)
  (#pm: _)
  (a: _)
  (bound: _)
{
  parse_header_eq ();
  pts_to_serialized_ext_trade (serializer_of_tot_serializer tot_serialize_header) serialize_header a;
  let a1 = dtuple2_dfst _ jump_u8 _ a;
  Trade.trans _ _ (pts_to_serialized (serializer_of_tot_serializer tot_serialize_header) a #pm va);
  let kd = leaf_reader_of_reader read_u8 a1;
  Trade.elim _ _;
  if (kd = 255uy) {
    0sz;
  }
  else if (kd = 254uy) {
    2sz;
  } else {
    let len16 = FStar.Int.Cast.uint8_to_uint16 kd;
    SZ.uint16_to_sizet len16;
  }
}

let jump_expr : jumper tot_parse_expr =
  [@@inline_let] let _ = parse_header_eq () in
  jump_recursive serialize_expr_param jump_header (impl_jump_count_payload ())

(* Low-level data structure *)

noeq
type expr_base_t =
| EUPlus: (count: U8.t) -> (payload: with_perm (S.slice U8.t)) -> expr_base_t
| EUMinus: (fst: with_perm (S.slice U8.t)) -> (snd: with_perm (S.slice U8.t)) -> expr_base_t
| EValue of U64.t

noeq
type expr_t =
| EBase of expr_base_t // or value
| EPlus of with_perm (S.slice expr_t)
| EMinus: (fst: with_perm (ref expr_t)) -> (snd: with_perm (ref expr_t)) -> expr_t

(* Separation-logic predicate *)

[@@pulse_unfold]
let rel_base_EUPlus
  (count: U8.t)
  (pl: with_perm (S.slice U8.t))
  (n: nat)
  (sq: squash (n < 254))
  (l: nlist n expr)
: Tot slprop
= vmatch_and_const (pure (eq2 #nat n (U8.v count))) (pts_to_serialized_with_perm (serialize_nlist n serialize_expr)) pl l // FIXME: WHY WHY WHY WHY WHY WHY do I need this F*ing annotation on eq2? I wasted HOURS on this

let rel_base
  (base: expr_base_t)
  (e: expr)
: Tot slprop
= match base, e with
  | EUPlus count pl, Plus n sq l -> rel_base_EUPlus count pl n sq l
  | EUMinus fst snd, Minus v -> vmatch_pair (pts_to_serialized_with_perm serialize_expr) (pts_to_serialized_with_perm serialize_expr) (fst, snd) v
  | EValue vl, Value vh -> eq_as_slprop U64.t vl vh
  | _ -> pure False

(* Depth-indexed relation, following the "depth-indexed open recursion" pattern
   used by the CBOR serializer (EverParse PR #302 / #291): `d` is a bound on the
   *inline* depth of the low-level value, i.e. on how many pointer/slice
   indirections `low` may still contain before reaching a serialized `EBase`
   leaf. Since `rel_d` recurses on `d` (rather than structurally on `high`), the
   recursive writer below can be given `decreases d`, and the well-founded
   `nlist_match_slice_wf` / `vmatch_ref_wf` combinators are no longer needed. *)

noextract [@@noextract_to "krml"]
let nat_pred (n: nat) : Tot nat = if n = 0 then 0 else n - 1

noextract [@@noextract_to "krml"]
let epred (n: Ghost.erased nat) : Tot (Ghost.erased nat) =
  Ghost.hide (nat_pred (Ghost.reveal n))

let rel_base_cases_bool
  (low: expr_base_t)
  (high: expr)
: GTot bool
  (decreases high)
= match low, high with
  | EUPlus _ _, Plus _ _ _
  | EUMinus _ _, Minus _
  | EValue _, Value _
    -> true
  | _ -> false

ghost fn rel_base_cases
  (low: expr_base_t)
  (high: expr)
requires rel_base low high
ensures rel_base low high ** pure (rel_base_cases_bool low high == true)
{
  let g = rel_base_cases_bool low high;
  if (g) {
    ()
  } else {
    rewrite (rel_base low high) as (pure False);
    rewrite (pure False) as (rel_base low high)
  }
}

let rel_d_body
  (recf: (expr_t -> expr -> slprop))
  (low: expr_t)
  (high: expr)
: Tot slprop
= match low, high with
  | EBase vb, l -> rel_base vb l
  | EPlus s, Plus cnt _ l -> nlist_match_slice0 recf cnt s l
  | EMinus pl1 pl2, Minus ph -> vmatch_pair (vmatch_ref recf) (vmatch_ref recf) (pl1, pl2) ph
  | _ -> pure False

(* NOTE: `rel_d` must be defined with arity 1 and with the recursive call
   `rel_d (d - 1)` fully applied: a *partial* application of a recursive
   function is encoded to SMT as an opaque closure, which would make the
   defining equations below unprovable. *)

let rec rel_d
  (d: nat)
: Tot (expr_t -> expr -> slprop)
  (decreases d)
= if d = 0
  then (fun low high -> match low with
    | EBase vb -> rel_base vb high
    | _ -> pure False
  )
  else rel_d_body (rel_d (d - 1))

// from now on, rel_d should be opaque

let rel_d_eq_base
  (d: nat)
  (vb: expr_base_t)
  (high: expr)
: Lemma
  (ensures (rel_d d (EBase vb) high == rel_base vb high))
  [SMTPat (rel_d d (EBase vb) high)]
= ()

let rel_d_eq_plus
  (d: nat)
  (s: with_perm (S.slice expr_t))
  (cnt: nat)
  (sq: squash (cnt < 254))
  (l: nlist cnt expr)
: Lemma
  (requires (d > 0))
  (ensures (rel_d d (EPlus s) (Plus cnt sq l) == nlist_match_slice0 (rel_d (d - 1)) cnt s l))
= ()

let rel_d_eq_minus
  (d: nat)
  (pl1 pl2: with_perm (ref expr_t))
  (ph: (expr & expr))
: Lemma
  (requires (d > 0))
  (ensures (rel_d d (EMinus pl1 pl2) (Minus ph) ==
    vmatch_pair (vmatch_ref (rel_d (d - 1))) (vmatch_ref (rel_d (d - 1))) (pl1, pl2) ph))
= ()

let rel_d_cases_bool
  (d: nat)
  (low: expr_t)
  (high: expr)
: GTot bool
= match low, high with
  | EPlus _, Plus _ _ _
  | EMinus _ _, Minus _ -> d > 0
  | EBase _, _ -> true
  | _ -> false

let rel_d_eq_false
  (d: nat)
  (low: expr_t)
  (high: expr)
: Lemma
  (requires (rel_d_cases_bool d low high == false))
  (ensures (rel_d d low high == pure False))
= ()

ghost fn rel_d_cases
  (d: nat)
  (low: expr_t)
  (high: expr)
requires rel_d d low high
ensures rel_d d low high ** pure (rel_d_cases_bool d low high == true)
{
  let g = rel_d_cases_bool d low high;
  if (g) {
    ()
  } else {
    rel_d_eq_false d low high;
    rewrite (rel_d d low high) as (pure False);
    rewrite (pure False) as (rel_d d low high)
  }
}

(* Serialization *)

let write_header : l2r_leaf_writer serialize_header =
  l2r_leaf_write_dtuple2
    (l2r_leaf_write_u8 ())
    ()
    (fun lhs ->
      l2r_leaf_writer_ifthenelse
        (serialize_header_rhs lhs)
        (lhs = 255uy)
        (fun _ -> l2r_leaf_writer_ext (l2r_leaf_write_synth' (l2r_leaf_write_u64 ()) (HValue ()) (HValue?.v)) (serialize_header_rhs lhs))
        (fun _ -> l2r_leaf_writer_ext (l2r_leaf_write_synth' (l2r_leaf_write_empty) (HUnit ()) (HUnit?.v)) (serialize_header_rhs lhs))
    )

ghost
fn rewrite_with_trade_squash
  (#[FStar.Tactics.exact (`emp_inames)] is:inames)
  (p1 p2: slprop)
  (sq: squash (p1 == p2))
  requires p1
  ensures p2 ** (Trade.trade #is p2 p1)
{
  Trade.rewrite_with_trade #is p1 p2
}

inline_for_extraction noextract [@@noextract_to "krml"]
let get_header_type
  (h: header)
: Tot U8.t
= match h with
  | (| ty, _ |) -> ty

ghost fn unfold_vmatch_and_const
  (#tl #th: Type0)
  (const: slprop)
  (vmatch: tl -> th -> slprop)
  (xl: tl)
  (xh: th)
requires
  vmatch_and_const const vmatch xl xh
ensures
  const ** vmatch xl xh **
  Trade.trade (const ** vmatch xl xh) (vmatch_and_const const vmatch xl xh)
{
  Trade.rewrite_with_trade
    (vmatch_and_const const vmatch xl xh)
    (const ** vmatch xl xh)
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn write_expr_base_payload_plus
  (xh1: header)
  (sq255: squash (get_header_type xh1 = 255uy == false))
  (sq254: squash (get_header_type xh1 = 254uy == false))
: vmatch_lens #_ #_ #_ (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
  (pts_to_serialized_with_perm (serialize_nlist (count_payload xh1) serialize_expr))
= (x1': _)
  (x: _)
{
  let y' : Ghost.erased expr = Ghost.hide (synth_expr (| xh1, Ghost.reveal x |));
  Trade.rewrite_with_trade
    (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1 x1' x)
    (rel_base x1' y');
  rel_base_cases _ _;
  norewrite let EUPlus count pl = x1';
  Trade.rewrite_with_trade
    (rel_base x1' y')
    (rel_base_EUPlus count pl (count_payload xh1) () x);
  Trade.trans _ (rel_base x1' y') _;
  unfold_vmatch_and_const (pure (eq2 #nat (count_payload xh1) (U8.v count))) (pts_to_serialized_with_perm (serialize_nlist (count_payload xh1) serialize_expr)) pl x;
  Trade.trans _ _ (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1 x1' x);
  Trade.elim_hyp_l _ _ _;
  pl
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn write_expr_base_payload_minus
  (xh1: header)
  (sq255: squash (get_header_type xh1 = 255uy == false))
  (sq254: squash (get_header_type xh1 = 254uy == true))
: vmatch_lens #_ #_ #_ (vmatch_synth (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
      (pair_to_nlist expr))
  (vmatch_pair (pts_to_serialized_with_perm serialize_expr)
      (pts_to_serialized_with_perm serialize_expr))
=
  (x1': _)
  (x: _)
{
  let y' : Ghost.erased expr = (synth_expr (| xh1, pair_to_nlist expr (Ghost.reveal x) |));
  Trade.rewrite_with_trade
    (vmatch_synth (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1) (pair_to_nlist expr) x1' x)
    (rel_base x1' y');
  rel_base_cases _ _;
  norewrite let EUMinus fs sn = x1';
  Trade.rewrite_with_trade
    (rel_base x1' y')
    (vmatch_pair (pts_to_serialized_with_perm serialize_expr) (pts_to_serialized_with_perm serialize_expr) (fs, sn) x);
  Trade.trans _ (rel_base x1' y') _;
  (fs, sn)
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_base_payload'
  (xh1: header)
: l2r_writer (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
    (serialize_nlist 
      (count_payload xh1)
      serialize_expr
    )
= l2r_writer_ifthenelse
    (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
    (serialize_nlist 
      (count_payload xh1)
      serialize_expr
    )
    (get_header_type xh1 = 255uy)
    (fun _ ->
      [@@inline_let] let _ = LowParse.Spec.VCList.parse_nlist_nil_as_synth_eq parse_expr in
      l2r_writer_ext
        (l2r_write_synth_recip
          _
          (empty_to_nlist expr) (empty_to_nlist_recip expr)
          (l2r_write_empty _)
        )
        _
    )
    (fun _ -> l2r_writer_ifthenelse
      (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
      (serialize_nlist 
        (count_payload xh1)
        serialize_expr
      )
      (get_header_type xh1 = 254uy)
      (fun _ ->
        [@@inline_let] let _ = LowParse.Spec.VCList.parse_nlist_pair_as_synth_eq parse_expr in
        l2r_writer_ext
          (l2r_write_synth_recip
            (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
            (pair_to_nlist expr) (pair_to_nlist_recip expr)
            (l2r_writer_lens
              (write_expr_base_payload_minus xh1 () ())
              (l2r_write_nondep_then_direct
                (l2r_write_copy serialize_expr)
                ()
                (l2r_write_copy serialize_expr)
              )
            )
          )
          (serialize_nlist 
            (count_payload xh1)
            serialize_expr
          )
      )
      (fun _ ->
        l2r_writer_lens
          (write_expr_base_payload_plus xh1 () ())
          (l2r_write_copy _)
      )
    )

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_base_payload
  (xh1: header)
: l2r_writer (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh1)
      (spec_serialize_recursive_payload serialize_expr_param xh1)
= l2r_writer_ext
    (write_expr_base_payload' xh1)
    (spec_serialize_recursive_payload serialize_expr_param xh1)

inline_for_extraction noextract [@@noextract_to "krml"]
let mk_header
  (lhs: U8.t)
  (rhs: header_rhs lhs)
: Tot header
= (| lhs, rhs |)

fn expr_base_get_header
    (xl: expr_base_t)
    (xh:
      erased (dtuple2 header
            (parse_recursive_payload_t expr
                header
                count_payload))
    )
requires
      (vmatch_synth rel_base synth_expr xl xh)
returns res: header
ensures
      (vmatch_synth rel_base synth_expr xl xh ** pure (res == dfst xh))
{
  unfold (vmatch_synth rel_base synth_expr xl xh);
  let xh' = Ghost.hide (synth_expr xh);
  rewrite (rel_base xl (synth_expr xh)) as (rel_base xl xh');
  rel_base_cases xl xh';
  match xl {
    norewrite EUPlus count payload -> {
      let n = Ghost.hide (Plus?.n xh');
      let l : Ghost.erased (nlist (Ghost.reveal n) expr) = Ghost.hide (Plus?.l xh');
      Trade.rewrite_with_trade (rel_base xl xh') (rel_base_EUPlus count payload n () l);
      unfold (vmatch_and_const (pure (eq2 #nat n (U8.v count))) (pts_to_serialized_with_perm (serialize_nlist n serialize_expr)) payload l);
      fold (vmatch_and_const (pure (eq2 #nat n (U8.v count))) (pts_to_serialized_with_perm (serialize_nlist n serialize_expr)) payload l);
      Trade.elim _ _;
      rewrite (rel_base xl xh') as (rel_base xl (synth_expr xh));
      fold (vmatch_synth rel_base synth_expr xl xh);
      mk_header count (HUnit #count () ())
    }
    norewrite EValue v -> {
      let v' : Ghost.erased U64.t = Value?._0 xh';
      Trade.rewrite_with_trade (rel_base xl xh') (eq_as_slprop U64.t v v');
      unfold (eq_as_slprop U64.t v v');
      fold (eq_as_slprop U64.t v v');
      Trade.elim _ _;
      rewrite (rel_base xl xh') as (rel_base xl (synth_expr xh));
      fold (vmatch_synth rel_base synth_expr xl xh);
      mk_header 255uy (HValue () v)
    }
    norewrite EUMinus _ _ -> {
      rewrite (rel_base xl xh') as (rel_base xl (synth_expr xh));
      fold (vmatch_synth rel_base synth_expr xl xh);
      mk_header 254uy (HUnit () ())
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_base_dtuple2 : l2r_writer (vmatch_synth rel_base synth_expr)
  (serialize_dtuple2 serialize_header (spec_serialize_recursive_payload serialize_expr_param))
= l2r_write_dtuple2_recip_explicit_header
    write_header
    expr_base_get_header
    ()
    write_expr_base_payload

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_base' : l2r_writer #expr_base_t #expr rel_base #_ #_ (serialize_expr') =
  l2r_write_synth_recip _ synth_expr synth_expr_recip write_expr_base_dtuple2

let write_expr_base : l2r_writer #expr_base_t #expr rel_base #_ #_ (serialize_expr) =
  [@@inline_let] let _ = parse_expr_eq () in
  l2r_writer_ext write_expr_base' _

inline_for_extraction noextract [@@noextract_to "krml"]
fn write_expr_rec_base
  (d: Ghost.erased nat)
: vmatch_lens #_ #_ #_ (vmatch_with_cond (rel_d d) EBase?) rel_base
= (x1': _)
  (x: _)
{
  vmatch_with_cond_elim_trade (rel_d d) EBase? x1' x;
  rel_d_cases _ _ _;
  norewrite let EBase res = x1';
  Trade.rewrite_with_trade
    (rel_d d x1' x)
    (rel_base res x);
  Trade.trans _ (rel_d d x1' x) _;
  res
}

ghost fn vmatch_synth_elim_trade
  (#tl: Type0)
  (#th1 #th2: Type0)
  (vmatch: tl -> th1 -> slprop)
  (f21: th2 -> GTot th1)
  (xh: tl)
  (xl2: th2)
requires
  vmatch_synth vmatch f21 xh xl2
ensures
  vmatch xh (f21 xl2) **
  Trade.trade
    (vmatch xh (f21 xl2))
    (vmatch_synth vmatch f21 xh xl2)
{
  Trade.rewrite_with_trade
    (vmatch_synth vmatch f21 xh xl2)
    (vmatch xh (f21 xl2))
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn write_expr_rec_not_base_payload_plus_lens
  (d: Ghost.erased nat)
  (xh1: header)
  (sqplus: squash (get_header_type xh1 = 254uy == false))
: vmatch_lens #_ #_ #_ (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1)
  (nlist_match_slice0 (rel_d (epred d)) (count_payload xh1))
=
  (x1': _)
  (x: _)
{
  vmatch_dep_proj2_elim_trade (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1 x1' x;
  vmatch_synth_elim_trade (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr x1' (| xh1, Ghost.reveal x |);
  Trade.trans _ _ (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1 x1' x);
  vmatch_with_cond_elim_trade (rel_d d) (pnot EBase?) x1' (synth_expr (| xh1, Ghost.reveal x |));
  Trade.trans _ _ (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1 x1' x);
  rel_d_cases _ _ _;
  norewrite let EPlus s = x1';
  rel_d_eq_plus (Ghost.reveal d) s (count_payload xh1) () x;
  Trade.rewrite_with_trade
    (rel_d d x1' (synth_expr (| xh1, Ghost.reveal x |)))
    (nlist_match_slice0 (rel_d (epred d)) (count_payload xh1) s x);
  Trade.trans _ (rel_d d x1' (synth_expr (| xh1, Ghost.reveal x |))) _;
  s
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec_not_base_payload_plus
  (d: Ghost.erased nat)
  (w: l2r_writer (rel_d (epred d)) serialize_expr)
  (xh1: header)
  (sqplus: squash (get_header_type xh1 = 254uy == false))
: l2r_writer (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1
      )
      (spec_serialize_recursive_payload serialize_expr_param xh1)
= l2r_writer_ext
    (l2r_writer_lens
      (write_expr_rec_not_base_payload_plus_lens d xh1 sqplus)
      (l2r_write_nlist_as_slice0 (rel_d (epred d)) serialize_expr w (count_payload xh1))
    )
    _

inline_for_extraction noextract [@@noextract_to "krml"]
fn write_expr_rec_not_base_payload_minus_lens
  (d: Ghost.erased nat)
  (xh1: header)
  (sqplus: squash (get_header_type xh1 = 254uy == true))
: vmatch_lens #_ #_ #_ (vmatch_synth (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1)
      (pair_to_nlist expr))
  (vmatch_pair (vmatch_ref (rel_d (epred d))) (vmatch_ref (rel_d (epred d))))
= (x1': _)
  (x': _)
{
  vmatch_synth_elim_trade (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1)
      (pair_to_nlist expr) _ _;
  vmatch_dep_proj2_elim_trade (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1 _ _;
  Trade.trans _ _ (vmatch_synth (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1)
      (pair_to_nlist expr) _ _);
  vmatch_synth_elim_trade (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr _ _;
  Trade.trans _ _ (vmatch_synth (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1)
      (pair_to_nlist expr) _ _);
  vmatch_with_cond_elim_trade (rel_d d) (pnot EBase?) _ _;
  Trade.trans _ _ (vmatch_synth (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1)
      (pair_to_nlist expr) _ _);
  rel_d_cases _ _ _;
  norewrite let EMinus fs sn = x1';
  with y' . assert (rel_d d x1' y');
  rel_d_eq_minus (Ghost.reveal d) fs sn (Minus?._0 y');
  Trade.rewrite_with_trade (rel_d d x1' y') (vmatch_pair (vmatch_ref (rel_d (epred d))) (vmatch_ref (rel_d (epred d))) (fs, sn) x');
  Trade.trans _ _ (vmatch_synth (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?))
              synth_expr)
          xh1)
      (pair_to_nlist expr) _ _);
  (fs, sn)
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec_not_base_payload_minus
  (d: Ghost.erased nat)
  (w: l2r_writer (rel_d (epred d)) serialize_expr)
  (xh1: header)
  (sqplus: squash (get_header_type xh1 = 254uy == true))
: l2r_writer (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1
      )
      (spec_serialize_recursive_payload serialize_expr_param xh1)
=
        [@@inline_let] let _ = LowParse.Spec.VCList.parse_nlist_pair_as_synth_eq parse_expr in
        l2r_writer_ext
          (l2r_write_synth_recip
            _
            (pair_to_nlist expr) (pair_to_nlist_recip expr)
            (l2r_writer_lens
              (write_expr_rec_not_base_payload_minus_lens d xh1 ())
              (l2r_write_nondep_then_direct
                (l2r_write_ref w)
                ()
                (l2r_write_ref w)
              )
            )
          )
          (serialize_nlist 
            (count_payload xh1)
            serialize_expr
          )
 
inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec_not_base_payload
  (d: Ghost.erased nat)
  (w: l2r_writer (rel_d (epred d)) serialize_expr)
  (xh1: header)
: l2r_writer (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1
      )
      (spec_serialize_recursive_payload serialize_expr_param xh1)
= l2r_writer_ifthenelse
    (vmatch_dep_proj2 (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr) xh1)
    (spec_serialize_recursive_payload serialize_expr_param xh1)
    (get_header_type xh1 = 254uy)
    (write_expr_rec_not_base_payload_minus d w xh1)
    (write_expr_rec_not_base_payload_plus d w xh1)

fn expr_get_header
    (d: Ghost.erased nat)
    (xl: expr_t)
    (xh:
      erased (dtuple2 header
            (parse_recursive_payload_t expr
                header
                count_payload))
    )
requires
      (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr xl xh)
returns res: header
ensures
      (
          vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr xl xh **
          pure (res == dfst xh))
{
  vmatch_synth_elim_trade
    (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr xl xh;
  vmatch_with_cond_elim_trade (rel_d d) (pnot EBase?) xl (synth_expr xh);
  Trade.trans _ _ (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr xl xh);
  rel_d_cases _ _ _;
  match xl {
    norewrite EPlus s -> {
      let n = Ghost.hide (Plus?.n (synth_expr xh));
      let l = Ghost.hide (Plus?.l (synth_expr xh));
      rel_d_eq_plus (Ghost.reveal d) s n () l;
      Trade.rewrite_with_trade
        (rel_d d xl (synth_expr xh))
        (nlist_match_slice0 (rel_d (epred d)) n s l);
      Trade.trans _ (rel_d d xl (synth_expr xh)) _;
      nlist_match_slice0_elim_trade (rel_d (epred d)) n s l;
      Trade.trans _ _ (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr xl xh);
      S.pts_to_len s.v;
      PM.seq_list_match_length (rel_d (epred d)) _ _;
      let len = S.len s.v;
      Trade.elim _ _;
      let res32 = SZ.sizet_to_uint32 len;
      let res8 = FStar.Int.Cast.uint32_to_uint8 res32;
      mk_header res8 (HUnit () ())
    }
    norewrite EMinus fs sn -> {
      Trade.elim _ _;
      mk_header 254uy (HUnit () ())
    }
  }
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec_not_base_dtuple2
  (d: Ghost.erased nat)
  (w: l2r_writer (rel_d (epred d)) serialize_expr)
:
l2r_writer (vmatch_synth (vmatch_with_cond (rel_d d) (pnot EBase?)) synth_expr)
  (serialize_dtuple2 serialize_header (spec_serialize_recursive_payload serialize_expr_param))
= l2r_write_dtuple2_recip_explicit_header
    write_header
    (expr_get_header d)
    ()
    (write_expr_rec_not_base_payload d w)

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec_not_base'
  (d: Ghost.erased nat)
  (w: l2r_writer (rel_d (epred d)) serialize_expr)
: l2r_writer #expr_t #expr (vmatch_with_cond (rel_d d) (pnot EBase?)) #_ #_ (serialize_expr') =
  l2r_write_synth_recip _ synth_expr synth_expr_recip (write_expr_rec_not_base_dtuple2 d w)

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec_not_base
  (d: Ghost.erased nat)
  (w: l2r_writer (rel_d (epred d)) serialize_expr)
: l2r_writer (vmatch_with_cond (rel_d d) (pnot EBase?)) serialize_expr
= [@@inline_let] let _ = parse_expr_eq () in
  l2r_writer_ext (write_expr_rec_not_base' d w) _

(* The dispatcher that ties the depth to the recursive call: from `rel_d d`
   and the fact that the low-level value is not an `EBase`, we learn `d > 0`,
   which is exactly what is needed to call the recursive writer at depth
   `epred d < d`. *)
inline_for_extraction noextract [@@noextract_to "krml"]
fn write_expr_rec_not_base_d
  (d: Ghost.erased nat)
  (recf: (d': Ghost.erased nat { Ghost.reveal d' < Ghost.reveal d }) -> l2r_writer (rel_d d') serialize_expr)
: l2r_writer #expr_t #expr (vmatch_with_cond (rel_d d) (pnot EBase?)) #_ #_ serialize_expr
= (x': _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  vmatch_with_cond_elim_trade (rel_d d) (pnot EBase?) x' x;
  rel_d_cases _ _ _;
  Trade.elim _ _;
  write_expr_rec_not_base d (recf (epred d)) x' #x out offset #v
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr_rec
  (d: Ghost.erased nat)
  (recf: (d': Ghost.erased nat { Ghost.reveal d' < Ghost.reveal d }) -> l2r_writer (rel_d d') serialize_expr)
: l2r_writer #expr_t #expr (rel_d d) #_ #_ (serialize_expr)
=
  l2r_writer_ifthenelse_low
    _
    serialize_expr
    EBase?
    (l2r_writer_lens
      (write_expr_rec_base d)
      write_expr_base
    )
    (write_expr_rec_not_base_d d recf)

fn rec write_expr
  (d: Ghost.erased nat)
  (x': expr_t)
  (#x: Ghost.erased expr)
  (out: S.slice U8.t)
  (offset: SZ.t)
  (#v: Ghost.erased bytes)
requires
    (pts_to out v ** rel_d d x' x ** pure (
      l2r_writer_for_pre serialize_expr x offset v
    ))
returns res: SZ.t
ensures exists* v' .
  pts_to out v' ** rel_d d x' x ** pure (
  l2r_writer_for_post serialize_expr x offset v res v'
)
decreases (Ghost.reveal d)
{
  write_expr_rec d (fun (d': Ghost.erased nat { Ghost.reveal d' < Ghost.reveal d }) -> write_expr d') x' #x out offset #v
}

inline_for_extraction noextract [@@noextract_to "krml"]
let write_expr' (d: Ghost.erased nat) : l2r_writer (rel_d d) serialize_expr = write_expr d

(* Parsing *)

let read_header : leaf_reader serialize_header =
  leaf_reader_of_reader
    (read_dtuple2
      jump_u8
      read_u8
      (fun lhs ->
        ifthenelse_reader
          (serialize_header_rhs lhs)
          (lhs = 255uy)
          (fun _ -> reader_ext (read_synth' read_u64 (HValue ()) (HValue?.v)) (serialize_header_rhs lhs))
          (fun _ -> reader_ext (read_synth' read_empty (HUnit ()) (HUnit?.v)) (serialize_header_rhs lhs))
      )
    )

inline_for_extraction noextract [@@noextract_to "krml"]
let get_header_value
  (h: header)
  (sq: squash (get_header_type h == 255uy))
: Tot U64.t
= let (| _, HValue _ value |) = h in
  value

inline_for_extraction noextract [@@noextract_to "krml"]
fn value_lens
  (xh: header)
  (sq: squash (get_header_type xh = 255uy == true))
: vmatch_lens #_ #_ #_ vmatch_ignore (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh)
= (pl: _)
  (ph: _)
{
  let value = get_header_value xh ();
  let res = EValue value;
  fold (eq_as_slprop U64.t value value);
  Trade.rewrite_with_trade
    (eq_as_slprop U64.t value value)
    (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh res ph);
  unfold (vmatch_ignore pl (Ghost.reveal ph));
  intro
    (Trade.trade
      (eq_as_slprop U64.t value value)
      (vmatch_ignore pl (Ghost.reveal ph))
    )
    #emp
    fn _
  {
    unfold (eq_as_slprop U64.t value value);
    fold (vmatch_ignore pl (Ghost.reveal ph));
  };
  Trade.trans (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh res ph) _ _;
  res
}

ghost fn vmatch_pair_elim_trade
  (#tl1 #tl2 #th1 #th2: Type0)
  (vmatch1: tl1 -> th1 -> slprop)
  (vmatch2: tl2 -> th2 -> slprop)
  (xl: (tl1 & tl2))
  (xh: (th1 & th2))
requires
  vmatch_pair vmatch1 vmatch2 xl xh
ensures
  vmatch1 (fst xl) (fst xh) ** vmatch2 (snd xl) (snd xh) **
  Trade.trade
    (vmatch1 (fst xl) (fst xh) ** vmatch2 (snd xl) (snd xh))
    (vmatch_pair vmatch1 vmatch2 xl xh)
{
  Trade.rewrite_with_trade
    (vmatch_pair vmatch1 vmatch2 xl xh)
    (vmatch1 (fst xl) (fst xh) ** vmatch2 (snd xl) (snd xh))
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn minus_lens
  (xh: header)
  (sq255: squash (get_header_type xh = 255uy == false))
  (sq254: squash (get_header_type xh = 254uy == true))
: vmatch_lens #(with_perm (S.slice byte) & with_perm (S.slice byte))
  #expr_base_t
  #(parse_recursive_payload_t expr header count_payload xh)
  (vmatch_synth #(with_perm (S.slice byte) & with_perm (S.slice byte))
      #(expr & expr)
      #(parse_recursive_payload_t expr
          header
          count_payload
          xh)
      (vmatch_pair #(with_perm (S.slice byte))
          #(with_perm (S.slice byte))
          #expr
          #expr
          (pts_to_serialized_with_perm #expr
              #(reveal #parser_kind
                  (hide #parser_kind (parse_recursive_kind parse_expr_param.parse_header_kind)))
              #parse_expr
              serialize_expr)
          (pts_to_serialized_with_perm #expr
              #(reveal #parser_kind
                  (hide #parser_kind (parse_recursive_kind parse_expr_param.parse_header_kind)))
              #parse_expr
              serialize_expr))
      (pair_to_nlist_recip expr))
  (vmatch_dep_proj2 #expr_base_t
      #header
      #(parse_recursive_payload_t expr header count_payload)
      (vmatch_synth #expr_base_t
          #expr
          #(parse_recursive_alt_t expr header count_payload)
          rel_base
          synth_expr)
      xh)
= (pl: _)
  (ph: _)
{
  norewrite let (fs, sn) = pl;
  let res = (EUMinus fs sn);
  vmatch_synth_elim_trade _ _ _ _;
  Trade.rewrite_with_trade
    (vmatch_pair (pts_to_serialized_with_perm serialize_expr)
      (pts_to_serialized_with_perm serialize_expr)
      pl (pair_to_nlist_recip expr ph))
    (vmatch_dep_proj2 #expr_base_t
      #header
      #(parse_recursive_payload_t expr header count_payload)
      (vmatch_synth #expr_base_t
          #expr
          #(parse_recursive_alt_t expr header count_payload)
          rel_base
          synth_expr)
      xh res ph);
  Trade.trans 
    _
    (vmatch_pair (pts_to_serialized_with_perm serialize_expr)
      (pts_to_serialized_with_perm serialize_expr)
      pl (pair_to_nlist_recip expr ph))
    _;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
fn plus_lens
  (xh: header)
  (sq255: squash (get_header_type xh = 255uy == false))
  (sq254: squash (get_header_type xh = 254uy == false))
: vmatch_lens #_ #_ #_ (pts_to_serialized_with_perm (serialize_nlist (count_payload xh) serialize_expr))
  (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh
)
= (pl: _)
  (ph: _)
{
  let count = get_header_type xh;
  let res = EUPlus count pl;
  intro
    (Trade.trade
      (pure (eq2 #nat (count_payload xh) (U8.v count)) ** pts_to_serialized_with_perm (serialize_nlist (count_payload xh) serialize_expr) pl ph)
      (pts_to_serialized_with_perm (serialize_nlist (count_payload xh) serialize_expr) pl ph)
    )
    #emp
    fn _
  {
    ()
  };
  Trade.rewrite_with_trade
    (pure (eq2 #nat (count_payload xh) (U8.v count)) ** pts_to_serialized_with_perm (serialize_nlist (count_payload xh) serialize_expr) pl ph)
    (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh res ph);
  Trade.trans (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh res ph) _ _;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let zero_copy_parse_payload
  (xh: header)
: zero_copy_parse (vmatch_dep_proj2 (vmatch_synth rel_base synth_expr) xh)
      (spec_serialize_recursive_payload serialize_expr_param xh)
= zero_copy_parse_ifthenelse
    (get_header_type xh = 255uy)
    (fun _ ->
      zero_copy_parse_lens
        (zero_copy_parse_ignore (spec_serialize_recursive_payload serialize_expr_param xh))
        (value_lens xh ())
    )
    (fun _ ->
      zero_copy_parse_ifthenelse
        (get_header_type xh = 254uy)
        (fun _ ->
          [@@inline_let] let _ = LowParse.Spec.VCList.parse_nlist_pair_as_synth_eq parse_expr in
          zero_copy_parse_ext
            (zero_copy_parse_lens
              (zero_copy_parse_synth
                (zero_copy_parse_nondep_then
                  jump_expr
                  (zero_copy_parse_id serialize_expr)
                  ()
                  (zero_copy_parse_id serialize_expr)
                )
                (pair_to_nlist _) (pair_to_nlist_recip _)
              )
              (minus_lens xh () ())
            )
            (spec_serialize_recursive_payload serialize_expr_param xh)
        )
        (fun _ ->
          zero_copy_parse_ext
            (zero_copy_parse_lens
              (zero_copy_parse_id (serialize_nlist (count_payload xh) serialize_expr))
              (plus_lens xh () ())
            )
            (spec_serialize_recursive_payload serialize_expr_param xh)
        )
    )

inline_for_extraction noextract [@@noextract_to "krml"]
let zero_copy_parse_expr'_as_base : zero_copy_parse rel_base serialize_expr' =
  zero_copy_parse_synth_recip
    synth_expr
    synth_expr_recip
    (read_and_zero_copy_parse_dtuple2
      jump_header
      read_header
      ()
      zero_copy_parse_payload
    )

inline_for_extraction noextract [@@noextract_to "krml"]
fn base_lens (d: Ghost.erased nat) : vmatch_lens #_ #_ #_ rel_base (rel_d d)
= (x1': _) (x: _)
{
  Trade.rewrite_with_trade
    (rel_base x1' x)
    (rel_d d (EBase x1') x);
  EBase x1'
}

inline_for_extraction noextract [@@noextract_to "krml"]
let zero_copy_parse_expr' (d: Ghost.erased nat) : zero_copy_parse (rel_d d) serialize_expr' =
  zero_copy_parse_lens
    zero_copy_parse_expr'_as_base
    (base_lens d)

let zero_copy_parse_expr (d: Ghost.erased nat) : zero_copy_parse (rel_d d) serialize_expr =
  [@@inline_let] let _ = parse_expr_eq () in
  zero_copy_parse_ext
    (zero_copy_parse_expr' d)
    _
