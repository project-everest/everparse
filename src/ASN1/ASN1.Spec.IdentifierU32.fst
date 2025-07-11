module ASN1.Spec.IdentifierU32

open ASN1.Base

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.Int

open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

let byte = U8.t

(* Ref X690 8.1.2 *)

let partial_state_lowerbound (n : nat) =
  pow2 (n * 7)

let lemma_partial_state_lowerbound_mono (n : nat) (m : nat) : Lemma
  (requires m <= n)
  (ensures partial_state_lowerbound m <= partial_state_lowerbound n) = 
  let _ = Math.Lemmas.pow2_le_compat (n * 7) (m * 7) in _

let partial_state_upperbound (n : nat) =
  pow2 ((n + 1) * 7)
  
let lemma_partial_state_upperbound_eq (n : nat) : Lemma (partial_state_upperbound n = partial_state_lowerbound (n + 1)) = _

let partial_state_in_bound (n : nat) (v : nat) =
  partial_state_lowerbound n <= v /\ v < partial_state_upperbound n

let partial_state_bound_separation (n : nat) (v : U32.t) (v' : U32.t) :
  Lemma (requires (U32.v v < partial_state_upperbound n /\ partial_state_lowerbound (n + 1) <= U32.v v'))
        (ensures (U32.v v < U32.v v')) 
= _

let partial_state_bound_f32 (ui : U32.t) : Pure nat
  (requires (0 < U32.v ui))
  (ensures (fun n -> n <= 4 /\ partial_state_in_bound n (U32.v ui)))
= let v = U32.v ui in
  if v < partial_state_upperbound 0 then
    (0)
  else 
    (if v < partial_state_upperbound 1 then
      (1)
    else
      (if v < partial_state_upperbound 2 then
        (2)
      else
        (if v < partial_state_upperbound 3 then
          (3)
        else
          (Math.Lemmas.pow2_le_compat 35 32;
           4))))

#push-options "--z3rlimit 128 --fuel 0 --ifuel 0"

let lemma_partial_state_bound_f32_intro (ui : U32.t) (n : nat) :
  Lemma (requires (partial_state_in_bound n (U32.v ui)))
        (ensures (0 < U32.v ui /\ partial_state_bound_f32 ui = n))
= let v = U32.v ui in
  let _ = 
    Math.Lemmas.pow2_lt_compat 7 0;
    Math.Lemmas.pow2_lt_compat 14 7;
    Math.Lemmas.pow2_lt_compat 21 14;
    Math.Lemmas.pow2_lt_compat 28 21;
    Math.Lemmas.pow2_lt_compat 35 28
  in
  match n with
  | 0 -> _
  | 1 -> _
  | 2 -> _
  | 3 -> _
  | 4 -> _
  | _ -> let _ = Math.Lemmas.pow2_le_compat (n * 7) 35 in
        assert (pow2 35 <= v)

type asn1_partial_id_t = (x : U32.t {0 < U32.v x})

let partial_state_prefixf (state : asn1_partial_id_t) (m : nat) : Pure (asn1_partial_id_t) 
  (requires (m <= partial_state_bound_f32 state))
  (ensures (fun state' -> partial_state_bound_f32 state' = m))
= let n = partial_state_bound_f32 state in
  let delta = U32.mul (U32.uint_to_t (n - m)) 7ul in
  assert (U32.v delta < 32);
  let _ = UInt.shift_right_value_lemma (U32.v state) (U32.v delta) in
  let ret = U32.shift_right state delta in
  assert (U32.v state < partial_state_upperbound n);
  let _ = Math.Lemmas.lemma_div_lt (U32.v state) ((n + 1) * 7) (U32.v delta) in
  assert (U32.v ret < partial_state_upperbound m);
  assert (partial_state_lowerbound n <= U32.v state);
  let _ = Math.Lemmas.pow2_minus (n * 7) (U32.v delta) in
  let _ = Math.Lemmas.lemma_div_le (partial_state_lowerbound n) (U32.v state) (pow2 (U32.v delta)) in
  assert (partial_state_lowerbound m = partial_state_lowerbound n / (pow2 (U32.v delta)));
  assert (U32.v ret = U32.v state / (pow2 (U32.v delta)));
  assert (partial_state_lowerbound m <= U32.v ret);
  let _ = lemma_partial_state_bound_f32_intro ret m in
  ret

let lemma_partial_state_prefixf_val (state : asn1_partial_id_t) (m : nat)
: Lemma (requires (m <= partial_state_bound_f32 state))
        (ensures (U32.v (partial_state_prefixf state m) = U32.v state / (pow2 (((partial_state_bound_f32 state) - m) * 7))))
= let delta = U32.mul (U32.uint_to_t ((partial_state_bound_f32 state) - m)) 7ul in
  let _ = UInt.shift_right_value_lemma (U32.v state) (U32.v delta) in _ 

let partial_state_prefixr (state : asn1_partial_id_t) (state' : asn1_partial_id_t) =
  (let n = partial_state_bound_f32 state in
  let m = partial_state_bound_f32 state' in
  n < m /\
  state = partial_state_prefixf state' n)

let partial_state_prefixr_intro (a : asn1_partial_id_t) (b : nat) (state : asn1_partial_id_t)
: Lemma (requires ((let n = partial_state_bound_f32 a in
                   partial_state_bound_f32 state = n + 1 /\
                   b < pow2 7 /\ (U32.v state) = (U32.v a) * (pow2 7) + b)))
        (ensures (partial_state_prefixr a state))
= let n = partial_state_bound_f32 a in
  let _ = 
    lemma_partial_state_prefixf_val state n;
    Math.Lemmas.lemma_div_plus b (U32.v a) (pow2 7);
    Math.Lemmas.small_div b (pow2 7)
  in
  _

let partial_state_prefixf_trans (state : asn1_partial_id_t) (n' : nat) (n'' : nat) : 
Lemma (requires (n'' <= n' /\ n' <= partial_state_bound_f32 state))
      (ensures (partial_state_prefixf (partial_state_prefixf state n') n'' = partial_state_prefixf state n''))
= let n = partial_state_bound_f32 state in
  let _ = 
    lemma_partial_state_prefixf_val state n';
    lemma_partial_state_prefixf_val state n'';
    lemma_partial_state_prefixf_val (partial_state_prefixf state n') n''
  in
  assert (U32.v (partial_state_prefixf state n'') = U32.v state / (pow2 ((n - n'') * 7)));
  assert (U32.v (partial_state_prefixf (partial_state_prefixf state n') n'') = U32.v state / (pow2 ((n - n') * 7)) / (pow2((n' - n'') * 7)));
  let _ = Math.Lemmas.division_multiplication_lemma (U32.v state) (pow2 ((n - n') * 7)) (pow2 ((n' - n'') * 7)) in
  assert (U32.v (partial_state_prefixf (partial_state_prefixf state n') n'') = U32.v state / ((pow2 ((n - n') * 7)) * (pow2((n' - n'') * 7))));
  let _ = 
    Math.Lemmas.pow2_plus ((n - n') * 7) ((n' - n'') * 7);
    Math.Lemmas.distributivity_add_left (n - n') (n' - n'') 7
  in
  assert ((n - n') * 7 + (n' - n'') * 7 = (n - n' + (n' - n'')) * 7);
  assert (U32.v (partial_state_prefixf (partial_state_prefixf state n') n'') = U32.v state / (pow2 ((n - n'') * 7)))

let partial_state_prefixr_trans (state state' state'' : asn1_partial_id_t)
: Lemma (requires (partial_state_prefixr state state' /\ partial_state_prefixr state' state''))
        (ensures (partial_state_prefixr state state''))
= let n = partial_state_bound_f32 state in
  let n' = partial_state_bound_f32 state' in
  let n'' = partial_state_bound_f32 state'' in
  let _ = partial_state_prefixf_trans state'' n' n in _

let partial_state_prefixr_weaken 
  (state :asn1_partial_id_t) 
  (state' : asn1_partial_id_t {partial_state_prefixr state state'}) 
  (state'' : asn1_partial_id_t {partial_state_prefixr state' state''}) : 
  (s : asn1_partial_id_t {s = state'' /\ partial_state_prefixr state s})
= let _ = partial_state_prefixr_trans state state' state'' in
  state''

#push-options "--fuel 1 --ifuel 0"

let update_state (state :asn1_partial_id_t) (b : byte) : Pure (asn1_partial_id_t)
  (requires (U8.v b < 128 /\ (U32.v state < pow2 25)))
  (ensures (fun state' -> partial_state_bound_f32 state' = (partial_state_bound_f32 state) + 1 /\ partial_state_prefixr state state'))
= let n = partial_state_bound_f32 state in 
  let _ = Math.Lemmas.lemma_mult_lt_right (pow2 7) (U32.v state) (pow2 25) in
  let _ = Math.Lemmas.pow2_plus 25 7 in
  assert (U32.v state * pow2 7 < pow2 32);
  let _ = Math.Lemmas.pow2_lt_compat 28 25 in
  assert (partial_state_bound_f32 state < 4);
  let _ = UInt.shift_left_value_lemma (U32.v state) 7 in
  let _ = Math.Lemmas.pow2_plus ((n + 1) * 7) 7 in
  let a = U32.shift_left state 7ul in
  assert (U32.v a < partial_state_upperbound (n + 1));
  let _ = Math.Lemmas.pow2_plus (n * 7) 7 in
  assert (partial_state_lowerbound (n + 1) <= U32.v a);
  let b = Cast.uint8_to_uint32 b in
  assert (U32.v a % (pow2 7) = 0);
  assert (U32.v b < pow2 7);
  let _ = Math.Lemmas.cancel_mul_mod (U32.v state) (pow2 7) in
  let _ = UInt.logor_disjoint (U32.v a) (U32.v b) 7 in
  let _ = UInt.logor_ge (U32.v a) (U32.v b) in
  let ret = (U32.logor a b) in
  assert (partial_state_in_bound (n + 1) (U32.v ret)); 
  assert (partial_state_bound_f32 ret = n + 1);
  let _ = partial_state_prefixr_intro state (U32.v b) ret in
  ret

let update_state_inj2 (s1 s2 : asn1_partial_id_t)  (b1 b2 : byte) 
: Lemma
  (requires ((U8.v b1 < 128 /\ U8.v b2 < 128) /\ 
             (U32.v s1 < pow2 25) /\
             (U32.v s2 < pow2 25) /\
             update_state s1 b1 = update_state s2 b2))
  (ensures (s1 = s2 /\ b1 = b2))
= assert (s1 = s2);
  let _ = UInt.shift_left_value_lemma (U32.v s1) 7 in
  let _ = Math.Lemmas.cancel_mul_mod (U32.v s1) (pow2 7) in
  let a = UInt.shift_left (U32.v s1) 7 in
  UInt.logor_disjoint a (U8.v b1) 7;
  UInt.logor_disjoint a (U8.v b2) 7;
  assert (U32.v (update_state s1 b1) = UInt.logor a (U8.v b1));
  assert (U32.v (update_state s2 b2) = UInt.logor a (U8.v b2))

let in_bound_32 (i : nat) (v : U32.t) : Lemma
  (requires i <= 2 /\ (U32.v v < partial_state_upperbound i))
  (ensures U32.v v < pow2 25)
= assert (U32.v v < pow2 ((i + 1) * 7));
  let _ = Math.Lemmas.pow2_le_compat 21 ((i + 1) * 7) in
  assert (U32.v v < pow2 21);
  let _ = Math.Lemmas.pow2_lt_compat 25 21 in
  _

let decode_asn1_identifier_class (b : byte { U8.v b <= 3 }) : asn1_id_class_t
= match b with
  | 0uy -> UNIVERSAL
  | 1uy -> APPLICATION
  | 2uy -> CONTEXT_SPECIFIC
  | 3uy -> PRIVATE

let decode_asn1_identifier_class' (buf : byte) : asn1_id_class_t
= let b = U8.shift_right buf 6ul in
  decode_asn1_identifier_class b

let decode_asn1_identifier_flag (b : byte { U8.v b <= 1 }) : asn1_id_flag_t
= match b with
  | 0uy -> PRIMITIVE
  | 1uy -> CONSTRUCTED

let decode_asn1_identifier_flag' (buf : byte) : asn1_id_flag_t
= let b = U8.rem (U8.shift_right buf 5ul) 2uy in
  decode_asn1_identifier_flag b
  
let parse_asn1_identifier_tail_kind = strong_parser_kind 0 0 None

let parse_asn1_identifier_tail (state : asn1_partial_id_t {partial_state_bound_f32 state = 3}) (buf : byte) : 
  parser parse_asn1_identifier_tail_kind (state' : asn1_partial_id_t {partial_state_prefixr state state'})
= if U8.lt buf 128uy then
    if (U32.lt state (U32.uint_to_t (UInt.pow2_n #32 (32 - 7)))) then
      let ret = update_state state buf in
      weaken (parse_asn1_identifier_tail_kind) (parse_ret ret)
    else
      fail_parser (parse_asn1_identifier_tail_kind) _
  else
    fail_parser (parse_asn1_identifier_tail_kind) _

let parse_asn1_identifier_tail_injective (state : asn1_partial_id_t {partial_state_bound_f32 state = 3}) :
Lemma (and_then_cases_injective (parse_asn1_identifier_tail state))
= and_then_cases_injective_intro (parse_asn1_identifier_tail state) (fun x1 x2 b1 b2 ->
    assert (U8.v x1 < 128 /\ U8.v x2 < 128);
    assert (U32.v state < pow2 (32 - 7));
    let _ = Math.Lemmas.pow2_plus (32 - 7) 7 in
    let _ = Math.Lemmas.lemma_mult_lt_right (pow2 7) (U32.v state) (pow2 (32 - 7)) in
    assert (U32.v state * pow2 7 < pow2 32);
    let _ = update_state_inj2 state state x1 x2 in _)

let parse_asn1_identifier_loop_kind (i : nat {i <= 3}) = strong_parser_kind 0 (3 - i) None

let parse_asn1_identifier_loop_immediate_terminate
  (i : nat {i <= 2})
  (state : asn1_partial_id_t {partial_state_bound_f32 state = i})
  (buf : byte {U8.v buf < 128})
: (parser _ (state' : asn1_partial_id_t {partial_state_prefixr state state'}))
= let _ = in_bound_32 i state in
  parse_ret (update_state state buf)

let parse_cast
  (t : eqtype)
  (p1 : t -> Type0)
  (p2 : t -> Type0)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x: t {p1 x}))
: (parser k (x : t {p2 x}))
= let id_cast =
    fun (x : t {p1 x}) ->
      let _ = lem x in
      (x <: (x : t {p2 x}))
  in
  parse_synth #k #(x : t{p1 x}) #(x : t{p2 x}) p id_cast

let parse_cast_inverse
  (t : eqtype)
  (p1 : t -> Type0)
  (p2 : t -> Type0)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x : t {p1 x}))
  (b : bytes)
  (x : t {p2 x})
  (l : consumed_length b)
: Pure (x : t {p1 x})
  (requires (parse (parse_cast t p1 p2 lem p) b = Some (x, l)))
  (ensures (fun y -> y = x))
= let id_cast =
    fun (x : t {p1 x}) ->
      let _ = lem x in
      (x <: (x : t {p2 x}))
  in
  let _ = parse_synth_eq #k #(x : t{p1 x}) #(x : t{p2 x}) p id_cast b in
  match p b with
  | Some (x, l) -> x
  

let parse_asn1_identifier_loop_continue_weaken
  (state : asn1_partial_id_t)
  (state' : asn1_partial_id_t {partial_state_prefixr state state'})
  (#k : parser_kind)
  (p : parser k (state'' : asn1_partial_id_t {partial_state_prefixr state' state''}))
: parser k (state'' : asn1_partial_id_t {partial_state_prefixr state state''})
= let lem = Classical.move_requires (partial_state_prefixr_trans state state') in
  parse_cast 
    asn1_partial_id_t 
    (fun state'' -> partial_state_prefixr state' state'') 
    (fun state'' -> partial_state_prefixr state state'')     
    lem p

let lemma_parse_asn1_identifier_loop_continue_weaken_inverse
  (state : asn1_partial_id_t)
  (state' : asn1_partial_id_t {partial_state_prefixr state state'})
  (#k : parser_kind)
  (p : parser k (state'' : asn1_partial_id_t {partial_state_prefixr state' state''}))
  (b : bytes)
  (state'' : asn1_partial_id_t {partial_state_prefixr state state''})
  (l : _)
: Lemma 
  (requires (parse (parse_asn1_identifier_loop_continue_weaken state state' p) b = Some (state'', l)))
  (ensures (partial_state_prefixr state' state''))
= let lem = Classical.move_requires (partial_state_prefixr_trans state state') in
  let state''' = parse_cast_inverse 
                   asn1_partial_id_t 
                   (fun state'' -> partial_state_prefixr state' state'') 
                   (fun state'' -> partial_state_prefixr state state'') 
                   lem 
                   p b state'' l in
  assert (partial_state_prefixr state' state''');
  _

let loop_continue_calc_state'
  (state : asn1_partial_id_t)
  (buf : byte)
: Pure (asn1_partial_id_t)
  (requires (partial_state_bound_f32 state <= 2 /\ U8.v buf >= 128))
  (ensures (fun state' -> partial_state_bound_f32 state' = (partial_state_bound_f32 state) + 1 /\ partial_state_prefixr state state'))
= let b = U8.sub buf 128uy in
  let i = partial_state_bound_f32 state in
  let _ = in_bound_32 i state in
  update_state state b

let lemma_loop_continue_calc_state'_inj
  (state : asn1_partial_id_t)
  (buf1 buf2: byte)
  (state1 : asn1_partial_id_t)
  (state2 : asn1_partial_id_t)
: Lemma
  (requires (partial_state_bound_f32 state <= 2 /\ U8.v buf1 >= 128 /\ U8.v buf2 >= 128 
             /\ loop_continue_calc_state' state buf1 = state1 /\ loop_continue_calc_state' state buf2 = state2 /\ state1 = state2))
  (ensures (buf1 = buf2))
= let b1 = U8.sub buf1 128uy in
  let b2 = U8.sub buf2 128uy in
  let i = partial_state_bound_f32 state in
  let _ = in_bound_32 i state in
  update_state_inj2 state state b1 b2

let parse_loop_continuation_type (i : nat {i <= 3}) =
  (state : asn1_partial_id_t {partial_state_bound_f32 state = i}) -> byte ->
  (parser (parse_asn1_identifier_loop_kind (i)) (state' : asn1_partial_id_t {partial_state_prefixr state state'}))

let parse_loop_continuation_spec (i : nat {i <= 3}) (c : parse_loop_continuation_type i) =
  forall (state' : asn1_partial_id_t). (partial_state_bound_f32 state' = i) ==> and_then_cases_injective (c state')

let parse_asn1_identifier_loop_continue
  (i : nat {i <= 2})
  (c : parse_loop_continuation_type (i + 1))
  (state' : asn1_partial_id_t {partial_state_bound_f32 state' = i + 1})
: Pure (parser (parse_asn1_identifier_loop_kind i) (state'' : asn1_partial_id_t {partial_state_prefixr state' state''}))
  (requires (parse_loop_continuation_spec (i + 1) c))
  (ensures (fun _ -> True))
= let p' = c state' in
  weaken (parse_asn1_identifier_loop_kind i) (parse_u8 `and_then` p')

let parse_asn1_identifier_loop' 
  (i : nat {i <= 2})
  (c : parse_loop_continuation_type (i + 1))
  (state : asn1_partial_id_t {partial_state_bound_f32 state = i })
  (buf : byte) 
  : Pure (parser (parse_asn1_identifier_loop_kind i) (state' : asn1_partial_id_t {partial_state_prefixr state state'}))
    (requires (parse_loop_continuation_spec (i + 1) c))
    (ensures (fun _ -> True))
= if (U8.v buf) < 128 then
    weaken _ (parse_asn1_identifier_loop_immediate_terminate i state buf)
  else 
    let state' = loop_continue_calc_state' state buf in
    let p = parse_asn1_identifier_loop_continue i c state' in
    parse_asn1_identifier_loop_continue_weaken state state' p

let lemma_parse_asn1_identifier_loop'_cases_injective' 
  (i : nat {i <= 2}) 
  (c : parse_loop_continuation_type (i + 1))
  (state : asn1_partial_id_t {partial_state_bound_f32 state = i })
: Lemma 
  (requires (parse_loop_continuation_spec (i + 1) c))
  (ensures (and_then_cases_injective (parse_asn1_identifier_loop' i c state)))
= let p = parse_asn1_identifier_loop' i c state in
  and_then_cases_injective_intro p (fun x1 x2 b1 b2 ->
    match (parse (p x1) b1) with
    | Some (id1, l1) -> match (parse (p x2) b2) with
                 | Some (id2, l2) -> 
    (if (U8.v x1 < 128) then
      (let _ = in_bound_32 i state in
      if (U8.v x2 < 128) then
        let _ = update_state_inj2 state state x1 x2 in _
      else 
        (let state' = loop_continue_calc_state' state x2 in
        let p' = parse_asn1_identifier_loop_continue i c state' in
        let _ = lemma_parse_asn1_identifier_loop_continue_weaken_inverse state state' p' b2 id2 l2 in 
        _))
    else 
      (let _ = in_bound_32 i state in
      let state1' = loop_continue_calc_state' state x1 in
      let p1' = parse_asn1_identifier_loop_continue i c state1' in
      let _ = lemma_parse_asn1_identifier_loop_continue_weaken_inverse state state1' p1' b1 id1 l1 in
      if (U8.v x2 < 128) then
        _
      else
        (let state2' = loop_continue_calc_state' state x2 in
        let p2' = parse_asn1_identifier_loop_continue i c state2' in
        let _ = lemma_parse_asn1_identifier_loop_continue_weaken_inverse state state2' p2' b2 id2 l2 in 
        let _ = lemma_loop_continue_calc_state'_inj state x1 x2 state1' state2' in _
        ))))

let lemma_parse_asn1_identifier_loop'_cases_injective
  (i : nat {i <= 2}) 
  (c : parse_loop_continuation_type (i + 1))
: Lemma 
  (requires (parse_loop_continuation_spec (i + 1) c))
  (ensures (parse_loop_continuation_spec i (parse_asn1_identifier_loop' i c)))
= Classical.forall_intro (Classical.move_requires (lemma_parse_asn1_identifier_loop'_cases_injective' i c))

let rec parse_asn1_identifier_loop
  (i : nat {i <= 3})
: Pure (parse_loop_continuation_type i)
  (requires True)
  (ensures (fun c -> parse_loop_continuation_spec i c))
  (decreases %[3 - i])
= if i = 3 then
    let _ = Classical.forall_intro parse_asn1_identifier_tail_injective in
    parse_asn1_identifier_tail 
  else
    let c = parse_asn1_identifier_loop (i + 1) in
    let _ = (lemma_parse_asn1_identifier_loop'_cases_injective i c) in
    (parse_asn1_identifier_loop' i c)

let initialize_partial_state 
  (b : byte)
: Pure asn1_partial_id_t
  (requires (0 < U8.v b /\ U8.v b < 128))
  (ensures (fun state -> partial_state_bound_f32 state = 0))
= let ret = Cast.uint8_to_uint32 b in
  let _ = lemma_partial_state_bound_f32_intro ret 0 in
  ret

let initialize_partial_state_inj
  (b1 : byte)
  (b2 : byte)
: Lemma (requires (0 < U8.v b1 /\ U8.v b1 < 128 /\
                   0 < U8.v b2 /\ U8.v b2 < 128 /\
                   initialize_partial_state b1 = initialize_partial_state b2))
        (ensures b1 = b2)
= _

let parse_asn1_identifier_head_kind = strong_parser_kind 0 4 None

let parse_asn1_identifier_head'
  (state : asn1_partial_id_t)
: Pure (parser parse_asn1_identifier_head_kind (state' : asn1_partial_id_t {partial_state_prefixr state state'}))
  (requires (partial_state_bound_f32 state = 0))
  (ensures (fun _ -> True))
= let c = parse_asn1_identifier_loop 0 in
  let _ = Squash.give_proof (Classical.Sugar.forall_elim state (Squash.get_proof (parse_loop_continuation_spec 0 c))) in
  weaken (parse_asn1_identifier_head_kind)  
    (parse_u8
    `and_then`
    (c state))

let parse_asn1_identifier_head
  (buf : byte)
: parser parse_asn1_identifier_head_kind (state : asn1_partial_id_t {31 <= U32.v state})
= if (U8.v buf < 128) then
    (if (U8.v buf < 31) then
       fail_parser _ _
     else
       weaken (parse_asn1_identifier_head_kind) (parse_ret (initialize_partial_state buf)))
  else
    (let b = U8.sub buf 128uy in
    if (b = 0uy) then
      fail_parser _ _
    else
      (let state = (initialize_partial_state b) in
      parse_cast
        asn1_partial_id_t
        (fun x -> partial_state_prefixr state x)
        (fun x -> 31 <= U32.v x)
        (fun _ -> _)
        (parse_asn1_identifier_head' state)))

let lemma_parse_asn1_identifier_head_inj ()
: Lemma (ensures (and_then_cases_injective parse_asn1_identifier_head))
= let p = parse_asn1_identifier_head in
  and_then_cases_injective_intro p (fun buf1 buf2 b1 b2 ->
    match (parse (p buf1) b1) with
    | Some (state1, l1) -> match (parse (p buf2) b2) with
      | Some (state2, l2) ->
        (if (U8.v buf1 < 128) then
          (
            if (U8.v buf1 < 31) then
              _
            else
            ( if (U8.v buf2 < 128) then
              (
                if (U8.v buf2 < 31) then
                  _
                else
                  (
                    let _ = initialize_partial_state_inj buf1 buf2 in _
                  )
              )
              else
              (
                let unfold buf2' = U8.sub buf2 128uy in
                if (U8.v buf2' = 0) then
                  _
                else
                (
                  let unfold state2' = initialize_partial_state buf2' in
                  let state2 = parse_cast_inverse
                    asn1_partial_id_t
                    (fun x -> partial_state_prefixr state2' x)
                    (fun x -> 31 <= U32.v x)
                    (fun _ -> _)
                    (parse_asn1_identifier_head' state2')
                    b2
                    state2
                    l2
                  in
                  partial_state_bound_separation 0 state1 state2
                )
              )
            )
          )
        else
          (
          let unfold buf1' = U8.sub buf1 128uy in
          if (U8.v buf1' = 0) then
            _
          else
          (
            let unfold state1' = initialize_partial_state buf1' in
            let state1 = parse_cast_inverse
              asn1_partial_id_t
              (fun x -> partial_state_prefixr state1' x)
              (fun x -> 31 <= U32.v x)
              (fun _ -> _)
              (parse_asn1_identifier_head' state1')
              b1
              state1
              l1
            in
            ( if (U8.v buf2 < 128) then
              (
                if (U8.v buf2 < 31) then
                  _
                else
                  (
                    let _ = partial_state_bound_separation 0 state2 state1 in _
                  )
              )
              else
              (
                let unfold buf2' = U8.sub buf2 128uy in
                if (U8.v buf2' = 0) then
                  _
                else
                (
                  let unfold state2' = initialize_partial_state buf2' in
                  let state2 = parse_cast_inverse
                    asn1_partial_id_t
                    (fun x -> partial_state_prefixr state2' x)
                    (fun x -> 31 <= U32.v x)
                    (fun _ -> _)
                    (parse_asn1_identifier_head' state2')
                    b2
                    state2
                    l2
                  in
                  initialize_partial_state_inj buf1' buf2'
                )
              )
            )
          )
          )
        )
 )

let parse_asn1_identifier_head_alt
  (buf : byte)
: parser parse_asn1_identifier_head_kind (U32.t)
= if (U8.v buf < 128) then
    weaken (parse_asn1_identifier_head_kind) (parse_ret (Cast.uint8_to_uint32 buf))
  else
    (let b = U8.sub buf 128uy in
    if (b = 0uy) then
      fail_parser _ _
    else
      (let state = (initialize_partial_state b) in
      parse_cast
        U32.t
        (fun x -> 0 < U32.v x /\ partial_state_prefixr state x)
        (fun _ -> True)
        (fun _ -> _)
        (parse_asn1_identifier_head' state)))

let lemma_parse_asn1_identifier_head_alt_inj ()
: Lemma (ensures (and_then_cases_injective parse_asn1_identifier_head_alt))
= let p = parse_asn1_identifier_head_alt in
  and_then_cases_injective_intro p (fun buf1 buf2 b1 b2 ->
    match (parse (p buf1) b1) with
    | Some (state1, l1) -> match (parse (p buf2) b2) with
      | Some (state2, l2) ->
        (if (U8.v buf1 < 128) then
          (if (U8.v buf2 < 128) then
            _
          else
            (let unfold buf2' = U8.sub buf2 128uy in
            if (U8.v buf2' = 0) then
              _
            else
            (
              let unfold state2' = initialize_partial_state buf2' in
              let state2 = parse_cast_inverse
                U32.t
                (fun x -> 0 < U32.v x /\ partial_state_prefixr state2' x)
                (fun _ -> True)
                (fun _ -> _)
                (parse_asn1_identifier_head' state2')
                b2 state2 l2
              in
              partial_state_bound_separation 0 state1 state2
            )
            )
          )
        else
          (
          let unfold buf1' = U8.sub buf1 128uy in
          if (U8.v buf1' = 0) then
            _
          else
          (
            let unfold state1' = initialize_partial_state buf1' in
            let state1 = parse_cast_inverse
              U32.t
              (fun x -> 0 < U32.v x /\ partial_state_prefixr state1' x)
              (fun _ -> True)
              (fun _ -> _)
              (parse_asn1_identifier_head' state1')
              b1 state1 l1
            in
            (if (U8.v buf2 < 128) then
              _
              else
              (
                let unfold buf2' = U8.sub buf2 128uy in
                if (U8.v buf2' = 0) then
                  _
                else
                (
                  let unfold state2' = initialize_partial_state buf2' in
                  let state2 = parse_cast_inverse
                    U32.t
                    (fun x -> 0 < U32.v x /\ partial_state_prefixr state2' x)
                    (fun _ -> True)
                    (fun _ -> _)
                    (parse_asn1_identifier_head' state2')
                    b2 state2 l2
                  in
                  initialize_partial_state_inj buf1' buf2'
                )
              )
            )
          )
          )
        )
 )

let parse_asn1_identifier_first_kind = strong_parser_kind 0 5 None

let parse_asn1_identifier_first'
  (buf : byte {0 <= U8.v buf /\ U8.v buf <= 31})
: parser parse_asn1_identifier_first_kind U32.t
= if U8.v buf < 31 then
    weaken (parse_asn1_identifier_first_kind) (parse_ret (Cast.uint8_to_uint32 buf))
  else
    let _ = lemma_parse_asn1_identifier_head_inj () in
    let p = weaken (parse_asn1_identifier_first_kind)
    (parse_u8
    `and_then`
    parse_asn1_identifier_head) in
    parse_cast
      U32.t
      (fun x -> 31 <= U32.v x)
      (fun _ -> True)
      (fun _ -> _)
      p

let parse_asn1_identifier_first'_inj
  (buf1 : byte {0 <= U8.v buf1 /\ U8.v buf1 <= 31})
  (buf2 : byte {0 <= U8.v buf2 /\ U8.v buf2 <= 31})
  (by1 : bytes)
  (state1 : U32.t)
  (l1 : consumed_length by1)
  (by2 : bytes)
  (state2 : U32.t)
  (l2 : consumed_length by2)
: Lemma 
  (requires (parse (parse_asn1_identifier_first' buf1) by1 = Some (state1, l1) /\
             parse (parse_asn1_identifier_first' buf2) by2 = Some (state2, l2) /\
             state1 = state2))
  (ensures (buf1 = buf2))
= if U8.v buf1 < 31 then
  (
    if U8.v buf2 < 31 then
      _
    else 
      let _ = lemma_parse_asn1_identifier_head_inj () in
      let p = weaken (parse_asn1_identifier_first_kind)
        (parse_u8
        `and_then`
        parse_asn1_identifier_head) in
      let state2 = parse_cast_inverse
        U32.t
        (fun x -> 31 <= U32.v x)
        (fun _ -> True)
        (fun _ -> _)
        p by2 state2 l2 in
      _
  )
  else 
  (
    let _ = lemma_parse_asn1_identifier_head_inj () in
    let p = weaken (parse_asn1_identifier_first_kind)
      (parse_u8
      `and_then`
      parse_asn1_identifier_head) in
    let state1 = parse_cast_inverse
        U32.t
        (fun x -> 31 <= U32.v x)
        (fun _ -> True)
        (fun _ -> _)
        p by1 state1 l1 in
    if U8.v buf2 < 31 then
      _
    else 
      _
  )
  
let parse_asn1_identifier_first
  (buf : byte)
: parser parse_asn1_identifier_first_kind asn1_id_t
= let id_class = decode_asn1_identifier_class' buf in
  let id_flag = decode_asn1_identifier_flag' buf in
  let b = U8.rem buf 32uy in
  let p = parse_asn1_identifier_first' b in
  parse_synth p (MK_ASN1_ID id_class id_flag)

let encode_asn1_first_byte 
  (id_class : asn1_id_class_t)
  (id_flag : asn1_id_flag_t)
  (b : byte {0 <= U8.v b /\ U8.v b <= 31})
: byte
= let b0 = (match id_class with
           | UNIVERSAL -> 0uy
           | APPLICATION -> 1uy
           | CONTEXT_SPECIFIC -> 2uy
           | _ -> 3uy
           )
  in
  let b0' = U8.shift_left b0 6ul in
  assert (U8.v b0' <= 128 + 64);
  let b1 = (match id_flag with
           | PRIMITIVE -> 0uy
           | _ -> 1uy)
  in
  assert (U8.v b1 <= 1);
  let b1' = U8.shift_left b1 5ul in
  assert (U8.v b1' <= U8.v (U8.shift_left 1uy 5ul));
  assert (U8.v b1' <= 32);
  U8.add b0'
         (U8.add b1'
                 b)

let lemma_encode_asn1_first_byte_inverse
  (buf : byte)
: Lemma (ensures
    buf = encode_asn1_first_byte (decode_asn1_identifier_class' buf) (decode_asn1_identifier_flag' buf) (U8.rem buf 32uy))
= let id_class = decode_asn1_identifier_class' buf in
  let id_flag = decode_asn1_identifier_flag' buf in
  let b = U8.rem buf 32uy in
  let b0 = (match id_class with
             | UNIVERSAL -> 0uy
             | APPLICATION -> 1uy
             | CONTEXT_SPECIFIC -> 2uy
             | _ -> 3uy
             )
  in
  assert (b0 = (U8.shift_right buf) 6ul);
  let b0' = U8.shift_left b0 6ul in
  assert (U8.v b0' <= 128 + 64);
  let b1 = (match id_flag with
           | PRIMITIVE -> 0uy
           | _ -> 1uy)
  in
  assert (U8.v b1 <= 1);
  assert (b1 = U8.rem ((U8.shift_right buf) 5ul) 2uy);
  let b1' = U8.shift_left b1 5ul in
  assert (U8.v b1' <= U8.v (U8.shift_left 1uy 5ul));
  assert (U8.v b1' <= 32);
  let _ = UInt.shift_right_value_lemma #8 (U8.v buf) 6 in
  let _ = UInt.shift_right_value_lemma #8 (U8.v buf) 5 in
  let _ = UInt.shift_left_value_lemma #8 (U8.v b0) 6 in
  let _ = UInt.shift_left_value_lemma #8 (U8.v b1) 5 in
  assert (buf = U8.add b0' (U8.add b1' b))
  
let lemma_decode_asn1_identifier_first_byte_inj
  (id_class1 id_class2 : asn1_id_class_t)
  (id_flag1 id_flag2 : asn1_id_flag_t)
  (b1 b2 : byte)
  (buf1 buf2 : byte)
: Lemma (requires 
  (id_class1 = id_class2 /\
   id_flag1 = id_flag2 /\
   (0 <= U8.v b1 /\ U8.v b1 <= 31) /\
   (0 <= U8.v b2 /\ U8.v b2 <= 31) /\
   b1 = b2 /\
   decode_asn1_identifier_class' buf1 = id_class1 /\
   decode_asn1_identifier_class' buf2 = id_class2 /\
   decode_asn1_identifier_flag' buf1 = id_flag1 /\
   decode_asn1_identifier_flag' buf2 = id_flag2 /\
   U8.rem buf1 32uy = b1 /\
   U8.rem buf2 32uy = b2))
   (ensures (buf1 = buf2))
= let _ = lemma_encode_asn1_first_byte_inverse buf1 in
  let _ = lemma_encode_asn1_first_byte_inverse buf2 in
  _
  
let lemma_parse_asn1_identifier_first_inj ()
: Lemma (ensures (and_then_cases_injective parse_asn1_identifier_first))
= let p = parse_asn1_identifier_first in
  and_then_cases_injective_intro p (fun buf1 buf2 by1 by2 ->
    match (parse (p buf1) by1) with
    | Some (MK_ASN1_ID id_class1' id_flag1' state1', l1') -> match (parse (p buf2) by2) with
      | Some (MK_ASN1_ID id_class2' id_flag2' state2', l2') ->
      (
         let id_class1 = decode_asn1_identifier_class (U8.shift_right buf1 6ul) in
         let id_flag1 = decode_asn1_identifier_flag (U8.rem (U8.shift_right buf1 5ul) 2uy)in
         let b1 = U8.rem buf1 32uy in        
         let p1 = parse_asn1_identifier_first' b1 in
         let _ = parse_synth_eq p1 (MK_ASN1_ID id_class1 id_flag1) by1 in
         match (parse p1 by1) with
         | Some (state1, l1) ->
         (
           let id_class2 = decode_asn1_identifier_class (U8.shift_right buf2 6ul) in
           let id_flag2 = decode_asn1_identifier_flag (U8.rem (U8.shift_right buf2 5ul) 2uy)in
           let b2 = U8.rem buf2 32uy in        
           let p2 = parse_asn1_identifier_first' b2 in
           let _ = parse_synth_eq p2 (MK_ASN1_ID id_class2 id_flag2) by2 in
           match (parse p2 by2) with
           | Some (state2, l2) ->
             let _ = parse_asn1_identifier_first'_inj b1 b2 by1 state1 l1 by2 state2 l2 in
             assert (b1 = b2);
             lemma_decode_asn1_identifier_first_byte_inj id_class1 id_class2 id_flag1 id_flag2 b1 b2 buf1 buf2
         )
      )
  )

let parse_asn1_identifier_U32 : asn1_strong_parser (asn1_id_t)
= let _ = lemma_parse_asn1_identifier_first_inj () in
  weaken (asn1_strong_parser_kind)
  (parse_u8
  `and_then`
  parse_asn1_identifier_first)

let parse_asn1_identifier_U32_alt : parser parse_asn1_identifier_first_kind U32.t
= let _ = lemma_parse_asn1_identifier_head_alt_inj () in
  weaken (parse_asn1_identifier_first_kind)
  (parse_u8 `and_then` parse_asn1_identifier_head_alt)
