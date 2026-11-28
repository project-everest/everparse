module ASN1.Spec.IdentifierU32.Enc

(* Encoder for ASN.1 DER identifiers (X.690 8.1.2), and its correctness
   with respect to the identifier parser ASN1.Spec.IdentifierU32 *)

open ASN1.Base

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.Int

open ASN1.Spec.IdentifierU32

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module Cast = FStar.Int.Cast

(* First byte *)

let id_class_num (c: asn1_id_class_t) : Tot (n: nat { n <= 3 }) =
  match c with
  | UNIVERSAL -> 0
  | APPLICATION -> 1
  | CONTEXT_SPECIFIC -> 2
  | PRIVATE -> 3

let id_flag_num (f: asn1_id_flag_t) : Tot (n: nat { n <= 1 }) =
  match f with
  | PRIMITIVE -> 0
  | CONSTRUCTED -> 1

#push-options "--z3rlimit 64 --fuel 0 --ifuel 1"

let encode_asn1_first_byte_value
  (c: asn1_id_class_t)
  (f: asn1_id_flag_t)
  (b: byte { U8.v b <= 31 })
: Lemma
  (U8.v (encode_asn1_first_byte c f b) == 64 * id_class_num c + 32 * id_flag_num f + U8.v b)
= let b0 : U8.t = U8.uint_to_t (id_class_num c) in
  let b1 : U8.t = U8.uint_to_t (id_flag_num f) in
  UInt.shift_left_value_lemma #8 (U8.v b0) 6;
  UInt.shift_left_value_lemma #8 (U8.v b1) 5;
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 5 == 32);
  assert_norm (pow2 8 == 256)

let encode_asn1_first_byte_decode
  (c: asn1_id_class_t)
  (f: asn1_id_flag_t)
  (b: byte { U8.v b <= 31 })
: Lemma
  (let x = encode_asn1_first_byte c f b in
    decode_asn1_identifier_class' x == c /\
    decode_asn1_identifier_flag' x == f /\
    U8.rem x 32uy == b)
= let x = encode_asn1_first_byte c f b in
  encode_asn1_first_byte_value c f b;
  UInt.shift_right_value_lemma #8 (U8.v x) 6;
  UInt.shift_right_value_lemma #8 (U8.v x) 5;
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 5 == 32);
  let cn = id_class_num c in
  let fn = id_flag_num f in
  FStar.Math.Lemmas.lemma_div_plus (32 * fn + U8.v b) cn 64;
  FStar.Math.Lemmas.small_div (32 * fn + U8.v b) 64;
  assert (U8.v x / 64 == cn);
  FStar.Math.Lemmas.lemma_div_plus (U8.v b) (2 * cn + fn) 32;
  FStar.Math.Lemmas.small_div (U8.v b) 32;
  assert (U8.v x / 32 == 2 * cn + fn);
  FStar.Math.Lemmas.lemma_mod_plus fn cn 2;
  FStar.Math.Lemmas.small_mod fn 2;
  FStar.Math.Lemmas.lemma_mod_plus (U8.v b) (2 * cn + fn) 32;
  FStar.Math.Lemmas.small_mod (U8.v b) 32

#pop-options

(* Value of update_state *)

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let update_state_value (state: asn1_partial_id_t) (b: byte)
: Lemma
  (requires (U8.v b < 128 /\ U32.v state < pow2 25))
  (ensures (U32.v (update_state state b) == U32.v state * 128 + U8.v b))
= assert_norm (pow2 7 == 128);
  Math.Lemmas.lemma_mult_lt_right (pow2 7) (U32.v state) (pow2 25);
  Math.Lemmas.pow2_plus 25 7;
  UInt.shift_left_value_lemma #32 (U32.v state) 7;
  let a = U32.v state * pow2 7 in
  Math.Lemmas.small_mod a (pow2 32);
  Math.Lemmas.cancel_mul_mod (U32.v state) (pow2 7);
  UInt.logor_disjoint #32 a (U8.v b) 7
#pop-options

(* Base-128 digits *)

let id_bound (v: asn1_partial_id_t) : Tot (n: nat { n <= 4 }) = partial_state_bound_f32 v

let id_digit (v: asn1_partial_id_t) (m: nat { m <= id_bound v }) : Tot (d: nat { d < 128 }) =
  U32.v (partial_state_prefixf v m) % 128

#push-options "--z3rlimit 64 --fuel 0 --ifuel 0"
let id_digit_step (v: asn1_partial_id_t) (m: nat { m < id_bound v })
: Lemma
  (U32.v (partial_state_prefixf v (m + 1)) == U32.v (partial_state_prefixf v m) * 128 + id_digit v (m + 1))
= let j = id_bound v in
  lemma_partial_state_prefixf_val v m;
  lemma_partial_state_prefixf_val v (m + 1);
  let a = U32.v v / pow2 ((j - (m + 1)) * 7) in
  Math.Lemmas.division_multiplication_lemma (U32.v v) (pow2 ((j - (m + 1)) * 7)) (pow2 7);
  Math.Lemmas.pow2_plus ((j - (m + 1)) * 7) 7;
  assert ((j - (m + 1)) * 7 + 7 == (j - m) * 7);
  assert_norm (pow2 7 == 128);
  Math.Lemmas.euclidean_division_definition a 128

let id_digit_last (v: asn1_partial_id_t)
: Lemma (partial_state_prefixf v (id_bound v) == v)
= lemma_partial_state_prefixf_val v (id_bound v)

let id_digit_first (v: asn1_partial_id_t)
: Lemma (0 < U32.v (partial_state_prefixf v 0) /\ U32.v (partial_state_prefixf v 0) < 128 /\ id_digit v 0 == U32.v (partial_state_prefixf v 0))
= assert_norm (partial_state_upperbound 0 == 128)
#pop-options

let rec enc_tail (v: asn1_partial_id_t) (i: nat { i < id_bound v })
: Tot bytes
  (decreases (id_bound v - i))
= let m = i + 1 in
  let d = id_digit v m in
  if m = id_bound v
  then Seq.create 1 (U8.uint_to_t d)
  else Seq.cons (U8.uint_to_t (d + 128)) (enc_tail v m)

let parse_u8_and_then_cons
  (#k: parser_kind)
  (#t: Type)
  (p: byte -> parser k t)
  (x: byte)
  (rest: bytes)
: Lemma
  (requires (and_then_cases_injective p))
  (ensures (
    parse (parse_u8 `and_then` p) (Seq.cons x rest) == (
      match parse (p x) rest with
      | Some (v, l) -> Some (v, l + 1)
      | None -> None
  )))
= let b = Seq.cons x rest in
  and_then_eq parse_u8 p b;
  parse_u8_spec' b;
  parse_u8_spec b;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  assert (Seq.index b 0 == x);
  Seq.lemma_eq_elim (Seq.slice b 1 (Seq.length b)) rest


(* Relating parse results whose value types differ only in their
   refinements. We use projectors rather than `match`, since the SMT
   encoding of pattern matching on differently typed scrutinees does not
   allow rewriting across them. *)

let parse_cast_eq
  (t : eqtype)
  (p1 : t -> prop)
  (p2 : t -> prop)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x: t {p1 x}))
  (b: bytes)
: Lemma
  (let r1 = parse (parse_cast t p1 p2 lem p) b in
   let r2 = parse p b in
   (Some? r1 <==> Some? r2) /\
   (Some? r1 ==> ((fst (Some?.v r1) <: t) == (fst (Some?.v r2) <: t) /\ snd (Some?.v r1) == snd (Some?.v r2))))
= let id_cast =
    fun (x : t {p1 x}) ->
      let _ = lem x in
      (x <: (x : t {p2 x}))
  in
  parse_synth_eq #k #(x : t{p1 x}) #(x : t{p2 x}) p id_cast b

let parse_loop_continue_weaken_eq
  (state : asn1_partial_id_t)
  (state' : asn1_partial_id_t {partial_state_prefixr state state'})
  (#k : parser_kind)
  (p : parser k (state'' : asn1_partial_id_t {partial_state_prefixr state' state''}))
  (b : bytes)
: Lemma
  (let r1 = parse (parse_asn1_identifier_loop_continue_weaken state state' p) b in let r2 = parse p b in
     (Some? r1 <==> Some? r2) /\
     (Some? r1 ==> (U32.v (fst (Some?.v r1)) == U32.v (fst (Some?.v r2)) /\ snd (Some?.v r1) == snd (Some?.v r2))))
= let lem = Classical.move_requires (partial_state_prefixr_trans state state') in
  parse_cast_eq
    asn1_partial_id_t 
    (fun state'' -> partial_state_prefixr state' state'') 
    (fun state'' -> partial_state_prefixr state state'')     
    lem p b

let loop_continue_calc_state'_spec (state : asn1_partial_id_t) (buf : byte)
: Lemma
  (requires (partial_state_bound_f32 state <= 2 /\ U8.v buf >= 128))
  (ensures (
    let state' = loop_continue_calc_state' state buf in
    partial_state_bound_f32 state' = (partial_state_bound_f32 state) + 1 /\ partial_state_prefixr state state' /\
    U32.v state' == U32.v state * 128 + (U8.v buf - 128)
  ))
= let state' = loop_continue_calc_state' state buf in
  in_bound_32 (partial_state_bound_f32 state) state;
  update_state_value state (U8.sub buf 128uy)

let parse_asn1_identifier_loop_spec (i: nat { i <= 3 })
: Lemma (parse_loop_continuation_spec i (parse_asn1_identifier_loop i))
= let c = parse_asn1_identifier_loop i in
  assert (parse_loop_continuation_spec i c)

let parse_asn1_identifier_loop_inj (i: nat { i <= 3 }) (s: asn1_partial_id_t { partial_state_bound_f32 s = i })
: Lemma (and_then_cases_injective (parse_asn1_identifier_loop i s))
= parse_asn1_identifier_loop_spec i

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let parse_loop_step_last
  (i: nat { i <= 3 })
  (state: asn1_partial_id_t { partial_state_bound_f32 state = i })
  (x: byte { U8.v x < 128 })
  (suffix: bytes)
: Lemma
  (requires (i = 3 ==> U32.v state < pow2 25))
  (ensures (
    U32.v state < pow2 25 /\
    (let r1 = parse (parse_asn1_identifier_loop i state x) suffix in
     Some? r1 /\ U32.v (fst (Some?.v r1)) == U32.v (update_state state x) /\ snd (Some?.v r1) == 0)
  ))
= if i = 3
  then begin
    assert (parse (parse_asn1_identifier_loop i state x) suffix == parse (parse_asn1_identifier_tail state x) suffix)
  end else begin
    in_bound_32 i state;
    assert (parse (parse_asn1_identifier_loop i state x) suffix == parse (parse_asn1_identifier_loop' i (parse_asn1_identifier_loop (i + 1)) state x) suffix)
  end

let parse_loop_step_cont
  (i: nat { i <= 2 })
  (state: asn1_partial_id_t { partial_state_bound_f32 state = i })
  (x: byte { U8.v x >= 128 })
  (rest: bytes)
: Lemma
  (ensures (
    U32.v state < pow2 25 /\ (
    let state' = loop_continue_calc_state' state x in
    (let r1 = parse (parse_asn1_identifier_loop i state x) rest in let r2 = parse (parse_u8 `and_then` parse_asn1_identifier_loop (i + 1) state') rest in
     (Some? r1 <==> Some? r2) /\
     (Some? r1 ==> (U32.v (fst (Some?.v r1)) == U32.v (fst (Some?.v r2)) /\ snd (Some?.v r1) == snd (Some?.v r2))))
  )))
= in_bound_32 i state;
  loop_continue_calc_state'_spec state x;
  parse_asn1_identifier_loop_inj (i + 1) (loop_continue_calc_state' state x);
  assert (parse (parse_asn1_identifier_loop i state x) rest == parse (parse_asn1_identifier_loop_continue_weaken state (loop_continue_calc_state' state x) (parse_asn1_identifier_loop_continue i (parse_asn1_identifier_loop (i + 1)) (loop_continue_calc_state' state x))) rest);
  assert (parse (parse_asn1_identifier_loop_continue i (parse_asn1_identifier_loop (i + 1)) (loop_continue_calc_state' state x)) rest == parse (parse_u8 `and_then` parse_asn1_identifier_loop (i + 1) (loop_continue_calc_state' state x)) rest) by (
    FStar.Tactics.norm [delta_only [`%parse_asn1_identifier_loop_continue; `%weaken; `%tot_weaken; `%coerce_to_tot_bare_parser]; zeta; iota];
    FStar.Tactics.smt ()
  );
  parse_loop_continue_weaken_eq state (loop_continue_calc_state' state x) (parse_asn1_identifier_loop_continue i (parse_asn1_identifier_loop (i + 1)) (loop_continue_calc_state' state x)) rest
#pop-options

let parse_loop_state_eq
  (i: nat { i <= 3 })
  (s1 s2: asn1_partial_id_t)
  (b: bytes)
: Lemma
  (requires (partial_state_bound_f32 s1 = i /\ s1 == s2))
  (ensures (
    parse_asn1_identifier_loop_inj i s1;
    parse_asn1_identifier_loop_inj i s2;
    let r1 = parse (parse_u8 `and_then` parse_asn1_identifier_loop i s1) b in
    let r2 = parse (parse_u8 `and_then` parse_asn1_identifier_loop i s2) b in
    (Some? r1 <==> Some? r2) /\
    (Some? r1 ==> (U32.v (fst (Some?.v r1)) == U32.v (fst (Some?.v r2)) /\ snd (Some?.v r1) == snd (Some?.v r2)))
  ))
= parse_asn1_identifier_loop_inj i s1

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec parse_loop_enc_tail
  (i: nat { i <= 3 })
  (v: asn1_partial_id_t)
  (suffix: bytes)
: Lemma
  (requires (i < id_bound v))
  (ensures (
    let state = partial_state_prefixf v i in
    (let r1 = parse (parse_u8 `and_then` parse_asn1_identifier_loop i state) (enc_tail v i `Seq.append` suffix) in
     Some? r1 /\ U32.v (fst (Some?.v r1)) == U32.v v /\ snd (Some?.v r1) == Seq.length (enc_tail v i))
  ))
  (decreases (3 - i))
= id_digit_step v i;
  parse_asn1_identifier_loop_inj i (partial_state_prefixf v i);
  if i + 1 = id_bound v
  then begin
    id_digit_last v;
    Seq.lemma_eq_elim (enc_tail v i `Seq.append` suffix) (Seq.cons (U8.uint_to_t (id_digit v (i + 1))) suffix);
    parse_u8_and_then_cons (parse_asn1_identifier_loop i (partial_state_prefixf v i)) (U8.uint_to_t (id_digit v (i + 1))) suffix;
    if i = 3 then begin
      lemma_partial_state_prefixf_val v i;
      Math.Lemmas.lemma_div_lt_nat (U32.v v) 32 7
    end;
    parse_loop_step_last i (partial_state_prefixf v i) (U8.uint_to_t (id_digit v (i + 1))) suffix;
    update_state_value (partial_state_prefixf v i) (U8.uint_to_t (id_digit v (i + 1)))
  end else begin
    Seq.append_cons (U8.uint_to_t (id_digit v (i + 1) + 128)) (enc_tail v (i + 1)) suffix;
    Seq.lemma_eq_elim (enc_tail v i `Seq.append` suffix) (Seq.cons (U8.uint_to_t (id_digit v (i + 1) + 128)) (enc_tail v (i + 1) `Seq.append` suffix));
    parse_u8_and_then_cons (parse_asn1_identifier_loop i (partial_state_prefixf v i)) (U8.uint_to_t (id_digit v (i + 1) + 128)) (enc_tail v (i + 1) `Seq.append` suffix);
    parse_loop_step_cont i (partial_state_prefixf v i) (U8.uint_to_t (id_digit v (i + 1) + 128)) (enc_tail v (i + 1) `Seq.append` suffix);
    loop_continue_calc_state'_spec (partial_state_prefixf v i) (U8.uint_to_t (id_digit v (i + 1) + 128));
    U32.v_inj (loop_continue_calc_state' (partial_state_prefixf v i) (U8.uint_to_t (id_digit v (i + 1) + 128))) (partial_state_prefixf v (i + 1));
    parse_loop_state_eq (i + 1) (loop_continue_calc_state' (partial_state_prefixf v i) (U8.uint_to_t (id_digit v (i + 1) + 128))) (partial_state_prefixf v (i + 1)) (enc_tail v (i + 1) `Seq.append` suffix);
    parse_loop_enc_tail (i + 1) v suffix
  end
#pop-options

let parse_cast_eq_pat
  (t : eqtype)
  (p1 : t -> prop)
  (p2 : t -> prop)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x: t {p1 x}))
  (b: bytes)
: Lemma
  (let r1 = parse (parse_cast t p1 p2 lem p) b in
   let r2 = parse p b in
   (Some? r1 <==> Some? r2) /\
   (Some? r1 ==> ((fst (Some?.v r1) <: t) == (fst (Some?.v r2) <: t) /\ snd (Some?.v r1) == snd (Some?.v r2))))
  [SMTPat (parse (parse_cast t p1 p2 lem p) b)]
= parse_cast_eq t p1 p2 lem p b

let enc_long (v: U32.t { 31 <= U32.v v }) : Tot bytes =
  if id_bound v = 0
  then Seq.create 1 (Cast.uint32_to_uint8 v)
  else Seq.cons (U8.uint_to_t (id_digit v 0 + 128)) (enc_tail v 0)

let initialize_partial_state_spec (b: byte)
: Lemma
  (requires (0 < U8.v b /\ U8.v b < 128))
  (ensures (U32.v (initialize_partial_state b) == U8.v b /\ partial_state_bound_f32 (initialize_partial_state b) == 0))
= let _ = initialize_partial_state b in ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let parse_head_step
  (x: byte { U8.v x >= 128 /\ U8.v x <> 128 })
  (rest: bytes)
: Lemma
  (ensures (
    initialize_partial_state_spec (U8.sub x 128uy);
    parse_asn1_identifier_loop_inj 0 (initialize_partial_state (U8.sub x 128uy));
    let r1 = parse (parse_asn1_identifier_head x) rest in
    let r2 = parse (parse_u8 `and_then` parse_asn1_identifier_loop 0 (initialize_partial_state (U8.sub x 128uy))) rest in
    (Some? r1 <==> Some? r2) /\
    (Some? r1 ==> (U32.v (fst (Some?.v r1)) == U32.v (fst (Some?.v r2)) /\ snd (Some?.v r1) == snd (Some?.v r2)))
  ))
= initialize_partial_state_spec (U8.sub x 128uy);
  parse_asn1_identifier_loop_inj 0 (initialize_partial_state (U8.sub x 128uy));
  assert (parse (parse_asn1_identifier_head x) rest == parse (parse_cast
        asn1_partial_id_t
        (fun y -> partial_state_prefixr (initialize_partial_state (U8.sub x 128uy)) y)
        (fun y -> 31 <= U32.v y)
        (fun _ -> ())
        (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy)))) rest);
  assert (Some? (parse (parse_asn1_identifier_head x) rest) <==> Some? (parse (parse_cast
        asn1_partial_id_t
        (fun y -> partial_state_prefixr (initialize_partial_state (U8.sub x 128uy)) y)
        (fun y -> 31 <= U32.v y)
        (fun _ -> ())
        (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy)))) rest));
  parse_cast_eq
        asn1_partial_id_t
        (fun y -> partial_state_prefixr (initialize_partial_state (U8.sub x 128uy)) y)
        (fun y -> 31 <= U32.v y)
        (fun _ -> ())
        (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy))) rest;
  assert (parse (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy))) rest == parse (parse_u8 `and_then` parse_asn1_identifier_loop 0 (initialize_partial_state (U8.sub x 128uy))) rest) by (
    FStar.Tactics.norm [delta_only [`%parse_asn1_identifier_head'; `%weaken; `%tot_weaken; `%coerce_to_tot_bare_parser]; zeta; iota];
    FStar.Tactics.smt ()
  )

let parse_head_enc_long
  (v: U32.t { 31 <= U32.v v })
  (suffix: bytes)
: Lemma
  (lemma_parse_asn1_identifier_head_inj ();
   let r = parse (parse_u8 `and_then` parse_asn1_identifier_head) (enc_long v `Seq.append` suffix) in
   Some? r /\ U32.v (fst (Some?.v r)) == U32.v v /\ snd (Some?.v r) == Seq.length (enc_long v))
= lemma_parse_asn1_identifier_head_inj ();
  if id_bound v = 0
  then begin
    assert_norm (partial_state_upperbound 0 == 128);
    Seq.lemma_eq_elim (enc_long v `Seq.append` suffix) (Seq.cons (Cast.uint32_to_uint8 v) suffix);
    parse_u8_and_then_cons parse_asn1_identifier_head (Cast.uint32_to_uint8 v) suffix;
    initialize_partial_state_spec (Cast.uint32_to_uint8 v)
  end else begin
    id_digit_first v;
    Seq.append_cons (U8.uint_to_t (id_digit v 0 + 128)) (enc_tail v 0) suffix;
    Seq.lemma_eq_elim (enc_long v `Seq.append` suffix) (Seq.cons (U8.uint_to_t (id_digit v 0 + 128)) (enc_tail v 0 `Seq.append` suffix));
    parse_u8_and_then_cons parse_asn1_identifier_head (U8.uint_to_t (id_digit v 0 + 128)) (enc_tail v 0 `Seq.append` suffix);
    parse_head_step (U8.uint_to_t (id_digit v 0 + 128)) (enc_tail v 0 `Seq.append` suffix);
    initialize_partial_state_spec (U8.sub (U8.uint_to_t (id_digit v 0 + 128)) 128uy);
    U32.v_inj (initialize_partial_state (U8.sub (U8.uint_to_t (id_digit v 0 + 128)) 128uy)) (partial_state_prefixf v 0);
    parse_loop_state_eq 0 (initialize_partial_state (U8.sub (U8.uint_to_t (id_digit v 0 + 128)) 128uy)) (partial_state_prefixf v 0) (enc_tail v 0 `Seq.append` suffix);
    parse_loop_enc_tail 0 v suffix
  end
#pop-options

(* The identifier encoder (X.690 8.1.2) *)

let asn1_id_enc (id: asn1_id_t) : Tot bytes =
  let MK_ASN1_ID c f n = id in
  if U32.v n < 31
  then Seq.create 1 (encode_asn1_first_byte c f (Cast.uint32_to_uint8 n))
  else Seq.cons (encode_asn1_first_byte c f 31uy) (enc_long n)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let parse_first'_long
  (rest: bytes)
: Lemma
  (lemma_parse_asn1_identifier_head_inj ();
   let r1 = parse (parse_asn1_identifier_first' 31uy) rest in
   let r2 = parse (parse_u8 `and_then` parse_asn1_identifier_head) rest in
   (Some? r1 <==> Some? r2) /\
   (Some? r1 ==> (U32.v (fst (Some?.v r1)) == U32.v (fst (Some?.v r2)) /\ snd (Some?.v r1) == snd (Some?.v r2))))
= lemma_parse_asn1_identifier_head_inj ();
  let p = weaken (parse_asn1_identifier_first_kind) (parse_u8 `and_then` parse_asn1_identifier_head) in
  assert (parse (parse_asn1_identifier_first' 31uy) rest == parse (parse_cast U32.t (fun x -> 31 <= U32.v x) (fun _ -> True) (fun _ -> ()) p) rest);
  parse_cast_eq U32.t (fun x -> 31 <= U32.v x) (fun _ -> True) (fun _ -> ()) p rest;
  assert (parse p rest == parse (parse_u8 `and_then` parse_asn1_identifier_head) rest)

let parse_first'_enc
  (n: U32.t)
  (suffix: bytes)
: Lemma
  (let b : byte = if U32.v n < 31 then Cast.uint32_to_uint8 n else 31uy in
   let e : bytes = if U32.v n < 31 then Seq.empty else enc_long n in
   parse (parse_asn1_identifier_first' b) (e `Seq.append` suffix) == Some (n, Seq.length e))
= if U32.v n < 31
  then begin
    Seq.lemma_eq_elim (Seq.empty `Seq.append` suffix) suffix;
    assert_norm (pow2 8 == 256);
    FStar.Math.Lemmas.small_mod (U32.v n) (pow2 8);
    U32.v_inj (Cast.uint8_to_uint32 (Cast.uint32_to_uint8 n)) n
  end else begin
    parse_first'_long (enc_long n `Seq.append` suffix);
    parse_head_enc_long n suffix;
    match parse (parse_asn1_identifier_first' 31uy) (enc_long n `Seq.append` suffix) with
    | Some (y, _) -> U32.v_inj y n
  end
#pop-options

#push-options "--z3rlimit 64 --fuel 0 --ifuel 1"
let parse_asn1_identifier_U32_enc
  (id: asn1_id_t)
  (suffix: bytes)
: Lemma
  (parse parse_asn1_identifier_U32 (asn1_id_enc id `Seq.append` suffix) == Some (id, Seq.length (asn1_id_enc id)))
= let MK_ASN1_ID c f n = id in
  let b : byte = if U32.v n < 31 then Cast.uint32_to_uint8 n else 31uy in
  let e : bytes = if U32.v n < 31 then Seq.empty else enc_long n in
  assert_norm (pow2 8 == 256);
  if U32.v n < 31 then FStar.Math.Lemmas.small_mod (U32.v n) (pow2 8);
  let x = encode_asn1_first_byte c f b in
  encode_asn1_first_byte_decode c f b;
  Seq.lemma_eq_elim (asn1_id_enc id `Seq.append` suffix) (Seq.cons x (e `Seq.append` suffix));
  lemma_parse_asn1_identifier_first_inj ();
  assert (parse parse_asn1_identifier_U32 (asn1_id_enc id `Seq.append` suffix) == parse (parse_u8 `and_then` parse_asn1_identifier_first) (Seq.cons x (e `Seq.append` suffix)));
  parse_u8_and_then_cons parse_asn1_identifier_first x (e `Seq.append` suffix);
  parse_synth_eq (parse_asn1_identifier_first' (U8.rem x 32uy)) (MK_ASN1_ID c f) (e `Seq.append` suffix);
  parse_first'_enc n suffix;
  if U32.v n < 31
  then assert (Seq.length (asn1_id_enc id) == 1)
  else assert (Seq.length (asn1_id_enc id) == 1 + Seq.length e)
#pop-options

let parse_asn1_identifier_U32_consumed
  (b: bytes)
: Lemma
  (match parse parse_asn1_identifier_U32 b with
   | Some (id, c) -> Seq.slice b 0 c == asn1_id_enc id
   | None -> True)
= match parse parse_asn1_identifier_U32 b with
  | Some (id, c) ->
    let e = asn1_id_enc id in
    parse_asn1_identifier_U32_enc id Seq.empty;
    Seq.append_empty_r e;
    parse_injective #asn1_strong_parser_kind parse_asn1_identifier_U32 b e;
    Seq.lemma_eq_elim (Seq.slice e 0 (Seq.length e)) e
  | None -> ()
