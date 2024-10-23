module ASN1.Spec.Content.UTF8STRING
open ASN1.Base
open ASN1.Spec.Automata

open LowParse.Tot.Combinators
open LowParse.Tot.Int
open LowParse.Tot.List

module U8 = FStar.UInt8
module U32 = FStar.UInt32

module Cast = FStar.Int.Cast

open FStar.Mul

let _ = assert_norm (pow2 16 == 65536)
let _ = assert_norm (pow2 9 == 512)
let _ = assert_norm (pow2 3 == 8)
let _ = assert_norm (pow2 6 == 64)
let _ = assert_norm (pow2 12 == 4096)
let _ = assert_norm (pow2 18 == 262144)
let _ = assert_norm (pow2 11 == 2048)
let _ = assert_norm (pow2 21 == 2097152)
let _ = assert_norm (pow2 15 == 32768)
let _ = assert_norm (pow2 32 == 4294967296)
let _ = assert_norm (pow2 7 == 128)
let _ = assert_norm (pow2 20 == 1048576)

type utf8_cp_s =
| Init | S3 | S3' | S2 | S2' | S1

let ch_t = U8.t

let out_range_common (ch : ch_t) =
  U8.v ch < 128 || 128 + 64 <= U8.v ch

let out_range_s2' (ch : ch_t) =
  U8.v ch < 128 + 32 || 128 + 64 <= U8.v ch

let out_range_s3' (ch : ch_t) =
  U8.v ch < 128 + 16 || 128 + 64 <= U8.v ch

let out_range_init (ch : ch_t) =
  (128 <= U8.v ch && U8.v ch <= 128 + 64 + 1) || 248 <= U8.v ch

let fail_check (s : utf8_cp_s) : ch_t -> bool =
  match s with
  | S1 | S2 | S3 -> out_range_common
  | S2' -> out_range_s2'
  | S3' -> out_range_s3'
  | Init -> out_range_init

let termination_check (s : utf8_cp_s) =
  match s with
  | S1 -> fun _ -> true
  | S2 | S3 | S2' | S3' -> fun _ -> false
  | Init -> (fun (ch : ch_t {fail_check s ch = false}) -> U8.v ch < 128)

let next_state (s : utf8_cp_s) (ch : ch_t {fail_check s ch = false /\ termination_check s ch = false}) : utf8_cp_s =
  match s with
  | S2 | S2' -> S1
  | S3 | S3' -> S2
  | Init -> if (U8.v ch < 128 + 64 + 32) then
             S1
           else if (U8.v ch = 128 + 64 + 32) then
             S2'
           else if (U8.v ch < 128 + 64 + 32 + 16) then
             S2
           else if (U8.v ch = 128 + 64 + 32 + 16) then
             S3'
           else
             S3

let utf8_cp_cp : automata_control_param = {
  control_t = utf8_cp_s;
  ch_t = ch_t;
  fail_check = fail_check;
  termination_check = termination_check;
  next_state = next_state
}

let ret_t = utf8_cp_t

let partial_t = U32.t
  
let pre_t (s : utf8_cp_s) : partial_t -> Type0 =
  match s with
  | S1 -> (fun data -> 1 < U32.v data /\ U32.v data < pow2 15)
  | S2 -> (fun data -> 0 < U32.v data /\ U32.v data < pow2 9)
  | S3 -> (fun data -> 0 < U32.v data /\ U32.v data < pow2 3)
  | S2' | S3' | Init -> (fun data -> U32.v data = 0)

let post_t (s : utf8_cp_s) (data : partial_t {pre_t s data}) : ret_t -> Type0 =
  match s with
  | S1 -> (fun ret -> U32.v data * (pow2 6) <= U32.v ret /\ U32.v ret < (U32.v data + 1) * (pow2 6))
  | S2 -> (fun ret -> U32.v data * (pow2 12) <= U32.v ret /\ U32.v ret < (U32.v data + 1) * (pow2 12))
  | S3 -> (fun ret -> U32.v data * (pow2 18) <= U32.v ret /\ U32.v ret < (U32.v data + 1) * (pow2 18))
  | S2' -> (fun ret -> pow2 11 <= U32.v ret /\ U32.v ret < pow2 12)
  | S3' -> (fun ret -> pow2 16 <= U32.v ret /\ U32.v ret < pow2 18)
  | Init -> (fun ret -> U32.v ret < pow2 21)

let update_term (state : utf8_cp_s) : (data : partial_t {pre_t state data}) -> 
  (ch : ch_t {fail_check state ch = false /\ termination_check state ch = true}) -> 
  (ret : ret_t {post_t state data ret}) =
  match state with
  | S2 | S3 | S2' | S3' -> (fun _ _ -> false_elim ())
  | S1 -> (fun data ch -> 
    assert (U32.v data < pow2 15);
    let _ = Math.Lemmas.pow2_plus 15 6 in
    let _ = Math.Lemmas.pow2_lt_compat 32 21 in
    let b = U8.sub ch 128uy in (U32.add (U32.mul data 64ul) (Cast.uint8_to_uint32 b)))
  | Init -> (fun _ ch -> 
    let _ = Math.Lemmas.pow2_lt_compat 21 7 in
    Cast.uint8_to_uint32 ch)

let update_next (state : utf8_cp_s) : (data : partial_t {pre_t state data}) ->
  (ch : ch_t {fail_check state ch = false /\ termination_check state ch = false}) ->
  (data' : partial_t {pre_t (next_state state ch) data'}) =
  match state with
  | S1 -> (fun _ _ -> false_elim ())
  | S2 -> (fun data ch ->
           let _ = Math.Lemmas.pow2_plus 9 6 in
           let b = U8.sub ch 128uy in (U32.add (U32.mul data 64ul) (Cast.uint8_to_uint32 b)))
  | S3 -> (fun data ch ->
           let _ = Math.Lemmas.pow2_plus 3 6 in
           let b = U8.sub ch 128uy in (U32.add (U32.mul data 64ul) (Cast.uint8_to_uint32 b)))
  | S2' -> (fun _ ch -> 
            let b = U8.sub ch 128uy in 
            assert (32 <= U8.v b /\ U8.v b < 64);
            let _ = Math.Lemmas.pow2_lt_compat 15 6 in
            Cast.uint8_to_uint32 b)
  | S3' -> (fun _ ch -> 
            let b = U8.sub ch 128uy in Cast.uint8_to_uint32 b)
  | Init -> (fun _ ch -> 
           if (U8.v ch < 128 + 64 + 32) then
             let _ = Math.Lemmas.pow2_lt_compat 15 5 in
             Cast.uint8_to_uint32 (U8.sub ch 192uy)
           else if (U8.v ch = 128 + 64 + 32) then
             0ul
           else if (U8.v ch < 128 + 64 + 32 + 16) then
             Cast.uint8_to_uint32 (U8.sub ch 224uy)
           else if (U8.v ch = 128 + 64 + 32 + 16) then
             0ul
           else
             Cast.uint8_to_uint32 (U8.sub ch 240uy))

let lemma_mul_le_le_le (a b c d : nat)
: Lemma (requires (a <= b /\ b * c <= d))
        (ensures (a * c <= d))
= _

let lemma_mul_lt_lt_lt (a b c d : nat)
: Lemma (requires (a < b /\ c < (a + 1) * d))
        (ensures (c < b * d))
= _

#push-options "--z3rlimit 128 --fuel 8 --ifuel 0"

let lemma_cast_ret
  (state : utf8_cp_s)
  (data : partial_t {pre_t state data})
  (ch : ch_t {fail_check state ch = false /\ termination_check state ch = false})
  (ret : ret_t) 
: Lemma (requires (post_t (next_state state ch) (update_next state data ch) ret))
        (ensures (post_t state data ret))
= _

#pop-options

let utf8_cp_dp : automata_data_param utf8_cp_cp = {
  ret_t = ret_t;
  partial_t = partial_t;
  pre_t = pre_t;
  post_t = post_t;
  update_term = update_term;
  update_next = update_next;
  lemma_cast_ret = lemma_cast_ret
}

let utf8_cp_bp : automata_bare_parser_param utf8_cp_cp = {
  ch_t_bare_parser = parse_u8;
  ch_t_bare_parser_valid =
    fun _ -> parser_kind_prop_equiv parse_u8_kind parse_u8
}

#push-options "--z3rlimit 64 --fuel 4 --ifuel 1" // --split_queries"

let lemma_update_term_inj2 
  (state : utf8_cp_s)
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ termination_check state ch1 = true})
  (ch2 : ch_t {fail_check state ch2 = false /\ termination_check state ch2 = true})
: Lemma (requires (update_term state data1 ch1 = update_term state data2 ch2))
        (ensures (data1 = data2 /\ ch1 = ch2))
= _

let lemma_update_term_next_non_intersect
  (state : utf8_cp_s)
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ termination_check state ch1 = true})
  (ch2 : ch_t {fail_check state ch2 = false /\ termination_check state ch2 = false})
  (ret1 : ret_t {post_t state data1 ret1})
  (ret2 : ret_t {post_t (next_state state ch2) (update_next state data2 ch2) ret2})
: Lemma (requires (ret1 = update_term state data1 ch1 /\ ret1 = ret2))
        (ensures False)
= _

let control_s_sym_ord
  (state : utf8_cp_s)
= match state with
  | S1 -> 0 
  | S2 -> 1 
  | S2' -> 2 
  | S3 -> 3 
  | S3' -> 4 
  | Init -> 5

#restart-solver
let lemma_update_next_non_intersect_init_sym
  (data1 : partial_t {pre_t Init data1})
  (data2 : partial_t {pre_t Init data2})
  (ch1 : ch_t {fail_check Init ch1 = false /\ termination_check Init ch1 = false})
  (ch2 : ch_t {fail_check Init ch2 = false /\ termination_check Init ch2 = false})
  (ret1 : ret_t {post_t (next_state Init ch1) (update_next Init data1 ch1) ret1})
  (ret2 : ret_t {post_t (next_state Init ch2) (update_next Init data2 ch2) ret2})
: Lemma (requires (control_s_sym_ord (next_state Init ch1) < control_s_sym_ord (next_state Init ch2) /\ ret1 = ret2))
        (ensures False)
= let state'1 = next_state Init ch1 in
  let state'2 = next_state Init ch2 in
  match state'1 with
  | S1 | S2 | S2' -> _
  | S3 -> match state'2 with
         | S3' -> assert (pow2 18 <= U32.v ret1);
                 assert (U32.v ret2 < pow2 18)

let lemma_update_next_non_intersect 
  (state : utf8_cp_s)
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ termination_check state ch1 = false})
  (ch2 : ch_t {fail_check state ch2 = false /\ termination_check state ch2 = false})
  (ret1 : ret_t {post_t (next_state state ch1) (update_next state data1 ch1) ret1})
  (ret2 : ret_t {post_t (next_state state ch2) (update_next state data2 ch2) ret2})
: Lemma (requires (next_state state ch1 <> next_state state ch2 /\ ret1 = ret2))
        (ensures False)
= match state with
  | S2 | S2' | S3 | S3' | S1 -> false_elim ()
  | Init -> let state'1 = next_state state ch1 in
           let state'2 = next_state state ch2 in
           if (control_s_sym_ord state'1 < control_s_sym_ord state'2) then
             lemma_update_next_non_intersect_init_sym data1 data2 ch1 ch2 ret1 ret2
           else
             lemma_update_next_non_intersect_init_sym data2 data1 ch2 ch1 ret2 ret1
  
let lemma_update_next_inj2
  (state : utf8_cp_s) 
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ termination_check state ch1 = false})
  (ch2 : ch_t {fail_check state ch2 = false /\ termination_check state ch2 = false})
: Lemma (requires next_state state ch1 = next_state state ch2 /\ update_next state data1 ch1 = update_next state data2 ch2)
        (ensures data1 = data2 /\ ch1 = ch2)
= _

#pop-options

let utf8_cp_pp : automata_parser_param utf8_cp_cp utf8_cp_dp utf8_cp_bp = {
  ch_t_parser_valid = (fun _ -> 
    let _ = parser_kind_prop_equiv parse_u8_kind parse_u8 in
    let _ = parser_kind_prop_equiv automata_default_parser_kind parse_u8 in
    _);
  lemma_update_term_inj2 = lemma_update_term_inj2;
  lemma_update_term_next_non_intersect = lemma_update_term_next_non_intersect;
  lemma_update_next_non_intersect = lemma_update_next_non_intersect;  
  lemma_update_next_inj2 = lemma_update_next_inj2  
}

let utf8_cp_parser = automata_parser utf8_cp_cp utf8_cp_dp utf8_cp_bp utf8_cp_pp Init 0ul

let parse_asn1_utf8string : asn1_weak_parser asn1_utf8string_t
= weaken _ (parse_list utf8_cp_parser)
