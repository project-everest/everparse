module ASN1.Spec.Automata

open LowParse.Spec.Base
open LowParse.Spec.Combinators

open LowParse.Spec.Int

open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

open ASN1.Base

let id_cast
  (t : eqtype)
  (p1 : t -> Type0)
  (p2 : t -> Type0)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (x : t {p1 x})
: (x' : t {p2 x'})
= let _ = lem x in
  (x <: (x : t {p2 x}))

let parse_cast
  (t : eqtype)
  (p1 : t -> Type0)
  (p2 : t -> Type0)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x: t {p1 x}))
: (parser k (x : t {p2 x}))
= parse_synth #k #(x : t{p1 x}) #(x : t{p2 x}) p (id_cast t p1 p2 lem)

let parse_cast_eq
  (t : eqtype)
  (p1 : t -> Type0)
  (p2 : t -> Type0)
  (lem : (x : t -> (Lemma (p1 x ==> p2 x))))
  (#k : parser_kind)
  (p : parser k (x : t {p1 x}))
  (b : bytes)
: Lemma (ensures (parse (parse_cast t p1 p2 lem p) b = (match (parse p b) with
                                                       | None -> None
                                                       | Some (x, l) -> Some (id_cast t p1 p2 lem x, l))))
= parse_synth_eq #k #(x : t{p1 x}) #(x : t{p2 x}) p (id_cast t p1 p2 lem) b

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
= let _ = parse_cast_eq t p1 p2 lem p b in
  match (parse p b) with
  | Some (x, l) -> x

let cases_injective2_precond
  (#t1 #t2:Type)
  (#t': Type)
  (gt : t1 -> t' -> Type0)
  (p': ((x : t1) -> t2 -> Tot (bare_parser (y : t' {gt x y}))))
  (x1 x2: t1)
  (y1 y2: t2)
  (b1 b2: bytes)
: GTot Type0
= Some? (parse (p' x1 y1) b1) /\
  Some? (parse (p' x2 y2) b2) /\ (
    let (Some (v1, _)) = parse (p' x1 y1) b1 in
    let (Some (v2, _)) = parse (p' x2 y2) b2 in
    v1 == v2
  )

let cases_injective2
  (#t1 #t2:Type)
  (#t': Type)
  (gt : t1 -> t' -> Type0)
  (p': ((x : t1) -> t2 -> Tot (bare_parser (y : t' {gt x y}))))
: GTot Type0
= forall (x1 x2: t1) (y1 y2 : t2) (b1 b2: bytes) . {:pattern (parse (p' x1 y1) b1); (parse (p' x2 y2) b2)}
  cases_injective2_precond gt p' x1 x2 y1 y2 b1 b2 ==>
  x1 == x2 /\ y1 == y2

let cases_injective2_intro
  (#t1 #t2:Type)
  (#t': Type)
  (gt : t1 -> t' -> Type0)
  (p': ((x : t1) -> t2 -> Tot (bare_parser (y : t' {gt x y}))))
  (lem: (
    (x1: t1) -> 
    (x2: t1) ->
    (y1 : t2) ->
    (y2 : t2) ->
    (b1: bytes) ->
    (b2: bytes) ->
    Lemma
    (requires (cases_injective2_precond gt p' x1 x2 y1 y2 b1 b2))
    (ensures (x1 == x2 /\ y1 == y2))
  ))
: Lemma
  (cases_injective2 gt p')
= Classical.forall_intro (fun x1 -> Classical.forall_intro_4 (fun x2 y1 y2 b1 -> Classical.forall_intro (Classical.move_requires (lem x1 x2 y1 y2 b1))))

let cases_injective2_weaken
  (#t1 #t2:Type)
  (#t': Type)
  (gt : t1 -> t' -> Type0)
  (p': ((x : t1) -> t2 -> Tot (bare_parser (y : t' {gt x y}))))
: Lemma
  (requires cases_injective2 gt p')
  (ensures (forall (x : t1). and_then_cases_injective (p' x)))
= _

noeq
type automata_control_param = {
  control_t : eqtype;
  ch_t : eqtype;
  fail_check : control_t -> ch_t -> bool;
  termination_check : (s : control_t) -> 
                      (ch : ch_t {fail_check s ch = false}) -> bool;
  next_state : (s : control_t) ->
               (ch : ch_t {fail_check s ch = false /\ termination_check s ch = false}) -> control_t;
}

type extend_control_t (t : Type) =
| CFail 
| CTerm 
| CCont : (s : t) -> extend_control_t t

let automata_cp_small_step 
  (cp : automata_control_param)
  (s : cp.control_t)
  (ch : cp.ch_t)
: extend_control_t (cp.control_t)
= if (cp.fail_check s ch) then
    CFail
  else 
    if (cp.termination_check s ch) then
      CTerm
    else
      CCont (cp.next_state s ch)

// Cannot define big step due to non-termination unless finite input

let rec automata_cp_big_step_list
  (cp : automata_control_param)
  (s : cp.control_t)
  (lch : list cp.ch_t)
: Tot (extend_control_t cp.control_t)
  (decreases lch)
= let cur = automata_cp_small_step cp s in
  match lch with
  | [] -> CFail
  | ch :: tl ->
    match (cur ch) with
    | CCont s' -> automata_cp_big_step_list cp s' tl
    | other -> other

type dec (t : Type) = nat -> option t

(*
let dec_count (t : Type) (c : dec t) : dec t =
  fun n -> if n = 0 then
          None
        else 
          c (n - 1)
*)

let rec dec_fix'
  (s : Type)
  (t : Type)
  (f : s -> (k : nat) -> (s -> ((m : nat {m <= k}) -> option t)) -> option t)
  (x : s)
  (n : nat)
: Tot (option t)
  (decreases n)
= if n = 0 then
    None
  else 
    f x (n - 1) (fun y (m : nat {m <= n - 1}) -> dec_fix' s t f y m) 


noeq
type automata_data_param (cp : automata_control_param) = {
  ret_t : eqtype;
  partial_t : eqtype;
  pre_t : cp.control_t -> partial_t -> Type0;
  post_t : (s : cp.control_t) -> 
           (data : partial_t {pre_t s data}) ->
           ret_t -> Type0;
  update_term : (s : cp.control_t) ->
                (data : partial_t {pre_t s data}) ->
                (ch : cp.ch_t {cp.fail_check s ch = false /\ cp.termination_check s ch = true}) ->
                (ret : ret_t {post_t s data ret});
  update_next : (s : cp.control_t) ->
                (data : partial_t {pre_t s data}) ->
                (ch : cp.ch_t {cp.fail_check s ch = false /\ cp.termination_check s ch = false}) ->
                (data' : partial_t {pre_t (cp.next_state s ch) data'});
  lemma_cast_ret : (state : cp.control_t) ->
                   (data : partial_t {pre_t state data}) ->
                   (ch : cp.ch_t {cp.fail_check state ch = false /\ cp.termination_check state ch = false}) ->
                   (ret : ret_t) ->
                   (post_t (cp.next_state state ch) (update_next state data ch) ret ==> post_t state data ret)
}

type extend_control_data_t
  (cp : automata_control_param)
  (dp : automata_data_param cp)
= | DFail
  | DTerm : dp.ret_t -> extend_control_data_t cp dp
  | DCont : (s : cp.control_t) -> (data : dp.partial_t {dp.pre_t s data}) -> extend_control_data_t cp dp

let automata_cp_dp_small_step
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (ch : cp.ch_t)
: extend_control_data_t cp dp
= if cp.fail_check s ch then
    DFail
  else
    if cp.termination_check s ch then
      DTerm (dp.update_term s data ch)
    else 
      DCont (cp.next_state s ch) (dp.update_next s data ch)

noeq
type automata_bare_parser_param (cp : automata_control_param) = {
  ch_t_bare_parser : bare_parser cp.ch_t;
  ch_t_bare_parser_valid : 
    (forall (b : bytes). match (parse ch_t_bare_parser b) with
                    | Some (_, n) -> n > 0
                    | None -> True);
}

let rec automata_bare_parser'
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
  (b : bytes)
: Tot (option (tuple2 (ret : dp.ret_t {dp.post_t s data ret}) (consumed_length b)))
  (decreases (Seq.length b))
= match (parse bp.ch_t_bare_parser b) with
  | None -> None
  | Some (ch, l) ->
    if cp.fail_check s ch then
      None
    else
      if cp.termination_check s ch then
        Some (dp.update_term s data ch, l)
      else
        (
        let s' = cp.next_state s ch in
        let data' = dp.update_next s data ch in
        let _ = bp.ch_t_bare_parser_valid in
        let (b' : bytes{Seq.length b' < Seq.length b}) = Seq.slice b l (Seq.length b) in
        match (automata_bare_parser' cp dp bp s' data' b') with
        | None -> None
        | Some (ret, l') ->
          Some (id_cast dp.ret_t (dp.post_t s' data') (dp.post_t s data) (dp.lemma_cast_ret s data ch) ret, l + l')
        )

let automata_bare_parser
  (cp : automata_control_param)
  (dp : automata_data_param cp)
  (bp : automata_bare_parser_param cp)
  (s : cp.control_t)
  (data : dp.partial_t {dp.pre_t s data})
: (bare_parser (ret : dp.ret_t {dp.post_t s data ret}))
= automata_bare_parser' cp dp bp s data

(*

noeq
type automata_parser_param (cp : automata_control_param) (dp : automata_data_param cp) = {
  ch_t_parser_kind : parser_kind;
  ch_t_parser : parser ch_t_parser_kind cp.ch_t;
  ch_t_parser_valid : 
    (forall (b : bytes). match (parse ch_t_parser b) with
                    | Some (_, n) -> n > 0
                    | None -> True);
                          
}
*) 

(*
  ch_t_parser_kind : parser_kind;
  ch_t_parser : parser ch_t_parser_kind cp.ch_t;


*)

(*

// Control plane

// assume val control_t : eqtype

type control_t =
| Init | S3' | S3 | S2' | S2 | S1

let ord (s : control_t) : nat =
  match s with
  | S1 -> 0
  | S2 | S2' -> 1
  | S3 | S3' -> 2
  | Init -> 3

// assume val ch_t : eqtype

let ch_t = U8.t

//  assume val ch_t_parser_kind : parser_kind

let ch_t_parser_kind = parse_u8_kind

// assume val ch_t_parser : parser ch_t_parser_kind ch_t

let ch_t_parser : parser ch_t_parser_kind ch_t = parse_u8

// assume val fail_check : control_t -> ch_t -> bool

let out_range_common (ch : ch_t) =
  U8.v ch < 128 || 128 + 64 <= U8.v ch

let out_range_s2' (ch : ch_t) =
  U8.v ch < 128 + 32 || 128 + 64 <= U8.v ch

let out_range_s3' (ch : ch_t) =
  U8.v ch < 128 + 16 || 128 + 64 <= U8.v ch

let out_range_init (ch : ch_t) =
  (128 <= U8.v ch && U8.v ch <= 128 + 64) || 248 <= U8.v ch

let fail_check (s : control_t) : ch_t -> bool =
  match s with
  | S1 | S2 | S3 -> out_range_common
  | S2' -> out_range_s2'
  | S3' -> out_range_s3'
  | Init -> out_range_init

// assume val terminate_check : (state : control_t) -> (ch : ch_t {fail_check state ch = false}) -> bool

let terminate_check (s : control_t) =
  match s with
  | S1 -> fun _ -> true
  | S2 | S3 | S2' | S3' -> fun _ -> false
  | Init -> (fun (ch : ch_t {fail_check s ch = false}) -> U8.v ch < 128)

// assume val next_state : (state : control_t) -> (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = false}) -> (state' : control_t {state' << state})

let next_state (s : control_t) (ch : ch_t {fail_check s ch = false /\ terminate_check s ch = false}) : (s' : control_t {ord s' << ord s}) =
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

// Data plane

// assume val ret_t : eqtype

let ret_t = U32.t

// assume val partial_t : eqtype

let partial_t = U32.t
  
// assume val pre_t : control_t -> partial_t -> Type0

let pre_t (s : control_t) : partial_t -> Type0 =
  match s with
  | S1 -> (fun data -> 0 < U32.v data /\ U32.v data < pow2 26)
  | S2 -> (fun data -> 0 < U32.v data /\ U32.v data < pow2 20)
  | S3 -> (fun data -> 0 < U32.v data /\ U32.v data < pow2 14)
  | S2' | S3' | Init -> (fun data -> U32.v data = 0)

// assume val post_t : (s : control_t) -> (data : partial_t {pre_t s data}) -> ret_t -> Type0

let post_t (s : control_t) (data : partial_t {pre_t s data}) : ret_t -> Type0 =
  match s with
  | S1 -> (fun data' -> U32.v data * (pow2 6) <= U32.v data' /\ U32.v data' < (U32.v data + 1) * (pow2 6))
  | S2 -> (fun data' -> U32.v data * (pow2 12) <= U32.v data' /\ U32.v data' < (U32.v data + 1) * (pow2 12))
  | S3 -> (fun data' -> U32.v data * (pow2 18) <= U32.v data' /\ U32.v data' < (U32.v data + 1) * (pow2 18))
  | S2' -> (fun data' -> pow2 11 <= U32.v data' /\ U32.v data' < pow2 12)
  | S3' -> (fun data' -> pow2 16 <= U32.v data' /\ U32.v data' < pow2 18)
  | Init -> (fun data' -> U32.v data' < pow2 21)

// assume val ret_t_parser_kind : control_t -> parser_kind

let ret_t_parser_kind (s : control_t) : parser_kind = asn1_strong_parser_kind

//assume val update_term : (state : control_t) -> (data : partial_t {pre_t state data}) -> 
//  (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = true}) -> 
//  (ret : ret_t {post_t state data ret}) 

let update_term (state : control_t) : (data : partial_t {pre_t state data}) -> 
  (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = true}) -> 
  (ret : ret_t {post_t state data ret}) =
  match state with
  | S2 | S3 | S2' | S3' -> (fun _ _ -> false_elim ())
  | S1 -> (fun data ch -> let b = U8.sub ch 128uy in (U32.add (U32.mul data 64ul) (Cast.uint8_to_uint32 b)))
  | Init -> (fun _ ch -> Cast.uint8_to_uint32 ch)

assume val lemma_update_term_inj2 (state : control_t) 
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ terminate_check state ch1 = true})
  (ch2 : ch_t {fail_check state ch2 = false /\ terminate_check state ch2 = true})
: Lemma (requires (update_term state data1 ch1 = update_term state data2 ch2))
        (ensures (data1 = data2 /\ ch1 = ch2))

//assume val update_next : (state : control_t) -> (data : partial_t {pre_t state data}) ->
//  (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = false}) ->
//  (data' : partial_t {pre_t (next_state state ch) data'})

let update_next (state : control_t) : (data : partial_t {pre_t state data}) ->
  (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = false}) ->
  (data' : partial_t {pre_t (next_state state ch) data'}) =
  match state with
  | S1 -> (fun _ _ -> false_elim ())
  | S2 -> (fun data ch ->
           let _ = Math.Lemmas.pow2_plus 20 6 in
           let b = U8.sub ch 128uy in (U32.add (U32.mul data 64ul) (Cast.uint8_to_uint32 b)))
  | S3 -> (fun data ch ->
           let _ = Math.Lemmas.pow2_plus 14 6 in
           let b = U8.sub ch 128uy in (U32.add (U32.mul data 64ul) (Cast.uint8_to_uint32 b)))
  | S2' -> (fun _ ch -> 
            let b = U8.sub ch 128uy in 
            assert (32 <= U8.v b /\ U8.v b < 64);
            let _ = Math.Lemmas.pow2_lt_compat 26 6 in
            Cast.uint8_to_uint32 b)
  | S3' -> (fun _ ch -> 
            let b = U8.sub ch 128uy in Cast.uint8_to_uint32 b)
  | Init -> (fun _ ch -> 
           if (U8.v ch < 128 + 64 + 32) then
             let _ = Math.Lemmas.pow2_lt_compat 26 5 in
             Cast.uint8_to_uint32 (U8.sub ch 192uy)
           else if (U8.v ch = 128 + 64 + 32) then
             0ul
           else if (U8.v ch < 128 + 64 + 32 + 16) then
             Cast.uint8_to_uint32 (U8.sub ch 224uy)
           else if (U8.v ch = 128 + 64 + 32 + 16) then
             0ul
           else
             Cast.uint8_to_uint32 (U8.sub ch 240uy))

assume val lemma_update_term_next_non_intersect 
  (state : control_t) 
  (data1 : partial_t {pre_t state data1})
  (ch1 : ch_t {fail_check state ch1 = false /\ terminate_check state ch1 = true})
  (ch2 : ch_t {fail_check state ch2 = false /\ terminate_check state ch2 = false})
  (ret1 : ret_t {post_t state data1 ret1})
  (ret2 : ret_t {post_t (next_state state ch2) (update_next state data1 ch2) ret2})
: Lemma (requires (ret1 = update_term state data1 ch1 /\ ret1 = ret2))
        (ensures False)

assume val lemma_update_next_non_intersect
  (state : control_t) 
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ terminate_check state ch1 = false})
  (ch2 : ch_t {fail_check state ch2 = false /\ terminate_check state ch2 = false})
  (ret1 : ret_t {post_t (next_state state ch1) (update_next state data1 ch1) ret1})
  (ret2 : ret_t {post_t (next_state state ch2) (update_next state data2 ch2) ret2})
: Lemma (requires (next_state state ch1 <> next_state state ch2 /\ ret1 = ret2))
        (ensures False)

assume val lemma_update_next_inj2
  (state : control_t) 
  (data1 : partial_t {pre_t state data1})
  (data2 : partial_t {pre_t state data2})
  (ch1 : ch_t {fail_check state ch1 = false /\ terminate_check state ch1 = false})
  (ch2 : ch_t {fail_check state ch2 = false /\ terminate_check state ch2 = false})
: Lemma (requires next_state state ch1 = next_state state ch2 /\ update_next state data1 ch1 = update_next state data2 ch2)
        (ensures data1 = data2 /\ ch1 = ch2)

assume val lemma_cast_ret (state : control_t) (data : partial_t {pre_t state data}) (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = false}) (ret : ret_t)
: Lemma (post_t (next_state state ch) (update_next state data ch) ret ==> post_t state data ret)

assume val lemma_parser_kind1
  (state : control_t)
  (ch : ch_t {fail_check state ch = true})
: Lemma (fail_parser_kind_precond (ret_t_parser_kind state))

assume val lemma_parser_kind2
  (state : control_t)
  (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = true})
: Lemma (ret_t_parser_kind state `is_weaker_than` parse_ret_kind)

assume val lemma_parser_kind3
  (state : control_t)
  (ch : ch_t {fail_check state ch = false /\ terminate_check state ch = false})
: Lemma (ret_t_parser_kind state `is_weaker_than` (and_then_kind ch_t_parser_kind (ret_t_parser_kind (next_state state ch))))

let reachable_1 (state state' : control_t) =
  exists ch. next_state state ch = state'

let lemma_reachable_1 (state state' : control_t) :
  Lemma (requires (reachable_1 state state'))
        (ensures (ord state' << ord state))
= _

let parse_automata_gt (state : control_t) : (data : partial_t {pre_t state data}) -> ret_t -> Type0 = fun data -> post_t state data 

let parse_automata_type (state : control_t) = (data : partial_t {pre_t state data}) -> (ch : ch_t) -> parser (ret_t_parser_kind state) (ret : ret_t {parse_automata_gt state data ret})

let parse_automata_spec (state : control_t) (p : parse_automata_type state)
= cases_injective2 (parse_automata_gt state) p

let parse_automata' 
  (state : control_t)
  (fp : (state' : control_t {reachable_1 state state'}) -> parse_automata_type state')
  (data : partial_t {pre_t state data})
  (ch : ch_t)
: Pure (parser (ret_t_parser_kind state) (ret : ret_t {post_t state data ret}))
  (requires (forall state'. parse_automata_spec state' (fp state')))
  (ensures (fun _ -> True))
= let k = ret_t_parser_kind state in
  if fail_check state ch then
    let _ = lemma_parser_kind1 state ch in
    fail_parser k (ret : ret_t {post_t state data ret})
  else 
    (
    if terminate_check state ch then
      let _ = lemma_parser_kind2 state ch in
      weaken k (parse_ret (update_term state data ch))
    else
      (
        let state' = next_state state ch in
        let data' = update_next state data ch in
        let _ = cases_injective2_weaken (parse_automata_gt state') (fp state') in
        let p = ch_t_parser `and_then` (fp state' data') in
        let p' = 
          parse_cast
          ret_t
          (post_t state' data')
          (post_t state data)
          (lemma_cast_ret state data ch)
          p
        in
        let _ = lemma_parser_kind3 state ch in
        weaken k p'
      )
    )

let lemma_parse_automata'_inj2
  (state : control_t)
  (fp : (state' : control_t {reachable_1 state state'}) -> parse_automata_type state')  
: Lemma (requires (forall state'. parse_automata_spec state' (fp state')))
        (ensures (parse_automata_spec state (parse_automata' state fp)))
= let p = parse_automata' state fp in
  cases_injective2_intro (parse_automata_gt state) p (fun data1 data2 ch1 ch2 bytes1 bytes2 ->
    match parse (p data1 ch1) bytes1 with | Some (ret1, l1) -> 
    match parse (p data2 ch2) bytes2 with | Some (ret2, l2) ->   
    if (fail_check state ch1) then
      _
    else
      if (fail_check state ch2) then
        _
      else
        (
        if (terminate_check state ch1) then
        (
          if (terminate_check state ch2) then
            let _ : squash (fail_check state ch1 = false /\ terminate_check state ch1 = true) = _ in
            let _ : squash (fail_check state ch2 = false /\ terminate_check state ch2 = true) = _ in
            lemma_update_term_inj2 state data1 data2 ch1 ch2
          else
          (
            let _ : squash (fail_check state ch1 = false /\ terminate_check state ch1 = true) = _ in
            let _ : squash (fail_check state ch2 = false /\ terminate_check state ch2 = false) = _ in
            let state'2 = next_state state ch2 in
            let data'2 = update_next state data2 ch2 in
            let _ = cases_injective2_weaken (parse_automata_gt state'2) (fp state'2) in
            let p = ch_t_parser `and_then` (fp state'2 data'2) in
            let ret2' = 
              parse_cast_inverse
              ret_t
              (post_t state'2 data'2)
              (post_t state data2)
              (lemma_cast_ret state data2 ch2)
              p
              bytes2
              ret2
              l2
            in
            lemma_update_term_next_non_intersect state data1 ch1 ch2 ret1 ret2'
          )
        )
        else
        (
          if (terminate_check state ch2) then
          (
            let _ : squash (fail_check state ch1 = false /\ terminate_check state ch1 = false) = _ in
            let _ : squash (fail_check state ch2 = false /\ terminate_check state ch2 = true) = _ in
            let state'1 = next_state state ch1 in
            let data'1 = update_next state data1 ch1 in
            let _ = cases_injective2_weaken (parse_automata_gt state'1) (fp state'1) in
            let p = ch_t_parser `and_then` (fp state'1 data'1) in
            let ret1' = 
              parse_cast_inverse
              ret_t
              (post_t state'1 data'1)
              (post_t state data1)
              (lemma_cast_ret state data1 ch1)
              p
              bytes1
              ret1
              l1
            in
            lemma_update_term_next_non_intersect state data2 ch2 ch1 ret2 ret1'
          )
          else
          (
            let _ : squash (fail_check state ch1 = false /\ terminate_check state ch1 = false) = _ in
            let _ : squash (fail_check state ch2 = false /\ terminate_check state ch2 = false) = _ in
            let state'1 = next_state state ch1 in
            let state'2 = next_state state ch2 in
            let data'1 = update_next state data1 ch1 in
            let data'2 = update_next state data2 ch2 in
            if (state'1 = state'2) then
            (
              let _ = cases_injective2_weaken (parse_automata_gt state'1) (fp state'1) in
              let p1 = ch_t_parser `and_then` (fp state'1 data'1) in
              let _ = parse_cast_eq
                ret_t
                (post_t state'1 data'1)
                (post_t state data1)
                (lemma_cast_ret state data1 ch1)
                p1
                bytes1
              in
              let _ = and_then_eq ch_t_parser (fp state'1 data'1) bytes1 in
              match (parse ch_t_parser bytes1) with | Some (ch'1, l'1) -> let bytes'1 : bytes = Seq.slice bytes1 l'1 (Seq.length bytes1) in
              let _ = cases_injective2_weaken (parse_automata_gt state'2) (fp state'2) in
              let p2 = ch_t_parser `and_then` (fp state'2 data'2) in
              let _ = parse_cast_eq
                ret_t
                (post_t state'2 data'2)
                (post_t state data2)
                (lemma_cast_ret state data2 ch2)
                p2
                bytes2
              in
              let _ = and_then_eq ch_t_parser (fp state'2 data'2) bytes2 in
              match (parse ch_t_parser bytes2) with | Some (ch'2, l'2) -> let bytes'2 : bytes = Seq.slice bytes2 l'2 (Seq.length bytes2) in
              let fp' = fp state'1 in
              assert (cases_injective2_precond (parse_automata_gt state'1) fp' data'1 data'2 ch'1 ch'2 bytes'1 bytes'2);
              assert (data'1 = data'2);
              lemma_update_next_inj2 state data1 data2 ch1 ch2
            )
            else
            (
              let _ = cases_injective2_weaken (parse_automata_gt state'1) (fp state'1) in
              let p1 = ch_t_parser `and_then` (fp state'1 data'1) in
              let ret1' = 
                parse_cast_inverse
                ret_t
                (post_t state'1 data'1)
                (post_t state data1)
                (lemma_cast_ret state data1 ch1)
                p1
                bytes1
                ret1
                l1
              in
              let _ = cases_injective2_weaken (parse_automata_gt state'2) (fp state'2) in
              let p2 = ch_t_parser `and_then` (fp state'2 data'2) in
              let ret2' = 
                parse_cast_inverse
                ret_t
                (post_t state'2 data'2)
                (post_t state data2)
                (lemma_cast_ret state data2 ch2)
                p2
                bytes2
                ret2
                l2
              in
              lemma_update_next_non_intersect state data1 data2 ch1 ch2 ret1' ret2'
            )
          )
        )
        )
    )

let rec parse_automata'' 
  (state : control_t)
: Pure (parse_automata_type state)
  (requires True)
  (ensures (fun p -> parse_automata_spec state p))
  (decreases %[ord state]) 
= let _ = lemma_parse_automata'_inj2 state (parse_automata'') in
  parse_automata' state (parse_automata'')

assume val initial_state : control_t

assume val initial_data : (data : partial_t {pre_t initial_state data})

let parse_automata = parse_automata'' initial_state initial_data
*)
