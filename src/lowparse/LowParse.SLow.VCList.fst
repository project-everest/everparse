module LowParse.SLow.VCList
include LowParse.Spec.VCList
include LowParse.SLow.List

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot
module B32 = LowParse.Bytes32

let rec parse_nlist_tailrec
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (accu: list t * nat)
  (b: bytes)
: GTot (option (list t * nat))
= if n = 0
  then Some accu
  else
    match parse p b with
    | Some (elem, consumed) ->
      let (l0, consumed0) = accu in
      let b' = Seq.slice b consumed (Seq.length b) in
      parse_nlist_tailrec (n - 1) p (elem :: l0, consumed0 + consumed) b'
    | _ -> None

let rec parse_nlist_tailrec_correct'
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (accu: list t * nat)
  (b: bytes)
: Lemma
  (match parse_nlist_tailrec n p accu b, parse (parse_nlist n p) b with
    | None, None -> True
    | Some (l', consumed'), Some (l, consumed) ->
      let (l0, consumed0) = accu in
      consumed' == consumed0 + consumed /\ l' == L.rev l `L.append` l0
    | _ -> False)
= parse_nlist_eq n p b;
  if n = 0
  then ()
  else begin
    match parse p b with
    | None -> ()
    | Some (elem1, consumed1) ->
      let (l0, consumed0) = accu in
      let b' = Seq.slice b consumed1 (Seq.length b) in
      parse_nlist_tailrec_correct' (n - 1) p (elem1 :: l0, consumed0 + consumed1) b' ;
      match parse (parse_nlist (n - 1) p) b' with
      | None -> ()
      | Some (l2, consumed2) ->
        L.rev_rev' (elem1 :: l2);
        L.rev_rev' l2;
        L.append_assoc (L.rev l2) [elem1] l0
  end

let parse_nlist_tailrec_correct
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma
  (match parse_nlist_tailrec n p ([], 0) b, parse (parse_nlist n p) b with
    | None, None -> True
    | Some (l', consumed'), Some (l, consumed) ->
      consumed' == consumed /\ l == L.rev l'
    | _ -> False)
= parse_nlist_tailrec_correct' n p ([], 0) b;
  match parse (parse_nlist n p) b with
  | None -> ()
  | Some (l, _) ->
    L.append_l_nil (L.rev l);
    L.rev_involutive l

let parse_nlist_tailrec_inv
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (accu: list t * nat)
  (input: bytes32)
  (b: bool)
  (x: option (bytes32 * U32.t * list t * U32.t))
: GTot Type0
= match x with
  | Some (input', i, accu', consumed') ->
    U32.v i <= U32.v n /\
    U32.v consumed' + B32.length input' < 4294967296 /\
    parse_nlist_tailrec (U32.v n) p accu (B32.reveal input) == parse_nlist_tailrec (U32.v n - U32.v i) p (accu', U32.v consumed') (B32.reveal input') /\
    (b == false ==> i == n)
  | None ->
    b == false /\ None? (parse_nlist_tailrec (U32.v n) p accu (B32.reveal input))

let parse_nlist_tailrec_measure
  (#t: Type)
  (n: U32.t)
  (x: option (bytes32 * U32.t * list t * U32.t))
: GTot nat
= match x with
  | None -> 0
  | Some (_, i', _, _) -> if U32.v i' > U32.v n then 0 else (U32.v n - U32.v i' + 1)

inline_for_extraction
let parse_nlist_body
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
  (x: option (bytes32 * U32.t * list t * U32.t))
: Pure (bool * option (bytes32 * U32.t * list t * U32.t))
  (requires (parse_nlist_tailrec_inv n p ([], 0) input true x))
  (ensures (fun (continue, y) ->
    parse_nlist_tailrec_inv n p ([], 0) input continue y /\
    (if continue then parse_nlist_tailrec_measure n y < parse_nlist_tailrec_measure n x else True)
  ))
= match x with
  | Some (input', i, accu', consumed') ->
    if i = n
    then (false, x)
    else
      match p32 input' with
      | None -> (false, None)
      | Some (y, consumed1) ->
        let input2 = B32.slice input' consumed1 (B32.len input') in
        (true, Some (input2, i `U32.add` 1ul, y :: accu', consumed' `U32.add` consumed1))

inline_for_extraction
let parse32_nlist
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_nlist (U32.v n) p))
= fun input -> ((
    parse_nlist_tailrec_correct (U32.v n) p  (B32.reveal input);
    let res =
      C.Loops.total_while
        (parse_nlist_tailrec_measure n)
        (parse_nlist_tailrec_inv n p ([], 0) input)
        (fun x -> parse_nlist_body n p32 input x)
        (Some (input, 0ul, [], 0ul))
    in
    match res with
    | Some (_, _, accu, consumed) ->
      Some (list_rev accu, consumed)
    | None -> None
  ) <: Tot (res: _ { parser32_correct (parse_nlist (U32.v n) p) input res } ))

let serialize32_nlist_precond
  (n: nat)
  (k: parser_kind)
: GTot Type0
= k.parser_kind_subkind == Some ParserStrong /\ (
    match k.parser_kind_high with
    | None -> False
    | Some hi -> n `FStar.Mul.op_Star` hi < 4294967296
  )

#push-options "--z3rlimit 100"

inline_for_extraction
let serialize32_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (u: squash (
    serialize32_nlist_precond n k
  ))
: Tot (serializer32 (serialize_nlist (n) s))
= fun (input: nlist (n) t) -> ((
    [@inline_let] let _ =
      assert_norm (pow2 32 == 4294967296);
      B32.reveal_empty ();
      parse_nlist_kind_high (n) k;
      Seq.append_empty_l (serialize (serialize_nlist (n) s) input)
    in
    let x = C.Loops.total_while
      (fun (x: (list t * bytes32)) -> L.length (fst x))
      (fun (continue: bool) (x: (list t * bytes32)) ->
        serialize (serialize_nlist (n) s) input == B32.reveal (snd x) `Seq.append` serialize (serialize_nlist (L.length (fst x)) s) (fst x) /\
        (continue == false ==> fst x == [])
      )
      (fun (x: (list t * bytes32)) ->
         match x with
         | [], res -> (false, x)
         | a :: q, res ->
           let sa = s32 a in
           [@inline_let] let _ =
             serialize_nlist_cons (L.length q) s a q;
             Seq.append_assoc (B32.reveal res) (B32.reveal sa) (serialize (serialize_nlist (L.length q) s) q);
             assert (B32.length res + B32.length sa + Seq.length (serialize (serialize_nlist (L.length q) s) q) == Seq.length (serialize (serialize_nlist (n) s) input))
           in
           let res' = res `B32.append` sa in
           (true, (q, res'))
      )
      (input, B32.empty_bytes)
    in
    match x with
    | (_, res) ->
      [@inline_let] let _ =
        serialize_nlist_nil _ s;
        Seq.append_empty_r (B32.reveal res)
      in
      res
  ) <: (res: _ { serializer32_correct (serialize_nlist (n) s) input res }))

#pop-options

#push-options "--z3rlimit 64 --initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0"

inline_for_extraction
let size32_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: squash (
    serialize32_nlist_precond n k
  ))
: Tot (size32 (serialize_nlist (n) s))
= fun (input: nlist (n) t) -> ((
    [@inline_let] let _ =
      assert_norm (pow2 32 == 4294967296);
      B32.reveal_empty ();
      parse_nlist_kind_high (n) k
    in
    let x = C.Loops.total_while
      (fun (x: (list t * U32.t)) -> L.length (fst x))
      (fun (continue: bool) (x: (list t * U32.t)) ->
        Seq.length (serialize (serialize_nlist (n) s) input) == U32.v (snd x) + Seq.length (serialize (serialize_nlist (L.length (fst x)) s) (fst x)) /\
        (continue == false ==> fst x == [])
      )
      (fun (x: (list t * U32.t)) ->
         match x with
         | [], res -> (false, x)
         | a :: q, res ->
           let sa = s32 a in
           [@inline_let] let _ =
             serialize_nlist_cons (L.length q) s a q;
             assert (U32.v res + U32.v sa + Seq.length (serialize (serialize_nlist (L.length q) s) q) == Seq.length (serialize (serialize_nlist (n) s) input))
           in
           let res' = res `U32.add` sa in
           (true, (q, res'))
      )
      (input, 0ul)
    in
    match x with
    | (_, res) ->
      res
  ) <: (res: _ { size32_postcond (serialize_nlist (n) s) input res }))

#pop-options

inline_for_extraction
let parse32_vclist_payload
  (min max: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (n: bounded_count min max)
: Tot (parser32 (parse_vclist_payload min max p n))
= (fun (x: bytes32) -> ((
     parse32_synth'
       _
       (synth_vclist_payload min max n)
       (parse32_nlist n p32)
       ()
       x
  ) <: (res: _ { parser32_correct (parse_vclist_payload min max p n) x res } )))

inline_for_extraction
let parse32_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (lp32: parser32 lp)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_vclist (U32.v min) (U32.v max) lp p))
= parse32_and_then
    (parse32_synth'
      _
      (synth_bounded_count (U32.v min) (U32.v max))
      (parse32_filter
        lp32
        (bounded_count_prop (U32.v min) (U32.v max))
        (fun x -> not (x `U32.lt` min || max `U32.lt` x))
      )
      ()
    )
    (parse_vclist_payload (U32.v min) (U32.v max) p)
    ()
    (parse32_vclist_payload (U32.v min) (U32.v max) p32)

let serialize32_vclist_precond
  (min: nat)
  (max: nat { min <= max } )
  (lk: parser_kind)
  (k: parser_kind)
: GTot Type0
= match lk.parser_kind_high, k.parser_kind_high with
  | Some lhi, Some hi ->
    lhi + (max `FStar.Mul.op_Star` hi) < 4294967296
  | _ -> False

inline_for_extraction
let list_length32
  (#t: Type)
  (l: list t { L.length l < 4294967296 } )
: Tot (x: U32.t { U32.v x == L.length l } )
= match C.Loops.total_while
    (fun (_, l') -> L.length l')
    (fun continue (len, l') ->
      L.length l == U32.v len + L.length l' /\
      (continue == false ==> l' == []))
    (fun x ->
      match x with
      | (len, l') ->
        begin match l' with
        | [] -> (false, x)
        | _ :: q -> (true, (len `U32.add` 1ul, q))
        end
    )
    (0ul, l)
  with (len, _) -> len

#push-options "--z3rlimit 16 --max_fuel 1"
inline_for_extraction
let serialize32_vclist
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (#ls: serializer lp)
  (ls32: serializer32 ls { lk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s { k.parser_kind_subkind == Some ParserStrong /\ serialize32_vclist_precond min max lk k })
: Tot (serializer32 (serialize_vclist min max ls s))
= fun (x: vlarray t min max) -> ((
    let ln = list_length32 x in
    let sn = ls32 ln in
    [@inline_let] let _ = LowParse.Math.lemma_mult_le_right (Some?.v k.parser_kind_high) (U32.v ln) max in
    let sl = serialize32_nlist (U32.v ln) s32 () x in
    sn `B32.append` sl
  ) <: (res: _ { serializer32_correct (serialize_vclist min max ls s) x res } ))
#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
let size32_vclist
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#lk: parser_kind)
  (#lp: parser lk U32.t)
  (#ls: serializer lp)
  (ls32: size32 ls { lk.parser_kind_subkind == Some ParserStrong } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s { k.parser_kind_subkind == Some ParserStrong /\ serialize32_vclist_precond min max lk k })
: Tot (size32 (serialize_vclist min max ls s))
= fun x -> ((
    let ln = list_length32 x in
    let sn = ls32 ln in
    [@inline_let] let _ = LowParse.Math.lemma_mult_le_right (Some?.v k.parser_kind_high) (U32.v ln) max in
    let sl = size32_nlist (U32.v ln) s32 () x in
    sn `U32.add` sl
  ) <: (res: _ { size32_postcond (serialize_vclist min max ls s) x res } ))

#pop-options
