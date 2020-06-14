module LowParse.SLow.List
include LowParse.Spec.List
include LowParse.SLow.Combinators

module B32 = FStar.Bytes
module U32 = FStar.UInt32
module CL = C.Loops

#set-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8"

module L = FStar.List.Tot

let rec parse_list_tailrec'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (b: bytes32)
  (aux: list t)
: GTot (option (list t))
  (decreases (B32.length b))
= parse_list_eq p (B32.reveal b);
  if B32.len b = 0ul
  then 
    Some (L.rev aux)
  else
    match p32 b with
    | None -> None
    | Some (v, n) ->
      if n = 0ul
      then None (* elements cannot be empty *)
      else
	parse_list_tailrec' p32 (B32.slice b n (B32.len b)) (v :: aux)

let list_append_rev_cons
  (#t: Type)
  (v: t) 
  (aux l: list t)
: Lemma (L.append (L.rev (v ::aux)) l == L.append (L.rev aux) (v :: l))
= L.rev_rev' (v :: aux);
  L.rev_rev' aux;
  L.append_assoc (L.rev aux) [v] l

let rec parse_list_tailrec'_correct'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (b: bytes32)
  (aux: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec' p32 b aux == (
    match parse (parse_list p) (B32.reveal b) with
    | Some (l, n) -> Some (L.append (L.rev aux) l)
    | None -> None
  )))
  (decreases (B32.length b))
= parse_list_eq p (B32.reveal b);
  if B32.len b = 0ul
  then
    L.append_l_nil (L.rev aux)
  else
    match p32 b with
    | None -> ()
    | Some (v, n) ->
      if n = 0ul
      then ()
      else begin
	let s = B32.slice b n (B32.len b) in
	parse_list_tailrec'_correct' p32 s (v :: aux);
	match parse (parse_list p) (B32.reveal s) with
	| Some (l, n') ->
          list_append_rev_cons v aux l
        | None -> ()
      end

let parse_list_tailrec'_correct
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (b: bytes32)
: Lemma
  begin match parse (parse_list p) (B32.reveal b) with
  | Some (l, n) -> parse_list_tailrec' p32 b [] == Some l
  | None -> parse_list_tailrec' p32 b [] == None
  end
= parse_list_tailrec'_correct' p32 b []

let list_rev_inv
  (#t: Type)
  (l: list t)
  (b: bool)
  (x: list t * list t)
: GTot Type0
= let (rem, acc) = x in
  L.rev l == L.rev_acc rem acc /\
  (b == false ==> rem == [])

let list_rev
  (#t: Type)
  (l: list t)
: Tot (l' : list t { l' == L.rev l } )
= match l with
  | [] -> []
  | _ ->
    let (_, l') =
      CL.total_while
        (fun (rem, _) -> L.length rem)
        (list_rev_inv l)
        (fun (rem, acc) ->
          match rem with
          | [] -> (false, (rem, acc))
          | a :: q -> (true, (q, a :: acc))
        )
        (l, [])
    in
    l'

let parse_list_tailrec_inv
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
  (b: bool)
  (x: option (bytes32 * list t))
: GTot Type0
= match x with
  | Some (input', accu') ->
    parse_list_tailrec' p32 input [] == parse_list_tailrec' p32 input' accu' /\
    (b == false ==> B32.length input' == 0)
  | None -> 
    b == false /\ None? (parse_list_tailrec' p32 input [])

let parse_list_tailrec_measure
  (#t: Type)
  (x: option (bytes32 * list t))
: GTot nat
= match x with
  | None -> 0
  | Some (input', _) -> B32.length input'

inline_for_extraction
let parse_list_tailrec_body
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: (x: option (bytes32 * list t)) ->
  Pure (bool * option (bytes32 * list t))
  (requires (parse_list_tailrec_inv p32 input true x))
  (ensures (fun (continue, y) ->
    parse_list_tailrec_inv p32 input continue y /\
    (if continue then parse_list_tailrec_measure y < parse_list_tailrec_measure x else True)
  ))
= fun (x: option (bytes32 * list t)) ->
  let (Some (input', accu')) = x in
  let len = B32.len input' in
  if len = 0ul
  then (false, x)
  else
    match p32 input' with
    | Some (v, consumed) ->
      if consumed = 0ul
      then (false, None)
      else
        let input'' = B32.slice input' consumed len in
        (true, Some (input'', v :: accu'))
    | None -> (false, None)

inline_for_extraction
let parse_list_tailrec
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: Tot (res: option (list t) { res == parse_list_tailrec' p32 input [] } )
= let accu =
    CL.total_while
      (parse_list_tailrec_measure #t)
      (parse_list_tailrec_inv p32 input)
      (fun x -> parse_list_tailrec_body p32 input x)
      (Some (input, []))
  in
  match accu with
  | None -> None
  | Some (_, accu') -> Some (list_rev accu')

inline_for_extraction
let parse32_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_list p))
= fun (input: bytes32) -> ((
    parse_list_tailrec'_correct p32 input;
    parser_kind_prop_equiv parse_list_kind (parse_list p);
    match parse_list_tailrec p32 input with
    | None -> None
    | Some res ->
      Some (res, B32.len input)
  ) <: (res: option (list t * U32.t) { parser32_correct (parse_list p) input res } ))

let rec partial_serialize32_list'
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (input: list t)
: Ghost bytes32
  (requires (
    serialize_list_precond k /\ (
    Seq.length (serialize (serialize_list p s) input) < 4294967296
  )))
  (ensures (fun (res: bytes32) ->
    serialize_list_precond k /\
    serializer32_correct (serialize_list p s) input res
  ))
  (decreases input)
= match input with
  | [] ->
    serialize_list_nil p s;
    let res = B32.empty_bytes in
    assert (Seq.equal (B32.reveal res) (Seq.empty));
    res
  | a :: q ->
    serialize_list_cons p s a q;
    let sa = s32 a in
    let sq = partial_serialize32_list' p s s32 q in
    let res = B32.append sa sq in
    res

let rec partial_serialize32_list_tailrec'
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (accu: bytes32)
  (input: list t)
: Ghost bytes32
  (requires (
    serialize_list_precond k /\ (
    B32.length accu + Seq.length (serialize (serialize_list p s) input) < 4294967296
  )))
  (ensures (fun (res: bytes32) ->
    serialize_list_precond k /\
    Seq.length (serialize (serialize_list p s) input) < 4294967296 /\
    B32.reveal res == Seq.append (B32.reveal accu) (B32.reveal (partial_serialize32_list' p s s32 input))
  ))
  (decreases input)
= match input with
  | [] ->
    serialize_list_nil p s;
    Seq.append_empty_r (B32.reveal accu);
    accu
  | a :: q ->
    serialize_list_cons p s a q;
    let sa = s32 a in
    let accu' = B32.append accu sa in
    Seq.append_assoc (B32.reveal accu) (B32.reveal sa) (B32.reveal (partial_serialize32_list' p s s32 q));
    partial_serialize32_list_tailrec' p s s32 accu' q

let partial_serialize32_list'_inv
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (input: list t)
  (continue: bool)
  (x: bytes32 * list t)
: GTot Type0
= serialize_list_precond k /\
  Seq.length (serialize (serialize_list p s) input) < 4294967296 /\ (
    let (accu, input') = x in
    B32.length accu + Seq.length (serialize (serialize_list p s) input') < 4294967296 /\
    serializer32_correct
      (serialize_list p s)
      input
      (partial_serialize32_list_tailrec' p s s32 accu input') /\
    (continue == false ==> L.length input' == 0)
  )

let partial_serialize32_list'_measure
  (#t: Type)
  (x: bytes32 * list t)
: GTot nat
= L.length (snd x)

inline_for_extraction
let partial_serialize32_list'_body
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (input: list t)
: (x: (bytes32 * list t)) ->
  Pure (bool * (bytes32 * list t))
  (requires (partial_serialize32_list'_inv p s s32 input true x))
  (ensures (fun (continue, y) ->
    partial_serialize32_list'_inv p s s32 input continue y /\
    (continue == true ==> partial_serialize32_list'_measure y < partial_serialize32_list'_measure x)
  ))
= fun (x: bytes32 * list t) ->
  let (accu, input') = x in
  match input' with
  | [] -> (false, x)
  | a :: q ->
    [@inline_let]
    let _ = serialize_list_cons p s a q in
    let sa = s32 a in
    let accu' = B32.append accu sa in
    (true, (accu', q))

let partial_serialize32_list'_init
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (input: list t)
: Lemma
  (requires (
    serialize_list_precond k /\
    Seq.length (serialize (serialize_list p s) input) < 4294967296
  ))
  (ensures (
    partial_serialize32_list'_inv p s s32 input true (B32.empty_bytes, input)
  ))
= assert (Seq.equal (B32.reveal B32.empty_bytes) Seq.empty);
  Seq.append_empty_l (B32.reveal (partial_serialize32_list' p s s32 input));
  assert (B32.reveal (partial_serialize32_list' p s s32 input) == B32.reveal (partial_serialize32_list_tailrec' p s s32 B32.empty_bytes input));
  assert (serializer32_correct (serialize_list p s) input (partial_serialize32_list_tailrec' p s s32 B32.empty_bytes input))

inline_for_extraction
let partial_serialize32_list
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (partial_serializer32 (serialize_list p s))
= fun (input: list t { Seq.length (serialize (serialize_list p s) input) < 4294967296 } ) -> ((
    let (res, _) =
      partial_serialize32_list'_init p s s32 input;
      CL.total_while
        partial_serialize32_list'_measure
        (partial_serialize32_list'_inv p s s32 input)
        (fun x -> partial_serialize32_list'_body p s s32 input x)
        (B32.empty_bytes, input)
    in
    res
  ) <: (res: bytes32 { serializer32_correct (serialize_list p s) input res }))

let size32_list_inv
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
  (input: list t)
  (continue: bool)
  (accu: (U32.t * list t))
: GTot Type0
= let (len, rem) = accu in
  let sz = Seq.length (serialize (serialize_list p s) input) in
  if continue
  then
    U32.v len < U32.v u32_max /\
    sz == U32.v len + Seq.length (serialize (serialize_list p s) rem)
  else
    size32_postcond (serialize_list p s) input len

let size32_list_measure
  (#t: Type)
  (accu: (U32.t * list t))
: GTot nat
= let (_, rem) = accu in
  L.length rem

inline_for_extraction
let size32_list_body
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
  (input: list t)
: (x: (U32.t * list t)) ->
  Pure (bool * (U32.t * list t))
  (requires (size32_list_inv s32 u input true x))
  (ensures (fun (continue, y) ->
    size32_list_inv s32 u input continue y /\
    (continue == true ==> size32_list_measure y < size32_list_measure x)
  ))
= fun accu ->
  let (len, rem) = accu in
  match rem with
    | [] ->
      [@inline_let]
      let _ = serialize_list_nil p s in
      (false, accu)
    | a :: q ->
      [@inline_let]
      let _ = serialize_list_cons p s a q in
      let sza = s32 a in
      let len' = add_overflow len sza in
      if len' = u32_max
      then (false, (u32_max, []))
      else (true, (len', q))

inline_for_extraction
let size32_list
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (size32 (serialize_list p s))
= fun input ->
  [@inline_let]
  let (len, _) =
    CL.total_while
      size32_list_measure
      (size32_list_inv s32 u input)
      (fun x -> size32_list_body s32 u input x)
      (0ul, input)
  in
  (len <: (len : U32.t { size32_postcond (serialize_list p s) input len } ))
