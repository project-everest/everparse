module CBOR.Spec.Raw.Format.UTF8
module U8 = FStar.UInt8

(* Unicode 4.0.0 Table 3-6: Well-Formed UTF-8 Byte Sequences *)

let byte_in_80_BF
  (x: nat)
: Tot bool
= 0x80 <= x && x <= 0xBF

type fetch_result (t: Type) =
| TooShort
| Error
| Success of t

let fetch_postcond
  (s: Seq.seq U8.t)
  (res: fetch_result pos)
: Tot prop
=
  match res with
    | Success res -> res <= Seq.length s
    | _ -> True
    
let fetch
  (s: Seq.seq U8.t)
: Pure (fetch_result pos)
    (requires Seq.length s > 0)
    (ensures fun res -> fetch_postcond s res)
= let check_last_byte_in_80_BF (n: pos) : Tot (fetch_result pos) =
    if Seq.length s < n
    then TooShort
    else if not (byte_in_80_BF (U8.v (Seq.index s (n - 1))))
    then Error
    else Success n
  in
  let is_length3 () : Tot (fetch_result pos) = check_last_byte_in_80_BF 3 in
  let is_length4 () : Tot (fetch_result pos) =
    match is_length3 () with
    | Success _ -> check_last_byte_in_80_BF 4
    | x -> x
  in
  let byte1 = U8.v (Seq.index s 0) in
  if byte1 <= 0x7F
  then Success 1
  else if (0x7F < byte1 && byte1 < 0xC2) || byte1 > 0xF4
  then Error
  else if Seq.length s = 1
  then TooShort
  else
    let byte2 = U8.v (Seq.index s 1) in
    if 0xC2 <= byte1 && byte1 <= 0xDF
    then
      if byte_in_80_BF byte2
      then Success 2
      else Error
    else if byte1 = 0xE0
    then
      if 0xA0 <= byte2 && byte2 <= 0xBF
      then is_length3 ()
      else Error
    else if byte1 = 0xED
    then
      if 0x80 <= byte2 && byte2 <= 0x9F
      then is_length3 ()
      else Error
    else if (0xE1 <= byte1 && byte1 <= 0xEF)
    then
      if byte_in_80_BF byte2
      then is_length3 ()
      else Error
    else if byte1 = 0xF0
    then
      if 0x90 <= byte2 && byte2 <= 0xBF
      then is_length4 ()
      else Error
    else if 0xF1 <= byte1 && byte1 <= 0xF3
    then
      if byte_in_80_BF byte2
      then is_length4 ()
      else Error
    else begin
      assert (byte1 == 0xF4);
      if 0x80 <= byte2 && byte2 <= 0x8F
      then is_length4 ()
      else Error
    end

let fetch'
  (s: Seq.seq U8.t)
: Pure (option pos)
    (requires Seq.length s > 0)
    (ensures fun res -> 
      (Some? res <==> Success? (fetch s)) /\
      begin match res, fetch s with
      | Some v1, Success v2 -> v1 == v2
      | _ -> True
      end
    )
= let byte1 = U8.v (Seq.index s 0) in
  if byte1 <= 0x7F
  then Some 1
  else if Seq.length s = 1
  then None
  else
    let byte2 = U8.v (Seq.index s 1) in
    if 0xC2 <= byte1 && byte1 <= 0xDF && byte_in_80_BF byte2
    then Some 2
    else if Seq.length s = 2
    then None
    else if not (byte_in_80_BF (U8.v (Seq.index s 2)))
    then None
    else if byte1 = 0xE0
    then
      if 0xA0 <= byte2 && byte2 <= 0xBF
      then Some 3
      else None
    else if byte1 = 0xED
    then
      if 0x80 <= byte2 && byte2 <= 0x9F
      then Some 3
      else None
    else if (0xE1 <= byte1 && byte1 <= 0xEF) && byte_in_80_BF byte2
    then Some 3
    else if Seq.length s = 3
    then None
    else if not (byte_in_80_BF (U8.v (Seq.index s 3)))
    then None
    else if byte1 = 0xF0 && 0x90 <= byte2 && byte2 <= 0xBF
    then Some 4
    else if 0xF1 <= byte1 && byte1 <= 0xF3 && byte_in_80_BF byte2
    then Some 4
    else if byte1 = 0xF4
    then
      if 0x80 <= byte2 && byte2 <= 0x8F
      then Some 4
      else None
    else None

let fetch_too_short_can_be_completed
  (s: Seq.seq U8.t)
: Lemma
  (requires (Seq.length s > 0 /\ TooShort? (fetch s)))
  (ensures exists s' . Success? (fetch (Seq.append s s')))
= assert (
    Success? (fetch (Seq.append s (Seq.cons 0x80uy (Seq.cons 0x80uy (Seq.cons 0x80uy Seq.empty))))) \/
    Success? (fetch (Seq.append s (Seq.cons 0x90uy (Seq.cons 0x80uy (Seq.cons 0x80uy Seq.empty))))) \/
    Success? (fetch (Seq.append s (Seq.cons 0xA0uy (Seq.cons 0x80uy (Seq.cons 0x80uy Seq.empty)))))
  )

let fetch_prefix
  (s s': Seq.seq U8.t)
: Lemma
  (requires Seq.length s > 0 /\ ~ (TooShort? (fetch s)))
  (ensures fetch (Seq.append s s') == fetch s)
= ()

let rec check
  (s: Seq.seq U8.t)
: Tot (fetch_result unit)
  (decreases (Seq.length s))
= if Seq.length s = 0
  then Success ()
  else match fetch s with
  | Error -> Error
  | TooShort -> TooShort
  | Success n -> check (Seq.slice s n (Seq.length s))

let rec check_prefix
  (s s': Seq.seq U8.t)
: Lemma
  (requires (~ (TooShort? (check s))))
  (ensures (check (Seq.append s s') == (if Error? (check s) then Error else check s')))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then assert (Seq.append s s' `Seq.equal` s')
  else match fetch s with
  | Error -> ()
  | Success n ->
    assert (Seq.slice (Seq.append s s') n (Seq.length (Seq.append s s')) `Seq.equal` Seq.append (Seq.slice s n (Seq.length s)) s');
    check_prefix (Seq.slice s n (Seq.length s)) s'

(* Tests (Unicode 4.0.0, Sections 3.9 sqq.) *)

let _ = assert (Error? (check (Seq.cons 0xC0uy (Seq.cons 0x80uy (Seq.cons 0x61uy (Seq.cons 0xF3uy Seq.empty))))))
let _ = assert (Success? (check (Seq.cons 0x4Duy Seq.empty)))
let _ = assert (Success? (check (Seq.cons 0xD0uy (Seq.cons 0xB0uy Seq.empty))))
let _ = assert (Success? (check (Seq.cons 0xE4uy (Seq.cons 0xBAuy (Seq.cons 0x8Cuy Seq.empty)))))
let _ = assert (Success? (check (Seq.cons 0xF0uy (Seq.cons 0x90uy (Seq.cons 0x8Cuy (Seq.cons 0x82uy Seq.empty))))))
#push-options "--fuel 5 --z3rlimit 64"
let _ = assert (Success? (check (Seq.cons 0x4Duy (Seq.cons 0xD0uy (Seq.cons 0xB0uy (Seq.cons 0xE4uy (Seq.cons 0xBAuy (Seq.cons 0x8Cuy (Seq.cons 0xF0uy (Seq.cons 0x90uy (Seq.cons 0x8Cuy (Seq.cons 0x82uy Seq.empty))))))))))))
#pop-options
let _ = assert (Error? (check (Seq.cons 0xC0uy (Seq.cons 0xAFuy Seq.empty))))
let _ = assert (Error? (check (Seq.cons 0xE0uy (Seq.cons 0x9Fuy (Seq.cons 0x80uy Seq.empty)))))
let _ = assert (Success? (check (Seq.cons 0xF4uy (Seq.cons 0x80uy (Seq.cons 0x83uy (Seq.cons 0x92uy Seq.empty))))))
let _ = assert (Success? (check (Seq.cons 0xEFuy (Seq.cons 0xBBuy (Seq.cons 0xBFuy Seq.empty)))))

let correct s = Success? (check s)

let rec ascii_is_utf8
  (s: Seq.seq U8.t)
: Lemma
  (requires (forall i . i < Seq.length s ==> U8.v (Seq.index s i) < 128))
  (ensures (correct s))
  (decreases (Seq.length s))
=
  if Seq.length s = 0
  then ()
  else ascii_is_utf8 (Seq.slice s 1 (Seq.length s))
