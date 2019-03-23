module LowParseExample2
open FStar.HyperStack.ST

module B32 = FStar.Bytes

type t = {
  b: (b: B32.bytes { B32.length b <= 65535 } );
}

val t'_l_serializable (x: list t) : GTot Type0

val check_t'_l_serializable (x: list t) : Tot (b: bool { b == true <==> t'_l_serializable x } )

type t' = {
  l: (l: list t { t'_l_serializable l });
}

let make_t' (x: list t) : Tot (option t') =
  if check_t'_l_serializable x
  then Some ({ l = x })
  else None

module U32 = FStar.UInt32

val parse_t' : B32.bytes -> Tot (option (t' * U32.t))

val serialize_t' : t' -> Tot B32.bytes

val serialize_then_parse_t'
  (x: t')
: Lemma
  (
    let b = serialize_t' x in
    parse_t' b == Some (x, B32.len b)
  )

val parse_then_serialize_t'
  (x: B32.bytes)
  (y: t')
  (consumed: U32.t)
: Lemma
  (requires (parse_t' x == Some (y, consumed)))
  (ensures (
    U32.v consumed <= B32.length x /\
    serialize_t' y == B32.slice x 0ul consumed
  ))

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
