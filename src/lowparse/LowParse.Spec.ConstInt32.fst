module LowParse.Spec.ConstInt32

(* LowParse specification module for parsing 32 bits = 4 bytes unsigned constants

   Examples:

   uint32 foo = 5
   uint32_le foo = 7

*)

(* TODO: support big endian constants *)

include FStar.Endianness

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.Int32le

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module M = LowParse.Math

let constint32
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot Type
= (u: U32.t { U32.v u == v } )

inline_for_extraction
let parse_constint32le_kind
: parser_kind
= strong_parser_kind 4 4 None

let decode_constint32le
  (v: nat {0 <= v /\ v < 4294967296 } )
  (b: bytes { Seq.length b == 4 } )
: Tot (option (constint32 v))
= let v' = decode_int32le b in
    if U32.v v' = v then
      Some v'
    else
      None

let decode_constint32le_injective'
  (v: nat { 0 <= v /\ v < 4294967296 } )
  (b1: bytes { Seq.length b1 == 4 } )
  (b2: bytes { Seq.length b2 == 4 } )
: Lemma
  ((Some? (decode_constint32le v b1) \/ Some? (decode_constint32le v b2))
   /\ (decode_constint32le v b1 == decode_constint32le v b2) 
   ==> Seq.equal b1 b2)
= let res1 = decode_constint32le v b1 in
  let res2 = decode_constint32le v b2 in
  match res1 with
  | Some v1 ->
    assert ( U32.v v1 == v );
    (match res2 with
    | Some v2 ->
      assert ( U32.v v2 == v );
      assert ( v1 == v2 );
      decode_int32le_injective b1 b2
    | None -> ())
  | None -> ()

let decode_constint32le_injective
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Lemma
  (make_constant_size_parser_precond 4 (constint32 v) (decode_constint32le v))
= Classical.forall_intro_2 (decode_constint32le_injective' v)

let parse_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (parser parse_constint32le_kind (constint32 v))
= decode_constint32le_injective v;
  make_constant_size_parser 4 (constint32 v) (decode_constint32le v)

let parse_constint32le_unfold
  (v: nat { 0 <= v /\ v < 4294967296 } )
  (input: bytes)
: Lemma 
  (parse (parse_constint32le v) input ==
  (let res = parse parse_int32le input in
     match res with
     | Some (x, consumed) ->
       if U32.v x = v && consumed = 4 then
         Some (x, consumed)
       else
         None
     | None -> None))
= let res = parse parse_int32le input in
    match res with
    | Some (x, consumed) ->
      if U32.v x = v && consumed = 4 then
        ()
      else
        ()
    | None -> ()

let serialize_constint32le'
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (bare_serializer (constint32 v))
= fun (x: constint32 v) -> 
  let res = n_to_le 4 v in
  res

let serialize_constint32le_correct
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Lemma
  (serializer_correct (parse_constint32le v) (serialize_constint32le' v))
= let prf
    (x: constint32 v)
  : Lemma 
    (let res = n_to_le 4 v in
     U32.v x == v /\ Seq.length res == 4 /\ (parse (parse_constint32le v) res == Some (x, 4)))
  = ()
  in
  Classical.forall_intro prf

let serialize_constint32le
  (v: nat { 0 <= v /\ v < 4294967296 } )
: Tot (serializer (parse_constint32le v))
= serialize_constint32le_correct v;
  serialize_constint32le' v

