module LowParse.Spec.SeqBytes
include LowParse.Spec.SeqBytes.Base
include LowParse.Spec.VLData

module Seq = FStar.Seq
module U32 = FStar.UInt32

(* VLBytes *)

(* For the payload: since the input buffer is truncated at the time of
reading the length header, "parsing" the payload will always succeed,
by just returning it unchanged (unless the length of the input
is greater than 2^32) *)

let parse_seq_all_bytes_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = None;
    parser_kind_subkind = Some ParserConsumesAll;
  }

let parse_seq_all_bytes'
  (input: bytes)
: GTot (option (bytes * consumed_length input))
= let len = Seq.length input in
    Some (input, len)

#set-options "--z3rlimit 16"

let parse_seq_all_bytes_injective () : Lemma
  (injective parse_seq_all_bytes')
= let prf
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond parse_seq_all_bytes' b1 b2))
    (ensures (injective_postcond parse_seq_all_bytes' b1 b2))
  = ()
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))

#reset-options

let parse_seq_all_bytes_correct () : Lemma
  (parser_kind_prop parse_seq_all_bytes_kind parse_seq_all_bytes')
= parser_kind_prop_equiv parse_seq_all_bytes_kind parse_seq_all_bytes';
  parse_seq_all_bytes_injective ()

let parse_seq_all_bytes : parser parse_seq_all_bytes_kind bytes =
  parse_seq_all_bytes_correct ();
  parse_seq_all_bytes'

let serialize_seq_all_bytes'
  (input: bytes)
: GTot bytes
= input

#set-options "--z3rlimit 32"

let serialize_seq_all_bytes_correct () : Lemma (serializer_correct parse_seq_all_bytes serialize_seq_all_bytes') =
  let prf
    (input: bytes)
  : Lemma
    (
      let ser = serialize_seq_all_bytes' input in
      let len : consumed_length ser = Seq.length ser in
      parse parse_seq_all_bytes ser == Some (input, len)
    )
  = assert (Seq.length (serialize_seq_all_bytes' input) == Seq.length input)
  in
  Classical.forall_intro prf

#reset-options

let serialize_seq_all_bytes : serializer parse_seq_all_bytes =
  serialize_seq_all_bytes_correct ();
  serialize_seq_all_bytes'

let parse_bounded_seq_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) parse_seq_all_bytes_kind) (parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes))
= parse_bounded_vldata_strong min max serialize_seq_all_bytes

let parse_bounded_seq_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: bytes)
: GTot Type0
= let reslen = Seq.length x in
  min <= reslen /\ reslen <= max

let parse_bounded_seq_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type
= (x: bytes { parse_bounded_seq_vlbytes_pred min max x } )

let synth_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (x: parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes)
: Tot (parse_bounded_seq_vlbytes_t min max)
= x

let parse_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) parse_seq_all_bytes_kind) (parse_bounded_seq_vlbytes_t min max))
= parse_synth (parse_bounded_seq_vlbytes' min max) (synth_bounded_seq_vlbytes min max)

let serialize_bounded_seq_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_seq_vlbytes' min max))
= serialize_bounded_vldata_strong min max serialize_seq_all_bytes

let serialize_bounded_seq_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_seq_vlbytes min max))
= serialize_synth
    (parse_bounded_seq_vlbytes' min max)
    (synth_bounded_seq_vlbytes min max)
    (serialize_bounded_seq_vlbytes' min max)
    (fun (x: parse_bounded_seq_vlbytes_t min max) ->
      (x <: parse_bounded_vldata_strong_t min max #_ #_ #parse_seq_all_bytes serialize_seq_all_bytes)
    )
    ()

(*

let serialize_bounded_seq_vlbytes_upd
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_seq_vlbytes_t min max)
  (y: bytes)
: Lemma
  (requires (Seq.length y == Seq.length x))
  (ensures (
    let sy = y in
    let y : parse_bounded_seq_vlbytes_t min max = y in
    let sx = serialize (serialize_bounded_seq_vlbytes min max) x in
    let lm = log256' max in
    lm + Seq.length y == Seq.length sx /\
    serialize (serialize_bounded_seq_vlbytes min max) y == seq_upd_seq sx lm sy
  ))
= serialize_bounded_vldata_strong_upd min max serialize_seq_all_bytes x y

let serialize_bounded_seq_vlbytes_upd_bw
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_seq_vlbytes_t min max)
  (y: bytes)
: Lemma
  (requires (Seq.length y == Seq.length x))
  (ensures (
    let sy = y in
    let y : parse_bounded_seq_vlbytes_t min max = y in
    let sx = serialize (serialize_bounded_seq_vlbytes min max) x in
    let lm = log256' max in
    lm + Seq.length y == Seq.length sx /\
    serialize (serialize_bounded_seq_vlbytes min max) y == seq_upd_bw_seq sx 0 sy
  ))
= serialize_bounded_vldata_strong_upd_bw min max serialize_seq_all_bytes x y
