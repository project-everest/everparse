module LowParse.Spec.Bytes
include LowParse.Spec.VLGen

module B32 = FStar.Bytes
module Seq = FStar.Seq
module U32 = FStar.UInt32

#set-options "--z3rlimit 128 --max_fuel 64 --max_ifuel 64"

let lt_pow2_32
  (x: nat)
: Lemma
  (x < 4294967296 <==> x < pow2 32)
= ()

#reset-options

let parse_flbytes_gen
  (sz: nat { sz < 4294967296 } )
  (s: bytes { Seq.length s == sz } )
: GTot (B32.lbytes sz)
= lt_pow2_32 sz;
  B32.hide s

let parse_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (parser (total_constant_size_parser_kind sz) (B32.lbytes sz))
= make_total_constant_size_parser sz (B32.lbytes sz) (parse_flbytes_gen sz)

let serialize_flbytes'
  (sz: nat { sz < 4294967296 } )
: Tot (bare_serializer (B32.lbytes sz))
= fun (x: B32.lbytes sz) -> (
    lt_pow2_32 sz;
    B32.reveal x
  )

let serialize_flbytes_correct
  (sz: nat { sz < 4294967296 } )
: Lemma
  (serializer_correct (parse_flbytes sz) (serialize_flbytes' sz))
= let prf
    (input: B32.lbytes sz)
  : Lemma
    (
      let ser = serialize_flbytes' sz input in
      Seq.length ser == sz /\
      parse (parse_flbytes sz) ser == Some (input, sz)
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (serializer (parse_flbytes sz))
= serialize_flbytes_correct sz;
  serialize_flbytes' sz

(* VLBytes *)

(* For the payload: since the input buffer is truncated at the time of
reading the length header, "parsing" the payload will always succeed,
by just returning it unchanged (unless the length of the input
is greater than 2^32) *)

inline_for_extraction
let parse_all_bytes_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = None;
    parser_kind_subkind = Some ParserConsumesAll;
  }

let parse_all_bytes'
  (input: bytes)
: GTot (option (B32.bytes * consumed_length input))
= let len = Seq.length input in
  if len >= 4294967296
  then None
  else begin
    lt_pow2_32 len;
    Some (B32.hide input, len)
  end

#set-options "--z3rlimit 16"

let parse_all_bytes_injective () : Lemma
  (injective parse_all_bytes')
= let prf
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond parse_all_bytes' b1 b2))
    (ensures (injective_postcond parse_all_bytes' b1 b2))
  = assert (Seq.length b1 < 4294967296);
    assert (Seq.length b2 < 4294967296);
    lt_pow2_32 (Seq.length b1);
    lt_pow2_32 (Seq.length b2);
    B32.reveal_hide b1;
    B32.reveal_hide b2
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))

#reset-options

let parse_all_bytes_correct () : Lemma
  (parser_kind_prop parse_all_bytes_kind parse_all_bytes')
= parser_kind_prop_equiv parse_all_bytes_kind parse_all_bytes';
  parse_all_bytes_injective ()

let parse_all_bytes : parser parse_all_bytes_kind B32.bytes =
  parse_all_bytes_correct ();
  parse_all_bytes'

let serialize_all_bytes'
  (input: B32.bytes)
: GTot bytes
= B32.reveal input

#set-options "--z3rlimit 32"

let serialize_all_bytes_correct () : Lemma (serializer_correct parse_all_bytes serialize_all_bytes') =
  let prf
    (input: B32.bytes)
  : Lemma
    (
      let ser = serialize_all_bytes' input in
      let len : consumed_length ser = Seq.length ser in
      parse parse_all_bytes ser == Some (input, len)
    )
  = assert (Seq.length (serialize_all_bytes' input) == B32.length input);
    lt_pow2_32 (B32.length input);
    B32.hide_reveal input
  in
  Classical.forall_intro prf

#reset-options

let serialize_all_bytes : serializer parse_all_bytes =
  serialize_all_bytes_correct ();
  serialize_all_bytes'

let parse_bounded_vlbytes_aux
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (parser (parse_bounded_vldata_strong_kind min max l parse_all_bytes_kind) (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes))
= parse_bounded_vldata_strong' min max l serialize_all_bytes

let parse_bounded_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: B32.bytes)
: GTot Type0
= let reslen = B32.length x in
  min <= reslen /\ reslen <= max

let parse_bounded_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type
= (x: B32.bytes { parse_bounded_vlbytes_pred min max x } )

let parse_bounded_vlbytes_kind
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
: Tot parser_kind
= parse_bounded_vldata_strong_kind min max (log256' max) parse_all_bytes_kind

inline_for_extraction
let synth_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (x: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
: Tot (parse_bounded_vlbytes_t min max)
= x

let parse_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (parser (parse_bounded_vldata_strong_kind min max l parse_all_bytes_kind) (parse_bounded_vlbytes_t min max))
= parse_synth (parse_bounded_vlbytes_aux min max l) (synth_bounded_vlbytes min max)

let parse_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) parse_all_bytes_kind) (parse_bounded_vlbytes_t min max))
= parse_bounded_vlbytes' min max (log256' max)

#set-options "--z3rlimit 16"

let parse_bounded_vlbytes_eq
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (input: bytes)
: Lemma
  (let res = parse (parse_bounded_vlbytes' min max l) input in
    match parse (parse_bounded_integer l) input with
    | None -> res == None
    | Some (header, consumed_header) ->
      if min <= U32.v header && U32.v header <= max && l + U32.v header <= Seq.length input
      then
        consumed_header == l /\
        res == Some (B32.hide (Seq.slice input l (l + U32.v header)), consumed_header + U32.v header)
      else
        res == None
  )
= let sz = l in
  parse_synth_eq (parse_bounded_vlbytes_aux min max l) (synth_bounded_vlbytes min max) input;
  parse_vldata_gen_eq sz (in_bounds min max) parse_all_bytes input;
  parser_kind_prop_equiv (parse_bounded_integer_kind sz) (parse_bounded_integer sz)

#reset-options

let serialize_bounded_vlbytes_aux
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (serializer (parse_bounded_vlbytes_aux min max l))
= serialize_bounded_vldata_strong' min max l serialize_all_bytes

inline_for_extraction
let synth_bounded_vlbytes_recip
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (x: parse_bounded_vlbytes_t min max)
: Tot (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
= x

let serialize_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (serializer (parse_bounded_vlbytes' min max l))
= serialize_synth
    (parse_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes_recip min max)
    ()

let serialize_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_vlbytes min max))
= serialize_bounded_vlbytes' min max (log256' max)

let length_serialize_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (x: parse_bounded_vlbytes_t min max)
: Lemma
  (Seq.length (serialize (serialize_bounded_vlbytes' min max l) x) == l + B32.length x)
= serialize_synth_eq
    (parse_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes_recip min max)
    ()
    x

let length_serialize_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_vlbytes_t min max)
: Lemma
  (Seq.length (serialize (serialize_bounded_vlbytes min max) x) == log256' max + B32.length x)
= length_serialize_bounded_vlbytes' min max (log256' max) x

let parse_bounded_vlgenbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#sk: parser_kind)
  (pk: parser sk (bounded_int32 min max))
: Tot (parser (parse_bounded_vlgen_kind sk min max parse_all_bytes_kind) (parse_bounded_vlbytes_t min max))
= parse_bounded_vlgen min max pk serialize_all_bytes `parse_synth` synth_bounded_vlbytes min max

let serialize_bounded_vlgenbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#kk: parser_kind)
  (#pk: parser kk (bounded_int32 min max))
  (sk: serializer pk { kk.parser_kind_subkind == Some ParserStrong })
: Tot (serializer (parse_bounded_vlgenbytes min max pk))
= serialize_synth
    (parse_bounded_vlgen min max pk serialize_all_bytes)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlgen min max sk serialize_all_bytes)
    (synth_bounded_vlbytes_recip min max)
    ()

let length_serialize_bounded_vlgenbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#kk: parser_kind)
  (#pk: parser kk (bounded_int32 min max))
  (sk: serializer pk { kk.parser_kind_subkind == Some ParserStrong })
  (x: parse_bounded_vlbytes_t min max)
: Lemma
  (
    Seq.length (serialize (serialize_bounded_vlgenbytes min max sk) x) ==
      Seq.length (serialize sk (B32.len x)) + B32.length x
  )
= serialize_synth_eq
    (parse_bounded_vlgen min max pk serialize_all_bytes)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlgen min max sk serialize_all_bytes)
    (synth_bounded_vlbytes_recip min max)
    ()
    x;
  serialize_bounded_vlgen_unfold
    min
    max
    sk
    serialize_all_bytes
    x

(*
let serialize_bounded_vlbytes_upd
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_vlbytes_t min max)
  (y: B32.bytes)
: Lemma
  (requires (B32.length y == B32.length x))
  (ensures (
    let sy = B32.reveal y in
    let y : parse_bounded_vlbytes_t min max = y in
    let sx = serialize (serialize_bounded_vlbytes min max) x in
    let lm = log256' max in
    lm + B32.length y == Seq.length sx /\
    serialize (serialize_bounded_vlbytes min max) y == seq_upd_seq sx lm sy
  ))
= serialize_bounded_vldata_strong_upd min max serialize_all_bytes x y

let serialize_bounded_vlbytes_upd_bw
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: parse_bounded_vlbytes_t min max)
  (y: B32.bytes)
: Lemma
  (requires (B32.length y == B32.length x))
  (ensures (
    let sy = B32.reveal y in
    let y : parse_bounded_vlbytes_t min max = y in
    let sx = serialize (serialize_bounded_vlbytes min max) x in
    let lm = log256' max in
    lm + B32.length y == Seq.length sx /\
    serialize (serialize_bounded_vlbytes min max) y == seq_upd_bw_seq sx 0 sy
  ))
= serialize_bounded_vldata_strong_upd_bw min max serialize_all_bytes x y
