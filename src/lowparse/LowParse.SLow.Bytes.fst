module LowParse.SLow.Bytes
include LowParse.Spec.Bytes
include LowParse.SLow.VLData
include LowParse.SLow.VLGen

module B32 = FStar.Bytes
module Seq = FStar.Seq
module U32 = FStar.UInt32

inline_for_extraction
let parse32_flbytes_gen
  (sz: nat { sz < 4294967296 } )
  (x: B32.lbytes sz)
: Tot (y: B32.lbytes sz { y == parse_flbytes_gen sz (B32.reveal x) } )
= B32.hide_reveal x;
  x

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_flbytes
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
: Tot (
     lt_pow2_32 sz;
     parser32 (parse_flbytes sz)
  )
= lt_pow2_32 sz;
  make_total_constant_size_parser32
    sz
    sz'
    #(B32.lbytes sz)
    (parse_flbytes_gen sz)
    ()
    (parse32_flbytes_gen sz)

inline_for_extraction
let serialize32_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (serializer32 (serialize_flbytes sz))
= fun (input: B32.lbytes sz) ->
    B32.hide_reveal input;
    (input <: (res: bytes32 { serializer32_correct (serialize_flbytes sz) input res } ))

inline_for_extraction
let parse32_all_bytes
  : parser32 parse_all_bytes
= fun (input: B32.bytes) ->
    let res = Some (input, B32.len input) in
    (res <: (res: option (bytes32 * U32.t) { parser32_correct parse_all_bytes input res } ))

inline_for_extraction
let serialize32_all_bytes
  : serializer32 serialize_all_bytes
= fun (input: B32.bytes) ->
  (input <: (res: bytes32 { serializer32_correct serialize_all_bytes input res } ))

inline_for_extraction
let parse32_bounded_vlbytes'
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max32: U32.t { U32.v max32 == max } )
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (parser32 (parse_bounded_vlbytes' min max l))
= parse32_synth
    _
    (synth_bounded_vlbytes min max)
    (fun (x: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes) -> (x <: parse_bounded_vlbytes_t min max))
    (parse32_bounded_vldata_strong' min min32 max max32 l serialize_all_bytes parse32_all_bytes)
    ()

inline_for_extraction
let parse32_bounded_vlbytes
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max32: U32.t { U32.v max32 == max } )
: Tot (parser32 (parse_bounded_vlbytes min max))
= parse32_bounded_vlbytes' min min32 max max32 (log256' max)

inline_for_extraction
let serialize32_bounded_vlbytes_aux
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (serializer32 (serialize_bounded_vlbytes_aux min max l))
= 
  serialize32_bounded_vldata_strong'
    min
    max
    l
    #_
    #_
    #parse_all_bytes
    #serialize_all_bytes
    serialize32_all_bytes

inline_for_extraction
let serialize32_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (serializer32 (serialize_bounded_vlbytes' min max l))
= serialize32_synth
    (parse_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlbytes_aux min max l)
    (serialize32_bounded_vlbytes_aux min max l)
    (fun (x: parse_bounded_vlbytes_t min max) ->
      (x <: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
    )
    (fun x -> x)
    ()

inline_for_extraction
let serialize32_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
: Tot (serializer32 (serialize_bounded_vlbytes min max))
= serialize32_bounded_vlbytes' min max (log256' max)

inline_for_extraction
let size32_all_bytes
: size32 serialize_all_bytes
= fun (input: B32.bytes) ->
  let res = B32.len input in
  (res <: (res: U32.t { size32_postcond serialize_all_bytes input res } ))

inline_for_extraction
let size32_bounded_vlbytes_aux
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (size32 (serialize_bounded_vlbytes_aux min max l))
= 
  size32_bounded_vldata_strong'
    min
    max
    l
    #_
    #_
    #parse_all_bytes
    #serialize_all_bytes
    size32_all_bytes
    (U32.uint_to_t l)

inline_for_extraction
let size32_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
  (l: nat { l >= log256' max /\ l <= 4 } )
: Tot (size32 (serialize_bounded_vlbytes' min max l))
= 
  size32_synth
    (parse_bounded_vlbytes_aux min max l)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlbytes_aux min max l)
    (size32_bounded_vlbytes_aux min max l)
    (fun (x: parse_bounded_vlbytes_t min max) ->
      (x <: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
    )
    (fun x -> x)
    ()

inline_for_extraction
let size32_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
: Tot (size32 (serialize_bounded_vlbytes min max))
= size32_bounded_vlbytes' min max (log256' max)

inline_for_extraction
let parse32_bounded_vlgenbytes
  (min: nat)
  (min32: U32.t { U32.v min32 == min })
  (max: nat{  min <= max /\ max > 0 })
  (max32: U32.t { U32.v max32 == max })
  (#kk: parser_kind)
  (#pk: parser kk (bounded_int32 min max))
  (pk32: parser32 pk)
: Tot (parser32 (parse_bounded_vlgenbytes min max pk))
= parse32_synth
    (parse_bounded_vlgen min max pk serialize_all_bytes)
    (fun x -> (x <: parse_bounded_vlbytes_t min max))
    (fun x -> (x <: parse_bounded_vlbytes_t min max))
    (parse32_bounded_vlgen min min32 max max32 pk32 serialize_all_bytes parse32_all_bytes)
    ()

inline_for_extraction
let serialize32_bounded_vlgenbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#kk: parser_kind)
  (#pk: parser kk (bounded_int32 min max))
  (#sk: serializer pk)
  (sk32: serializer32 sk {kk.parser_kind_subkind == Some ParserStrong /\ Some? kk.parser_kind_high /\ Some?.v kk.parser_kind_high + max < 4294967296 })
: Tot (serializer32 (serialize_bounded_vlgenbytes min max sk))
= serialize32_synth
    (parse_bounded_vlgen min max pk serialize_all_bytes)
    (fun x -> (x <: parse_bounded_vlbytes_t min max))
    (serialize_bounded_vlgen min max sk serialize_all_bytes)
    (serialize32_bounded_vlgen min max sk32 serialize32_all_bytes)
    (fun x -> x)
    (fun x -> x)
    ()

inline_for_extraction
let size32_bounded_vlgenbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#kk: parser_kind)
  (#pk: parser kk (bounded_int32 min max))
  (#sk: serializer pk)
  (sk32: size32 sk {kk.parser_kind_subkind == Some ParserStrong /\ Some? kk.parser_kind_high /\ Some?.v kk.parser_kind_high + max < 4294967296 })
: Tot (size32 (serialize_bounded_vlgenbytes min max sk))
= size32_synth
    (parse_bounded_vlgen min max pk serialize_all_bytes)
    (fun x -> (x <: parse_bounded_vlbytes_t min max))
    (serialize_bounded_vlgen min max sk serialize_all_bytes)
    (size32_bounded_vlgen min max sk32 size32_all_bytes)
    (fun x -> x)
    (fun x -> x)
    ()

