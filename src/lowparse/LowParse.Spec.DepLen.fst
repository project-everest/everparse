module LowParse.Spec.DepLen

(* LowParse specification module for parsing structures with dependent length

   Example:

   struct {
     uint len;
     uint foo;
     uint buf[len];
   };

*)

include LowParse.Spec.Combinators
include LowParse.Spec.AllIntegers
include LowParse.Spec.VLGen

module U32 = FStar.UInt32
module Seq = FStar.Seq


(* arguments

     @min     :
     @max     : integer bounds
     @ht      : header type
     @hk      : header parser metadata
     @hp      : header parser
     @h       : header data
     @dlf     : dependent length function
     @pt      : payload type
     @pk      : payload parser metadata
     @pp      : payload parser
     @ps      : payload serializer
     @x       : data

*)

(* data type of the dependent length parser, which is a pair of the header and the payload *)

let parse_deplen_data_t 
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 } )
  (#ht : Type)
  (#pt : Type)
  (dlf : ht -> Tot (bounded_int32 min max) )
  (#pk : parser_kind)
  (#pp : parser pk pt)
  (ps : serializer pp)
= x:(ht & pt) {U32.v (dlf (fst x)) == Seq.length (serialize ps (snd x) ) }


(* the tag for a piece of dependent length data is just its header *)

let calc_tag_of_deplen_data
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 } )
  (#ht : Type)
  (#pt : Type)
  (dlf : ht -> Tot (bounded_int32 min max) )
  (#pk : parser_kind)
  (#pp : parser pk pt)
  (ps : serializer pp)
  (x : parse_deplen_data_t min max dlf ps)
: GTot ht
= fst x


(* synth put the header and the payload together to get the data *)

let synth_deplen_data
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 } )
  (#ht : Type)
  (#pt : Type)
  (dlf : ht -> Tot (bounded_int32 min max) )
  (#pk : parser_kind)
  (#pp : parser pk pt)
  (ps : serializer pp)
  (h : ht)
  (x : parse_fldata_strong_t ps (U32.v (dlf h)))
: Tot (refine_with_tag (calc_tag_of_deplen_data min max dlf ps) h) 
= (h, x)


(* metadata of the payload, reuse bounded_vlgen_payload *)

let parse_deplen_payload_kind = parse_bounded_vlgen_payload_kind


(* parser spec for the dependent length payload which attaches the header to generate the data *)

let parse_deplen_payload
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 } )
  (#ht : Type)
  (#pt : Type)
  (dlf : ht -> Tot (bounded_int32 min max) )
  (#pk : parser_kind)
  (#pp : parser pk pt)
  (ps : serializer pp)
  (h : ht)
: Tot (parser (parse_deplen_payload_kind min max pk) (refine_with_tag (calc_tag_of_deplen_data min max dlf ps) h)) 
= let sz = (U32.v (dlf h)) in
  let bounds_off =
    pk.parser_kind_low > sz || (
    match pk.parser_kind_high with
    | None -> false
    | Some pkmax -> pkmax < sz
  )
  in
  if bounds_off
  then fail_parser (parse_deplen_payload_kind min max pk) (refine_with_tag (calc_tag_of_deplen_data min max dlf ps) h)
  else
    weaken (parse_deplen_payload_kind min max pk)
      (parse_fldata_strong ps sz
      `parse_synth`
      synth_deplen_data min max dlf ps h)


(* unfold is a more human readable version and do double-check of the definition

   This lemma says using the parser defined above is equivalent to using a fixed-length
   parser with the calculated size and then attach the header
*) 

let parse_deplen_payload_unfold
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 } )
  (#ht : Type)
  (#pt : Type)
  (dlf : ht -> Tot (bounded_int32 min max) )
  (#pk : parser_kind)
  (#pp : parser pk pt)
  (ps : serializer pp)
  (h : ht)
  (input: bytes)
: Lemma
  (parse (parse_deplen_payload min max dlf ps h) input == (match (parse (parse_fldata_strong ps (U32.v (dlf h))) input) with
    | None -> None
    | Some (x, consumed) -> Some (synth_deplen_data min max dlf ps h x, consumed)))
 = let sz = (U32.v (dlf h)) in
   let bounds_off =
     pk.parser_kind_low > sz || (
     match pk.parser_kind_high with
     | None -> false
     | Some pkmax -> pkmax < sz
   )
   in
   if bounds_off
   then ()
   else
     parse_synth_eq
       (parse_fldata_strong ps sz)
       (synth_deplen_data min max dlf ps h)
       input

(* metadata for dependent length parser

   @min : 
   @max : integer bounds
   @hk  : header metadata
   @pk  : payload metadata
*)

let parse_deplen_kind
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 } )
  (hk : parser_kind)
  (pk : parser_kind)
= and_then_kind hk (parse_deplen_payload_kind min max pk)


(* parse spec for dependent length structures *)

let parse_deplen
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#hk: parser_kind)
  (#ht: Type)
  (hp: parser hk ht)
  (dlf: ht -> Tot (bounded_int32 min max))
  (#pk: parser_kind)
  (#pt: Type)
  (#pp: parser pk pt)
  (ps: serializer pp)
: Tot (parser (parse_deplen_kind min max hk pk) (parse_deplen_data_t min max dlf ps))
= parse_tagged_union
    hp
    (calc_tag_of_deplen_data min max dlf ps)
    (parse_deplen_payload min max dlf ps)

(* This lemma says using the parser above is equivalent to using the header parser and then
   the deplen_payload parser
*)

let parse_deplen_unfold
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 } )
  (#hk: parser_kind)
  (#ht: Type)
  (hp: parser hk ht)
  (dlf: ht -> Tot (bounded_int32 min max))
  (#pk: parser_kind)
  (#pt: Type)
  (#pp: parser pk pt)
  (ps: serializer pp)
  (input : bytes)
: Lemma
  (let res = parse (parse_deplen min max hp dlf ps) input in
    match parse hp input with
    | None -> res == None
    | Some (h, consumed) ->
      begin
        let input' = Seq.slice input consumed (Seq.length input) in
        match parse (parse_deplen_payload min max dlf ps h) input' with
        | None -> res == None
        | Some(x, consumed') ->
          if consumed' = U32.v (dlf h) then
            let (h', t) = x in
              Seq.length (serialize ps t) = (U32.v (dlf h)) /\ res == Some (x, consumed + (U32.v (dlf h)))
          else
            res == None
      end
  )
= parse_tagged_union_eq
    hp
    (calc_tag_of_deplen_data min max dlf ps)
    (parse_deplen_payload min max dlf ps)
    input;
  match parse hp input with
  | None -> ()
  | Some (h, consumed) ->
    let input' = Seq.slice input consumed (Seq.length input) in
    parse_deplen_payload_unfold min max dlf ps h input';
    let sz = (U32.v (dlf h)) in
    if Seq.length input < consumed + sz then
      ()
    else
      Seq.slice_slice input consumed (Seq.length input) 0 sz
    
(* A unit test for the parser specification defined above *)

(* 1. the concrete data type *)

let unit_test_header_type = ((bounded_int32 0 100) & (bounded_int32 0 100))

module B32 = FStar.Bytes

let unit_test_payload_type = B32.bytes

let unit_test_data_type = unit_test_header_type & unit_test_payload_type

(* 2. parser for header *)

let unit_test_header_parser = ?

(* 3. dependent length function *)

let unit_test_dependent_length_f
  (h : unit_test_header_type)
: Tot (bounded_int32 0 100)
= fst h

(* 4. serializer for payload *)

let unit_test_payload_serializer = serialize_all_bytes

