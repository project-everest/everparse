module LowParseExampleDepLen

(* Unit test for LowParse.Spec.DepLen LowParse.Low.DepLen 

   Example:
   
   struct {
     uint len;
     uint foo;
     uint payload[len];
   }

   Contents:

   data type definition
   parser specification
   serializer specification
   extractable validator
*)

include LowParse.Spec.DepLen
include LowParse.Low.DepLen

include LowParse.Spec.Bytes
include LowParse.Low.Bytes

module B32 = FStar.Bytes
module U32 = FStar.UInt32

(* data type definition *)

let unit_test_header_type = ((bounded_int32 0 100) & (bounded_int32 0 100))

let unit_test_payload_type = B32.bytes

let unit_test_payload_serializer = serialize_all_bytes

noextract
let unit_test_min = 0

noextract
let unit_test_max = 4200000000

(* dependent length function *)

let unit_test_deplen_func
  (h : unit_test_header_type)
: Tot (bounded_int32 0 100)
= fst h

let unit_test_data_type = unit_test_header_type & unit_test_payload_type

let unit_test_data_type_strong = parse_deplen_data_t unit_test_min unit_test_max unit_test_deplen_func unit_test_payload_serializer

type unit_test_struct_type = 
  | MkUnit_test_struct_type : len: bounded_int32 0 100 -> foo: bounded_int32 0 100 -> payload: B32.bytes {U32.v (unit_test_deplen_func (len, foo)) == Seq.length (unit_test_payload_serializer payload)} -> unit_test_struct_type

let unit_test_synth_struct
  (x: unit_test_data_type_strong)
: Tot (unit_test_struct_type)
= MkUnit_test_struct_type (fst (fst x)) (snd (fst x)) (snd x)

(* parser specification *)

let unit_test_header_parser = nondep_then (parse_bounded_int32 0 100) (parse_bounded_int32 0 100)

let unit_test_data_parser = parse_deplen unit_test_min unit_test_max unit_test_header_parser unit_test_deplen_func unit_test_payload_serializer

let unit_test_struct_parser = unit_test_data_parser `parse_synth` unit_test_synth_struct

(* parser lemmas *)

let unit_test_struct_parser_unfold
  (input : bytes)
: Lemma
  (parse unit_test_struct_parser input == (
    let res = parse unit_test_data_parser input in
      match res with
      | None -> None
      | Some (x, consumed) -> Some (MkUnit_test_struct_type (fst (fst x)) (snd (fst x)) (snd x), consumed)
      )
  )
= parse_synth_eq
    unit_test_data_parser
    unit_test_synth_struct
    input

(* lemma1: the synthesized struct parser's output on all inputs should be the same as the result of calling the parser for each field *)

let unit_test_lemma1_aux1
  (input : bytes)
: Lemma
  (parse unit_test_header_parser input == (
   let res_len = parse (parse_bounded_int32 0 100) input in
     match res_len with
     | None -> None
     | Some (len, consumed) ->
       let input' = Seq.slice input consumed (Seq.length input) in
       let res_foo = parse (parse_bounded_int32 0 100) input' in
       match res_foo with
       | None -> None
       | Some (foo, consumed') -> Some ((len, foo), consumed + consumed'))
  )
= nondep_then_eq (parse_bounded_int32 0 100) (parse_bounded_int32 0 100) input

let unit_test_lemma1
  (input : bytes)
: Lemma 
  (parse unit_test_struct_parser input ==
   (let res_len = parse (parse_bounded_int32 0 100) input in
      match res_len with
      | None -> None
      | Some (len, consumed) ->
        let input' = Seq.slice input consumed (Seq.length input) in
        let res_foo = parse (parse_bounded_int32 0 100) input' in
        match res_foo with
        | None -> None
        | Some (foo, consumed') ->
          let sz = U32.v (unit_test_deplen_func (len, foo)) in
          if (sz + (consumed' + consumed) > Seq.length input) then
            None
          else
            let input'' = Seq.slice input (consumed + consumed') (consumed + consumed' + sz) in
            let res_payload = parse parse_all_bytes input'' in
            match res_payload with
            | None -> None
            | Some (payload, consumed'') -> 
              if consumed'' = sz && Seq.length (serialize serialize_all_bytes payload) = consumed'' then
                Some (MkUnit_test_struct_type len foo payload, consumed + consumed' + consumed'')
              else
                None)
  )
= unit_test_struct_parser_unfold input;
  parse_deplen_unfold2 unit_test_min unit_test_max unit_test_header_parser unit_test_deplen_func unit_test_payload_serializer input;
  unit_test_lemma1_aux1 input;
  let res_len = parse (parse_bounded_int32 0 100) input in
  match res_len with
  | None -> ()
  | Some (len, consumed) ->
    let input' = Seq.slice input consumed (Seq.length input) in
    let res_foo = parse (parse_bounded_int32 0 100) input' in
    match res_foo with
    | None -> ()
    | Some (foo, consumed') ->
      let sz = U32.v (unit_test_deplen_func (len, foo)) in
      if (sz + (consumed + consumed') > Seq.length input) then
        ()
      else
        let input'' = Seq.slice input (consumed + consumed') (Seq.length input) in
        parse_deplen_payload_unfold unit_test_min unit_test_max unit_test_deplen_func unit_test_payload_serializer (len, foo) input'';
        ()

(* serializer specification *)

let unit_test_header_serializer = serialize_nondep_then (serialize_bounded_int32 0 100) (serialize_bounded_int32 0 100)

let unit_test_data_serializer : serializer unit_test_data_parser = serialize_deplen unit_test_min unit_test_max unit_test_header_serializer unit_test_deplen_func unit_test_payload_serializer

let unit_test_synth_struct_recip
  (x: unit_test_struct_type)
: Tot (unit_test_data_type_strong)
= ((x.len, x.foo), x.payload) 

let unit_test_struct_serializer : serializer unit_test_struct_parser = 
  serialize_synth
    unit_test_data_parser
    unit_test_synth_struct
    unit_test_data_serializer
    unit_test_synth_struct_recip
    ()

(* Validator *)

inline_for_extraction
let unit_test_deplen_func_calc_type = deplen_func unit_test_min unit_test_max unit_test_header_parser unit_test_deplen_func

inline_for_extraction
let unit_test_deplen_func_calc : unit_test_deplen_func_calc_type
= fun #rrel #rel input pos ->
  let pos_len = accessor_fst (parse_bounded_int32 0 100) () (parse_bounded_int32 0 100) input pos in
  read_bounded_int32 0ul 100ul input pos_len

inline_for_extraction
let unit_test_header_validator : validator unit_test_header_parser
= validate_nondep_then (validate_bounded_int32 0ul 100ul) (validate_bounded_int32 0ul 100ul)

inline_for_extraction
let unit_test_payload_validator = validate_all_bytes ()

inline_for_extraction
let unit_test_data_validator : validator unit_test_data_parser
= validate_deplen 
    unit_test_min
    unit_test_max
    unit_test_header_validator
    unit_test_deplen_func
    unit_test_deplen_func_calc
    unit_test_payload_serializer
    unit_test_payload_validator

inline_for_extraction
let unit_test_struct_validator : validator unit_test_struct_parser
= validate_synth unit_test_data_validator unit_test_synth_struct ()

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)

let main _ _ = C.EXIT_SUCCESS
