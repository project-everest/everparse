module LowParse.SteelST.Validate
include LowParse.SteelST.Parse
open Steel.ST.Util

(* A validator that returns the number of bytes consumed. *)

module AP = LowParse.SteelST.ArrayPtr
module U32 = FStar.UInt32
module SZ = LowParse.Steel.StdInt
module R = Steel.ST.Reference

let validator_prop
  (#base: Type)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: AP.v base byte)
  (v_err: U32.t)
  (res: SZ.size_t)
: Tot prop
= 
  SZ.size_v res <= AP.length (AP.array_of b) /\
  begin match parse p (AP.contents_of b), (U32.v v_err = 0) with
  | None, false -> True
  | Some (_, consumed), true ->
    SZ.size_v res == consumed
  | _ -> False
  end

let validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (#base: Type) ->
  (#b: AP.v base byte) ->
  (a: byte_array base) ->
  (len: SZ.size_t) ->
  (err: R.ref U32.t) ->
  ST SZ.size_t
    (AP.arrayptr a b `star` R.pts_to err full_perm 0ul)
    (fun res -> AP.arrayptr a b `star` exists_ (fun v_err ->
      R.pts_to err full_perm v_err `star`
      pure (validator_prop p b v_err res)
    ))
    (SZ.size_v len == AP.length (AP.array_of b))
    (fun _ -> True)

// For debugging purposes only: "validator" without precondition
let debug_validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (#base: Type) ->
  (#b: AP.v base byte) ->
  (a: byte_array base) ->
  (len: SZ.size_t) ->
  (err: R.ref U32.t) ->
  ST SZ.size_t
    (AP.arrayptr a b `star` R.pts_to err full_perm 0ul)
    (fun res -> AP.arrayptr a b `star` exists_ (fun v_err ->
      R.pts_to err full_perm v_err
    ))
    (SZ.size_v len == AP.length (AP.array_of b))
    (fun _ -> True)

let validator_error_not_enough_data : U32.t = 1ul

let validate_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (validator p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.size_v sz /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal
    ))
    (ensures (fun _ -> True))
= fun a len err ->
    parser_kind_prop_equiv k p;
    if SZ.size_le sz len
    then begin
      noop ();
      return sz
    end
    else begin
      R.write err validator_error_not_enough_data;
      return SZ.zero_size
    end
