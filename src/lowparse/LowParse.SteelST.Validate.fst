module LowParse.SteelST.Validate
include LowParse.SteelST.Parse
open Steel.ST.GenElim

(* A validator that returns the number of bytes consumed. *)

module AP = LowParse.SteelST.ArrayPtr
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module R = Steel.ST.Reference

let validator_prop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: AP.v byte)
  (v_err: U32.t)
  (res: SZ.t)
: Tot prop
= 
  SZ.v res <= AP.length (AP.array_of b) /\
  begin match parse p (AP.contents_of b), (U32.v v_err = 0) with
  | None, false -> True
  | Some (_, consumed), true ->
    SZ.v res == consumed
  | _ -> False
  end

inline_for_extraction
let validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (#b: AP.v byte) ->
  (a: byte_array) ->
  (len: SZ.t) ->
  (err: R.ref U32.t) ->
  ST SZ.t
    (AP.arrayptr a b `star` R.pts_to err full_perm 0ul)
    (fun res -> AP.arrayptr a b `star` exists_ (fun v_err ->
      R.pts_to err full_perm v_err `star`
      pure (validator_prop p b v_err res)
    ))
    (SZ.v len == AP.length (AP.array_of b))
    (fun _ -> True)

// For debugging purposes only: "validator" without precondition
inline_for_extraction
let debug_validator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= 
  (#b: AP.v byte) ->
  (a: byte_array) ->
  (len: SZ.t) ->
  (err: R.ref U32.t) ->
  ST SZ.t
    (AP.arrayptr a b `star` R.pts_to err full_perm 0ul)
    (fun res -> AP.arrayptr a b `star` exists_ (fun v_err ->
      R.pts_to err full_perm v_err
    ))
    (SZ.v len == AP.length (AP.array_of b))
    (fun _ -> True)

[@CMacro]
let validator_error_not_enough_data : U32.t = 1ul

inline_for_extraction
let validate_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.t)
: Pure (validator p)
    (requires (
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_low == SZ.v sz /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal
    ))
    (ensures (fun _ -> True))
= fun a len err ->
    parser_kind_prop_equiv k p;
    if SZ.lte sz len
    then begin
      noop ();
      return sz
    end
    else begin
      R.write err validator_error_not_enough_data;
      return 0sz
    end

inline_for_extraction
let ifthenelse_validate
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (cond: bool)
  (vtrue: (squash (cond == true) -> Tot (validator p)))
  (vfalse: (squash (cond == false) -> Tot (validator p)))
: Tot (validator p)
= fun a len err ->
  if cond
  then vtrue () a len err
  else vfalse () a len err
