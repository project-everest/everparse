module CDDL.Spec.AST.Elab.Disjoint.Type
include CDDL.Spec.AST.Elab.Base

module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 256 --query_stats --split_queries always --fuel 4 --ifuel 8"

#restart-solver
[@@"opaque_to_smt"]
let typ_disjoint
  (typ_disjoint: typ_disjoint_t)
  (array_group_disjoint: array_group_disjoint_t)
: typ_disjoint_t
= fun e t1 t2 ->
  match t1, t2 with
  | TNamed _ t1, t2
  | t1, TNamed _ t2 -> typ_disjoint e t1 t2
  | TElem EAlwaysFalse, _
  | _, TElem EAlwaysFalse -> RSuccess ()
  | TElem EAny, _
  | _, TElem EAny -> RFailure "typ_disjoint: EAny"
  | _ ->
    if t1 = t2
    then RFailure "typ_disjoint: irrefl"
    else begin
  match t1, t2 with
  | t2, TDef i
  | TDef i, t2 ->
    let t1' = e.e_env i in
    typ_disjoint e t1' t2
  | TChoice t1l t1r, t2
  | t2, TChoice t1l t1r ->
    let aux = match t2 with
    | TRange _ _ _ ->
      begin match extract_range_value e.e_sem_env t2 with
      | None -> RSuccess ()
      | Some (ilo, ihi) ->
        let lo = eval_int_value ilo in
        let hi = eval_int_value ihi in
        if lo > hi
        then RSuccess ()
        else if lo < 0 && hi >= 0
        then
          let res1 = typ_disjoint e (TRange (TElem (ELiteral (LInt lo))) true (TElem (ELiteral (LInt (-1))))) (TChoice t1l t1r) in
          if not (RSuccess? res1)
          then res1
          else typ_disjoint e (TRange (TElem (ELiteral (LInt 0))) true (TElem (ELiteral (LInt hi)))) (TChoice t1l t1r)
        else RFailure ""
      end
    | _ -> RFailure ""
    in
    if not (RFailure? aux)
    then aux
    else let rl = typ_disjoint e t1l t2 in
    if not (RSuccess? rl)
    then rl
    else typ_disjoint e  t1r t2
  | TTagged tag1 t1', TTagged tag2 t2' ->
    if tag1 = tag2 || None? tag1 || None? tag2
    then typ_disjoint e  t1' t2'
    else RSuccess ()
  | TTagged _ _, _
  | _, TTagged _ _ -> RSuccess ()
  | TSize base range, t
  | t, TSize base range ->
    let res = typ_disjoint e  base t in
    if not (RFailure? res)
    then res
    else begin match typ_disjoint e  base (TChoice (TElem EByteString) (TElem ETextString)) with
    | ROutOfFuel -> ROutOfFuel
    | RSuccess _ ->
      begin match extract_int_value e.e_sem_env range with
      | None -> RSuccess ()
      | Some v ->
        let j = eval_int_value v in
        if j < 0
        then RSuccess ()
        else let vv = (let open FStar.Mul in 8 * j) in
        if vv < 64
        then begin
          FStar.Math.Lemmas.pow2_lt_compat 64 vv;
          typ_disjoint e  t (TRange (TElem (ELiteral (LInt 0))) true (TElem (ELiteral (LInt (pow2 vv - 1)))))
        end
        else begin
          FStar.Math.Lemmas.pow2_le_compat vv 64;
          typ_disjoint e  t (TElem EUInt)
        end
      end
    | RFailure _ ->
      begin match extract_range_value e.e_sem_env range with
      | None -> RSuccess ()
      | Some (rlo, rhi) ->
        let res1 = typ_disjoint e  base (TElem EUInt) in
        if not (RSuccess? res1)
        then res1
        else let lo = eval_int_value rlo in
        let hi = eval_int_value rhi in
        if lo > hi
        then RSuccess ()
        else begin match t with
        | TElem (ELiteral (LTextString s)) ->
          let len = String.length s in
          if len > hi || len < lo
          then RSuccess ()
          else RFailure "typ_disjoint: TSize vs. LTextString"
        | TDetCbor _ _ ->
          if hi <= 0
          then RSuccess () (* needed by COSE empty_or_serialized_map *)
          else RFailure "typ_disjoint: TSize vs. TDetCbor"
        | TSize base' range' ->
          begin match extract_range_value e.e_sem_env range' with
          | None -> RSuccess ()
          | Some (rlo', rhi') ->
            let lo' = eval_int_value rlo' in
            let hi' = eval_int_value rhi' in
            if lo' > hi'
            then RSuccess ()
            else if hi < lo' || hi' < lo
            then RSuccess ()
            else RFailure "typ_disjoint: TSize vs. TSize string"
          end
        | _ -> RFailure "typ_disjoint: TSize"
        end
      end
    end
  | TDetCbor _ dest, t
  | t, TDetCbor _ dest ->
    let res = typ_disjoint e  (TElem EByteString) t in
    if not (RFailure? res)
    then res
    else begin match t with
    | TDetCbor _ dest' -> typ_disjoint e  dest dest'
    | _ -> RFailure "typ_disjoint: TDetCbor"
    end
  | TRange _tlo _included _thi, t
  | t, TRange _tlo _included _thi ->
    begin match extract_range_value e.e_sem_env (TRange _tlo _included _thi) with
    | None -> RSuccess ()
    | Some (lo, hi) ->
      let lo = eval_int_value lo in
      let hi = eval_int_value hi in
      if lo > hi
      then RSuccess ()
      else begin match t with
      | TElem (ELiteral (LInt x)) ->
        if x < lo || x > hi
        then RSuccess ()
        else RFailure "typ_disjoint: TRange vs. TElem ELiteral LInt"
      | TRange _tlo' _included' _thi' ->
        begin match extract_range_value e.e_sem_env (TRange _tlo' _included' _thi') with
        | None -> RSuccess ()
        | Some (lo', hi') ->
          let lo' = eval_int_value lo' in
          let hi' = eval_int_value hi' in
          if lo' > hi' || hi < lo' || hi' < lo
          then RSuccess ()
          else RFailure "typ_disjoint: TRange vs. TRange"
        end
      | _ ->
        if lo >= 0
        then typ_disjoint e  t (TElem EUInt)
        else if hi < 0
        then typ_disjoint e  t (TElem ENInt)
        else typ_disjoint e  t (TChoice (TElem EUInt) (TElem ENInt))
      end
    end
  | TElem EBool, TElem (ELiteral (LSimple v))
  | TElem (ELiteral (LSimple v)), TElem EBool ->
    if U8.uint_to_t v = simple_value_true
    then RFailure "typ_disjoint: Bool vs. simple_value_true"
    else if U8.uint_to_t v = simple_value_false
    then RFailure "typ_disjoint: Bool vs. simple_value_false"
    else RSuccess ()
  | TElem ESimple, TElem (ELiteral (LSimple _))
  | TElem (ELiteral (LSimple _)), TElem ESimple ->
    RFailure "typ_disjoint: Simple vs. simple_value"
  | TElem ESimple, TElem EBool
  | TElem EBool, TElem ESimple
    -> RFailure "typ_disjoint: Bool vs. Simple"
  | TElem (ELiteral (LInt v)), TElem EUInt
  | TElem EUInt, TElem (ELiteral (LInt v)) ->
    if v >= 0
    then RFailure "typ_disjoint: uint64"
    else RSuccess ()
  | TElem (ELiteral (LInt v)), TElem ENInt
  | TElem ENInt, TElem (ELiteral (LInt v)) ->
    if v < 0
    then RFailure "typ_disjoint: neg_int64"
    else RSuccess ()
  | TElem (ELiteral (LTextString _)), TElem EByteString
  | TElem EByteString, TElem (ELiteral (LTextString _)) ->
    RSuccess ()
  | TElem (ELiteral (LTextString _)), TElem ETextString
  | TElem ETextString, TElem (ELiteral (LTextString _)) ->
    RFailure "typ_disjoint: text string"
  | TElem (ELiteral (LTextString s1)), TElem (ELiteral (LTextString s2)) ->
    byte_seq_of_ascii_string_diff s1 s2;
    RSuccess ()
  | TElem _, _
  | _, TElem _ -> RSuccess ()
  | TMap _, TMap _ -> RFailure "typ_disjoint: map: not supported"
  | TMap _, _
  | _, TMap _ -> RSuccess ()
  | TArray a1, TArray a2 ->
    Spec.array_close_array_group (array_group_sem e.e_sem_env a1);
    Spec.array_close_array_group (array_group_sem e.e_sem_env a2);
    array_group_disjoint e  true true a1 a2
  | TArray _, _
  | _, TArray _ -> RSuccess ()
  end
