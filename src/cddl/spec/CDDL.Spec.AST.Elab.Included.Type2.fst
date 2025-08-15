module CDDL.Spec.AST.Elab.Included.Type2
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 256 --query_stats --split_queries always --fuel 4 --ifuel 8"

let typ_included2
  (typ_included: typ_included_t)
  (typ_included2: typ_included_t) 
  (array_group_included: array_group_included_t)
: typ_included_t
= fun e t1 t2 ->
  match t1, t2 with
  | TNamed _ t1, t2
  | t1, TNamed _ t2 -> typ_included2 e t1 t2
  | _, TElem EAny
  | TElem EAlwaysFalse, _ -> RSuccess ()
  | TDef i, t2 ->
    let t1' = e.e_env i in
    typ_included e  t1' t2
  | t2, TDef i ->
    let t1' = e.e_env i in
    typ_included e  t2 t1'
  | TElem EAny, _ -> RFailure "typ_included: TElem EAny"
  | t1, TElem EAlwaysFalse ->
    begin match extract_range_value e.e_sem_env t1 with
    | Some (lo, hi) -> if eval_int_value lo > eval_int_value hi then RSuccess () else RFailure "typ_included: TRange vs. TElem EAlwaysFalse"
    | None -> RFailure "typ_included: TElem EAlwaysFalse"
    end
  | TChoice t1l t1r, t2 ->
    let rl = typ_included e  t1l t2 in
    if not (RSuccess? rl)
    then rl
    else typ_included e  t1r t2
  | t3, TChoice t1l t1r ->
    let aux = match extract_range_value e.e_sem_env t3 with
    | None -> RFailure ""
    | Some (lo, hi) ->
      let lo = eval_int_value lo in
      let hi = eval_int_value hi in
      if lo < 0 && hi >= 0
      then
        let res1 = typ_included e  (TRange (TElem (ELiteral (LInt lo))) true (TElem (ELiteral (LInt (-1))))) t2 in
        if RSuccess? res1
        then typ_included e  (TRange (TElem (ELiteral (LInt 0))) true (TElem (ELiteral (LInt hi)))) t2
        else res1
      else RFailure ""
    in
    if not (RFailure? aux)
    then aux
    else let rl = typ_included e  t3 t1l in
    if RFailure? rl
    then typ_included e  t3 t1r
    else rl
  | TTagged tag1 t1', TTagged tag2 t2' ->
    if tag1 = tag2 || None? tag2
    then typ_included e  t1' t2'
    else RFailure "typ_included: TTagged with different tags"
  | TTagged _ _, _
  | _, TTagged _ _ -> RFailure "typ_included: TTagged vs. anything"
  | TSize base range, t ->
    let res1 = typ_included e  base t in
    if not (RFailure? res1)
    then res1
    else let res0 = typ_included e  base (TChoice (TElem EByteString) (TElem ETextString)) in
    if not (RSuccess? res0)
    then res0
    else begin match extract_range_value e.e_sem_env range with
    | None -> RSuccess ()
    | Some (rlo, rhi) ->
      let lo = eval_int_value rlo in
      let hi = eval_int_value rhi in
      if lo > hi
      then RSuccess ()
      else begin match t with
      | TSize base' range' ->
        let res2 = typ_included e  base base' in
        if not (RSuccess? res2)
        then res2
        else begin match extract_range_value e.e_sem_env range' with
        | None -> RFailure "typ_included: TSize vs. TSize not range"
        | Some (rlo', rhi') ->
          if eval_int_value rlo' <= lo && hi <= eval_int_value rhi'
          then RSuccess ()
          else RFailure "typ_included: TSize string"
        end
      | _ -> RFailure "typ_included: TSize vs. something else"
      end
    end
  | _, TSize base range ->
    let res1 = typ_included e  t1 base in
    if not (RSuccess? res1)
    then res1
    else begin match t1 with
    | TElem (ELiteral (LTextString s)) ->
      begin match extract_range_value e.e_sem_env range with
      | None -> RFailure "typ_included: LTextString vs. TSize not range"
      | Some (tlo, thi) ->
        let lo = eval_int_value tlo in
        let hi = eval_int_value thi in
        let len = String.length s in
        if lo <= len && len <= hi
        then RSuccess ()
        else RFailure "typ_included: LTextString vs. TSize"
      end
    | _ ->
      begin match extract_int_value e.e_sem_env range with
      | None -> RFailure "typ_included: any vs. TSize not int"
      | Some ri ->
        let j = eval_int_value ri in
        if j < 0
        then RFailure "typ_included: any vs. TSize negative"
        else let i = (let open FStar.Mul in 8 * j) in
        if i >= 64
        then begin
          FStar.Math.Lemmas.pow2_le_compat i 64;
          typ_included e  t1 (TElem EUInt)
        end else begin
          FStar.Math.Lemmas.pow2_lt_compat 64 i;
          typ_included e  t1 (TRange (TElem (ELiteral (LInt 0))) true (TElem (ELiteral (LInt (pow2 i - 1)))))
        end
      end
    end
  | TRange _tlo _included _thi, t ->
    begin match extract_range_value e.e_sem_env (TRange _tlo _included _thi) with
    | None -> RSuccess ()
    | Some (lo, hi) ->
      let lo = eval_int_value lo in
      let hi = eval_int_value hi in
      if lo > hi
      then RSuccess ()
      else begin match t with
      | TElem (ELiteral (LInt v)) -> if v = lo && v = hi then RSuccess () else RFailure "typ_included: TRange vs. TElem ELiteral LInt"
      | TElem EUInt -> if lo >= 0 then RSuccess () else RFailure "typ_included: TRange vs. TElem EUInt"
      | TElem ENInt -> if hi < 0 then RSuccess () else RFailure "typ_included: TRange vs. TElem ENInt"
      | TRange _tlo' _included _thi' ->
        begin match extract_range_value e.e_sem_env (TRange _tlo' _included _thi') with
        | None -> RFailure "typ_included: TRange vs. TRange lo"
        | Some (lo', hi') ->
          let lo' = eval_int_value lo' in
          let hi' = eval_int_value hi' in
          if lo' <= lo && hi <= hi'
          then RSuccess ()
          else RFailure "typ_included: TRange vs. TRange"
        end
      | _ -> RFailure "typ_included: TRange vs. any"
      end
    end
  | TElem (ELiteral (LInt n)), TRange _tlo _included _thi ->
    begin match extract_range_value e.e_sem_env (TRange _tlo _included _thi) with
    | None -> RFailure "typ_included: TElem vs. TRange lo"
    | Some (lo, hi) ->
      let lo = eval_int_value lo in
      let hi = eval_int_value hi in
      if lo <= n && n <= hi
      then RSuccess ()
      else RFailure "typ_included: TElem vs. TRange"
    end
  | _, TRange _ _ _ -> RFailure "typ_included: any vs. TRange"
  | TDetCbor _ _, TElem EByteString -> RSuccess ()
  | TDetCbor base dest, TDetCbor base' dest' ->
    let res1 = typ_included e  base base' in
    if not (RSuccess? res1)
    then res1
    else typ_included e  dest dest'
  | TDetCbor _ dest, _ -> typ_included e  dest (TElem EAlwaysFalse)
  | TElem (ELiteral (LSimple v)), TElem ESimple
  | TElem (ELiteral (LSimple v)), TElem EBool ->
    if U8.uint_to_t v = simple_value_true || U8.uint_to_t v = simple_value_false
    then RSuccess ()
    else RFailure "typ_included: TElem EBool"
  | TElem EBool, TElem ESimple -> RSuccess ()
  | TElem (ELiteral (LInt v)), TElem EUInt ->
    if v >= 0
    then RSuccess ()
    else RFailure "typ_included: uint64"
  | TElem (ELiteral (LInt v)), TElem ENInt ->
    if v < 0
    then RSuccess ()
    else RFailure "typ_included: neg_int64"
  | TElem (ELiteral (LTextString _)), TElem EByteString ->
    RFailure "typ_included: byte string"
  | TElem (ELiteral (LTextString _)), TElem ETextString ->
    RSuccess ()
  | TArray a1, TArray a2 ->
    Spec.array_close_array_group (array_group_sem e.e_sem_env a1);
    Spec.array_close_array_group (array_group_sem e.e_sem_env a2);
    array_group_included e  true a1 a2
  | TMap _, _
  | _, TMap _
    -> RFailure "typ_included: unsupported cases: map"
  | TElem _, _
  | _, TElem _
  | TArray _, _
  | _, TArray _
    -> RFailure ("typ_included: unsupported cases: \n" ^ CDDL.Spec.AST.Print.typ_to_string t1 ^ "\n vs. \n" ^ CDDL.Spec.AST.Print.typ_to_string t2)
