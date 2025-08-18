module CDDL.Spec.AST.Elab.Included.Type
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 256 --query_stats --split_queries always --fuel 4 --ifuel 8"

let typ_included
  (typ_disjoint: typ_disjoint_t)
  (typ_included: typ_included_t)
  (typ_included2: typ_included_t) 
: typ_included_t
= fun e t1 t2 ->
  match t1, t2 with
  | TNamed _ t1, t2
  | t1, TNamed _ t2 -> typ_included e t1 t2
  | _, TElem EAny
  | TElem EAlwaysFalse, _ -> RSuccess ()
  | _ ->
    if t1 = t2
    then RSuccess ()
    else
    let aux = match t1 with
    | TSize base range ->
      begin match typ_disjoint e base (TChoice (TElem EByteString) (TElem ETextString)) with
      | ROutOfFuel -> ROutOfFuel
      | RSuccess _ ->
        begin match extract_int_value e.e_sem_env range with
        | None -> RSuccess ()
        | Some ti ->
          let j = eval_int_value ti in
          if j < 0
          then RSuccess ()
          else let i : nat = (let open FStar.Mul in 8 * j) in
          if i >= 64
          then begin
            FStar.Math.Lemmas.pow2_le_compat i 64;
            typ_included e  (TElem EUInt) t2
          end
          else begin
            FStar.Math.Lemmas.pow2_lt_compat 64 i;
            typ_included e  (TRange (TElem (ELiteral (LInt 0))) true (TElem (ELiteral (LInt (pow2 i - 1))))) t2
          end
        end
      | RFailure _ ->
        let res1 = typ_disjoint e base (TElem EUInt) in
        if not (RSuccess? res1)
        then res1
        else begin match extract_range_value e.e_sem_env range with
        | None -> RFailure ""
        | Some (tlo, thi) ->
          let lo = eval_int_value tlo in
          let hi = eval_int_value thi in
          if lo > hi
          then RSuccess ()
          else begin match split_interval e.e_sem_env false lo hi t2 with
          | None -> RFailure ""
          | Some mi ->
            let res2 = typ_included e  (TSize base (TRange (TElem (ELiteral (LInt lo))) true (TElem (ELiteral (LInt mi))))) t2 in
            if not (RSuccess? res2)
            then res2
            else typ_included e  (TSize base (TRange (TElem (ELiteral (LInt (mi + 1)))) true (TElem (ELiteral (LInt hi))))) t2
          end
        end
      end
    | TRange _ _ _ ->
      begin match extract_range_value e.e_sem_env t1 with
      | None -> RSuccess ()
      | Some (rlo, rhi) ->
        let lo = eval_int_value rlo in
        let hi = eval_int_value rhi in
        if lo > hi
        then RSuccess ()
        else begin match split_interval e.e_sem_env true lo hi t2 with
        | None -> RFailure ""
        | Some mi ->
          let res1 = typ_included e  (TRange (TElem (ELiteral (LInt lo))) true (TElem (ELiteral (LInt mi)))) t2 in
          if not (RSuccess? res1)
          then res1
          else typ_included e  (TRange (TElem (ELiteral (LInt (mi + 1)))) true (TElem (ELiteral (LInt hi)))) t2
        end
      end
    | _ -> RFailure ""
    in
    if not (RFailure? aux)
    then aux
    else typ_included2 e  t1 t2
