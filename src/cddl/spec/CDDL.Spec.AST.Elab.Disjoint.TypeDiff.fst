module CDDL.Spec.AST.Elab.Disjoint.TypeDiff
include CDDL.Spec.AST.Elab.Base
module Cbor = CBOR.Spec.API.Type
module Spec = CDDL.Spec.All
module U64 = FStar.UInt64
module Util = CBOR.Spec.Util
module U8 = FStar.UInt8

#push-options "--z3rlimit 64 --split_queries always --query_stats --fuel 4 --ifuel 8"

let typ_diff_disjoint
  (typ_disjoint: typ_disjoint_t)
  (typ_included: typ_included_t)
  (typ_diff_disjoint: typ_diff_disjoint_t)
: Tot typ_diff_disjoint_t
= fun env t1 d1 t2 d2 ->
  match t1 with
  | TChoice t1l t1r ->
    begin match typ_diff_disjoint env t1l d1 t2 d2 with
    | RSuccess _ ->
      typ_diff_disjoint env t1r d1 t2 d2
    | res -> res
    end
  | TDef i ->
    let t1' = env.e_env i in
    typ_diff_disjoint env t1' d1 t2 d2
  | _ ->
    begin match t2 with
    | TChoice t2l t2r ->
      begin match typ_diff_disjoint env t1 d1 t2l d2 with
      | RSuccess _ -> typ_diff_disjoint env t1 d1 t2r d2
      | res -> res
      end
    | TDef i ->
      let t2' = env.e_env i in
      typ_diff_disjoint env t1 d1 t2' d2
    | _ ->
      begin match typ_disjoint env t1 t2 with
      | RFailure _ ->
        begin match typ_included env t1 d2 with
        | RFailure _ -> typ_included env t2 d1
        | res -> res
        end
      | res -> res
      end
    end
