open Fstarcompiler
open Prims
type 'a termable =
  {
  to_term:
    'a -> (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr }
let __proj__Mktermable__item__to_term :
  'a .
    'a termable ->
      'a ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
  = fun projectee -> match projectee with | { to_term;_} -> to_term
let to_term :
  'a .
    'a termable ->
      'a ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun projectee -> match projectee with | { to_term = to_term1;_} -> to_term1
let (termable_term : FStarC_Reflection_Types.term termable) =
  { to_term = (fun uu___ -> (fun t -> Obj.magic (fun uu___ -> t)) uu___) }
let (termable_binding : FStarC_Reflection_V2_Data.binding termable) =
  {
    to_term =
      (fun uu___ ->
         (fun b ->
            Obj.magic
              (fun uu___ ->
                 FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)) uu___)
  }
let mapply :
  'ty . 'ty termable -> 'ty -> (unit, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    fun x ->
      fun ps ->
        let x1 = to_term uu___ x ps in FStar_Tactics_MApply0.mapply0 x1 ps
