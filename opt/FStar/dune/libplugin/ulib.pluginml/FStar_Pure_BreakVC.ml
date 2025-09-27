open Fstarcompiler
open Prims
type 'p break_wp' = unit FStar_Pervasives.spinoff
let (post : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    fun ps ->
      FStarC_Tactics_V2_Builtins.norm
        [Fstarcompiler.FStarC_NormSteps.delta_fully
           ["FStar.Pure.BreakVC.mono_lem"; "FStar.Pure.BreakVC.break_wp'"]]
        ps;
      FStar_Tactics_V2_Derived.trefl () ps
type 'p break_wp = unit FStar_Pervasives.spinoff
type ('p, 'q) op_Equals_Equals_Greater_Greater = unit
