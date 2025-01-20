module CDDLTest

[@@FStar.Tactics.postprocess_with (fun _ -> FStar.Tactics.norm [primops]; FStar.Tactics.trefl ())]
let foo = CDDL.Spec.AST.Plugin.parse ["cose.cddl"; "../spec/postlude.cddl"]

let _ = assert (Some? foo)
