type result = unit CDDL_Spec_AST_Base.ast0_wf_typ CDDL_Spec_AST_Elab.result [@@deriving show]

let typ_to_string = CDDL_Spec_AST_Base.show_typ

let ast0_wf_typ_result_to_string _ = show_result
