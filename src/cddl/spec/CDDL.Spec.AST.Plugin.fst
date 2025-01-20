module CDDL.Spec.AST.Plugin

[@@plugin]
let parse : list string -> CDDL.Spec.AST.Plugin.Base.result = CDDL.Spec.AST.Plugin.Parser.parse
