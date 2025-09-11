module CDDL.Tool.Plugin.Base

[@@plugin]
type result = option (list (string & CDDL.Spec.AST.Driver.decl))
