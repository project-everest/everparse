module CDDL.Tool.Plugin

[@@plugin]
let parse : list string -> CDDL.Tool.Plugin.Base.result = CDDL.Tool.Plugin.Parser.parse
