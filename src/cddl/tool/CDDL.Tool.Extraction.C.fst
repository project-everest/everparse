module CDDL.Tool.Extraction.C
open CDDL.Pulse.AST.Bundle
open CDDL.Tool.Gen
module DetC = CDDL.Pulse.AST.Det.C
module Impl = CDDL.Pulse.AST.Validate
module Env = CDDL.Pulse.AST.Env
module Parse = CDDL.Pulse.AST.Parse
module T = CDDL.Pulse.AST.Tactics
module SZ = FStar.SizeT
module C = C // for _zero_for_deref
