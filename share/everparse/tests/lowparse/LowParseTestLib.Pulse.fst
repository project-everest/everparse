module LowParseTestLib.Pulse
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module U8 = FStar.UInt8
module U32 = FStar.UInt32

assume val print_string : (s: string) -> stt unit emp (fun _ -> emp)

assume val exit_failure : unit -> stt unit emp (fun _ -> emp)

inline_for_extraction
let test_validator_accept
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (testname: string)
  (input: S.slice byte)
  (#pm: perm)
  (#contents: Ghost.erased bytes)
: stt unit
    (pts_to input #pm contents)
    (fun _ -> pts_to input #pm contents)
= admit ()

inline_for_extraction
let test_validator_reject
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
  (testname: string)
  (input: S.slice byte)
  (#pm: perm)
  (#contents: Ghost.erased bytes)
: stt unit
    (pts_to input #pm contents)
    (fun _ -> pts_to input #pm contents)
= admit ()
