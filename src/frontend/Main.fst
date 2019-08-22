module Main
open FStar.All
open Ast
open ParserDriver

let test =
  let cmdline = FStar.Getopt.cmdline() in
  match cmdline with
  | [_; fn] ->
    let x = ParserDriver.parse fn in
    ()
  | _ ->
    failwith "Not enough arguments"
