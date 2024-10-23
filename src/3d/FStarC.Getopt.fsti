(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Getopt
open FStar.ST
open FStar.All
open FStar.Char

val noshort : char
val nolong : string
noeq
type opt_variant 'a =
  | ZeroArgs of (unit -> ML 'a)
  | OneArg of (string -> ML 'a) * string

type opt' 'a = char * string * opt_variant 'a
type opt = opt' unit

type parse_cmdline_res =
  | Help
  | Error of string
  | Success

val parse_cmdline: list opt  -> (string -> ML parse_cmdline_res) -> parse_cmdline_res
val parse_string: list opt  -> (string -> ML parse_cmdline_res) -> string -> parse_cmdline_res
val cmdline: unit -> list string
