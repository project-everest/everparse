module Abort
#lang-pulse
open Pulse.Lib.Pervasives
(* Realized by libc's abort.  karamel gets the unqualified C name from
   -no-prefix Abort; Custard's --custard_c_no_prefix covers definitions, not
   assume vals, so the target name is given here. *)
[@@ FStar.Attributes.custard_extern "abort";
    FStar.Attributes.custard_c_header "stdlib.h"]
assume val abort () : stt unit emp (fun _ -> pure False)
