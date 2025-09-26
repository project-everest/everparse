module Abort
#lang-pulse
open Pulse.Lib.Pervasives
assume val abort () : stt unit emp (fun _ -> pure False)
