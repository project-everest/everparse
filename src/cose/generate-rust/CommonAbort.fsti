module CommonAbort
open Pulse

val abort () : stt unit emp (fun _ -> pure False)