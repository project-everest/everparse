module Deps

open FStar.All

val get_sorted_deps (fn:string) : ML (list string)
