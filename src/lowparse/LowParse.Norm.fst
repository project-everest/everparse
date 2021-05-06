module LowParse.Norm

noeq
type norm_t : Type = | Norm

let norm_steps = [delta_attr [`%Norm]; iota; zeta; primops]
