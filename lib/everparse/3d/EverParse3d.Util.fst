module EverParse3d.Util

(* Resolves the `extra_t` client context of an input stream from whatever
   binder happens to be in scope at the call site, falling back to `()` when no
   context binder is available.

   The fallback is needed because the binder is declared directly on each `fn`
   (a Pulse `fn` silently drops implicit binders that arrive through a type
   ascription), so the buffer backend, whose `extra_t` is `unit`, reaches the
   tactic with goal type `unit` and must be able to discharge it. *)

open FStar.Tactics.V2

let solve_from_ctx () : Tac unit =
  ignore (intros ());
  let bs = vars_of_env (cur_env ()) in
  first (
    map (fun (b: binding) () -> exact b) bs @
    [(fun () -> exact (`()))]
  )
