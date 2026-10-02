module EverParse3d.Util

(* This mirrors `src/3d/prelude/EverParse3d.Util.fst`, the tactic the Low*
   prelude uses to resolve the `extra_t` client context of an input stream from
   whatever binder happens to be in scope at the call site.

   It differs from the Low* version in one respect: it falls back to `()` when
   no context binder is available. The Low* version does not need this because
   its generated buffer-backend validators are not `fn`s, so the `extra_t =
   unit` of the buffer instance never reaches the tactic. In Pulse the binder is
   declared directly on each `fn` (a Pulse `fn` silently drops implicit binders
   that arrive through a type ascription), so the buffer backend does reach the
   tactic with goal type `unit`, and must be able to discharge it. *)

open FStar.Tactics.V2

let solve_from_ctx () : Tac unit =
  ignore (intros ());
  let bs = vars_of_env (cur_env ()) in
  first (
    map (fun (b: binding) () -> exact b) bs @
    [(fun () -> exact (`()))]
  )
