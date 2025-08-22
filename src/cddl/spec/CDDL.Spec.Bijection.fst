module CDDL.Spec.Bijection

noeq
type bijection (from to: Type) = {
  bij_from_to: from -> to;
  bij_to_from: to -> from;
  bij_from_to_from: squash (forall (x: to) . bij_from_to (bij_to_from x) == x);
  bij_to_from_to: squash (forall (x: from) . bij_to_from (bij_from_to x) == x);
}

inline_for_extraction
let bij_id (t: Type) : bijection t t = {
  bij_from_to = (fun x -> x);
  bij_to_from = (fun x -> x);
  bij_from_to_from = ();
  bij_to_from_to = ();
}
