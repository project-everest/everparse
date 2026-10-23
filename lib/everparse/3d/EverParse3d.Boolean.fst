module EverParse3d.Boolean

module B = EverParse3d.CAbi.Boolean

noextract inline_for_extraction
class boolean_repr (t: Type0) = {
  to_bool: t -> Tot bool;
  of_bool: bool -> Tot t;
  of_bool_inverse: b:bool -> Lemma (to_bool (of_bool b) == b);
}

noextract inline_for_extraction
let boolean_bool : boolean_repr bool = {
  to_bool = (fun b -> b);
  of_bool = (fun b -> b);
  of_bool_inverse = (fun _ -> ());
}

noextract inline_for_extraction
let boolean_byte : boolean_repr B.t = {
  to_bool = B.to_bool;
  of_bool = B.of_bool;
  of_bool_inverse = B.round_trip;
}
