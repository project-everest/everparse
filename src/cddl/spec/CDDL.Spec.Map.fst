module CDDL.Spec.Map
module F = FStar.FunctionalExtensionality

noeq
type t
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (value: Type u#a)
: Type u#a
= {
  dom: S.t spec_key;
  map: F.restricted_t key (fun _ -> option value);
  map_dom: squash (forall (k: key) . Some? (map k) <==> S.mem k dom); // we need to do this restriction because restricting the domain of `map` causes issues for proving type equality when domains are equal
}

let get m k = m.map k

let ext m1 m2 =
  assert (equal m1 m2 ==> S.equal m1.dom m2.dom);
  assert (equal m1 m2 ==> F.feq m1.map m2.map)

let length m = S.cardinality m.dom

let key_set m = m.dom

let empty #key spec_key value = {
  dom = S.emptyset _;
  map = F.on_dom key (fun _ -> None);
  map_dom = ();
}

let get_empty spec_key value k = ()

let singleton #key spec_key k v = {
  dom = S.singleton spec_key k;
  map = F.on_dom key (fun k' -> if S.mem k' (S.singleton spec_key k) then Some v else None);
  map_dom = ();
}

let get_singleton spec_key k v k' = ()

let union #key m1 m2 = {
  dom = S.union m1.dom m2.dom;
  map = F.on_dom key (fun k -> match m1.map k with Some v -> Some v | _ -> m2.map k);
  map_dom = ();
}

let get_union m1 m2 k = ()

let filter_op
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (f: (key & value) -> bool)
  (m: t spec_key value)
  (k: key)
: Tot bool
= match m.map k with
  | Some v -> f (k, v)
  | _ -> false

let filter #key f m = {
  dom = S.filter (filter_op f m) m.dom;
  map = F.on_dom key (fun k -> match m.map k with Some v -> if f (k, v) then Some v else None | _ -> None);
  map_dom = ();
}

let get_filter f m k = ()
