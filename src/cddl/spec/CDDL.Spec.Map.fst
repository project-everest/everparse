module CDDL.Spec.Map
module F = FStar.FunctionalExtensionality

noeq
type uunit : Type u#a = | UU

let codom
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (dom: S.t spec_key)
  ([@@@strictly_positive] value: Type u#a)
  (k: key)
: Tot (Type u#a)
= if S.mem k dom then value else uunit

noeq
type t
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  ([@@@strictly_positive] value: Type u#a)
: Type u#a
= {
  dom: S.t spec_key;
  map: F.restricted_t key (codom spec_key dom value);
}

let get m k =
  if S.mem k m.dom
  then Some (m.map k)
  else None

let ext #key #key_s #_ #value m1 m2 =
  assert (equal m1 m2 ==> S.equal m1.dom m2.dom);
  assert (equal m1 m2 ==> F.feq m1.map m2.map)

let length m = S.cardinality m.dom

let key_set m = m.dom

let empty #key spec_key value =
  let dom : S.t spec_key = S.emptyset _ in {
  dom = dom;
  map = F.on_dom key #(codom spec_key dom value) (fun _ -> UU);
}

let get_empty spec_key value k = ()

let singleton #key spec_key k v =
  let dom : S.t spec_key = S.singleton spec_key k in {
  dom = dom;
  map = F.on_dom key #(codom spec_key dom _) (fun k' -> if S.mem k' (S.singleton spec_key k) then v else UU);
}

let get_singleton spec_key k v k' = ()

let union #key #_ #spec_key m1 m2 =
  let dom : S.t spec_key = S.union m1.dom m2.dom in {
  dom = dom;
  map = F.on_dom key #(codom spec_key dom _) (fun k -> if S.mem k m1.dom then m1.map k else m2.map k);
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
= if S.mem k m.dom
  then f (k, m.map k)
  else false

let filter #key #_ #spec_key f m =
  let dom : S.t spec_key = S.filter (filter_op f m) m.dom in {
  dom = dom;
  map = F.on_dom key #(codom spec_key dom _)
    (fun k ->
      if S.mem k m.dom then
        let v = m.map k in
        if f (k, v)
        then v
        else UU
      else UU
    )
}

let get_filter f m k = ()
