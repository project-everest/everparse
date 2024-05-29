module CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Concise Data Definition Language (RFC 8610)

noextract
let opt_precedes
  (#t1 #t2: Type)
  (x1: t1)
  (x2: option t2)
: Tot prop
= match x2 with
  | None -> True
  | Some x2 -> x1 << x2

[@@noextract_to "krml"]
let bounded_typ_gen (e: option Cbor.raw_data_item) = (e': Cbor.raw_data_item { opt_precedes e' e }) -> GTot bool  // GTot needed because of the .cbor control (staged serialization)

[@@noextract_to "krml"]
let typ = bounded_typ_gen None

let any : typ = (fun _ -> true)
let t_always_false : typ = (fun _ -> false)

[@@noextract_to "krml"]
let bounded_typ (e: Cbor.raw_data_item) = bounded_typ_gen (Some e)

let coerce_to_bounded_typ
  (b: option Cbor.raw_data_item)
  (t: typ)
: Tot (bounded_typ_gen b)
= t

noextract
let typ_equiv
  (#b: option Cbor.raw_data_item)
  (t1 t2: bounded_typ_gen b)
: Tot prop
= forall x . t1 x == t2 x

let typ_included (f1 f2: typ) : Tot prop =
  forall x . f1 x ==> f2 x

let typ_disjoint (a1 a2: typ) : Tot prop
= (forall (l: Cbor.raw_data_item) . ~ (a1 l /\ a2 l))

let t_literal (i: Cbor.raw_data_item) : typ =
  (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (x == i))

let t_choice (#b: option Cbor.raw_data_item) (t1 t2: bounded_typ_gen b) : bounded_typ_gen b = (fun x -> t1 x || t2 x)

let t_choice_equiv
  #b
  (t1 t1' t2 t2' : bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t1' /\ t2 `typ_equiv` t2'))
  (ensures ((t1 `t_choice` t2) `typ_equiv` (t1' `t_choice` t2')))
= ()
// etc.

let t_choice_simpl
  #b
  (t: bounded_typ_gen b)
: Lemma
  ((t `t_choice` t) `typ_equiv` t)
= ()


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

let parser_spec (source:typ) (target: Type0) (target_prop: target -> prop) = (c: CBOR.Spec.raw_data_item { source c }) -> GTot (y: target { target_prop y })

let serializer_spec (#source:typ) (#target: Type0) (#target_prop: target -> prop) (p: parser_spec source target target_prop) =
  ((x: target { target_prop x }) -> GTot (y: CBOR.Spec.raw_data_item { source y /\ p y == x }))

[@@erasable]
noeq
type spec (source:typ) (target: Type0) = {
  serializable: target -> prop;
  parser: parser_spec source target serializable;
  serializer: serializer_spec parser;
}

let spec_ext
  (#source: typ) (#target: Type0) (s: spec source target) (source' : typ) : Pure (spec source' target)
    (requires typ_equiv source source')
    (ensures fun _ -> True)
= {
  serializable = (fun x -> s.serializable x);
  parser = (fun x -> s.parser x);
  serializer = (fun x -> s.serializer x);
}

let spec_coerce_target_prop
  (#source:typ) (#target: Type0)
  (p: spec source target)
  (target_prop' : (target -> prop) {
    forall x . target_prop' x <==> p.serializable x
  })
: Tot (spec source target)
= {
  serializable = target_prop';
  parser = (p.parser <: parser_spec source target target_prop');
  serializer = p.serializer;
}

let parse_spec_bij (#source:typ) (#target1 #target2: Type0) (#target1_prop: target1 -> prop) (p: parser_spec source target1 target1_prop) (target2_prop: target2 -> prop) (bij: bijection target1 target2 {
  forall x . target2_prop x <==> target1_prop (bij.bij_to_from x)
}) : parser_spec source target2 target2_prop =
  (fun c -> bij.bij_from_to (p c))

let serialize_spec_bij (#source:typ) (#target1 #target2: Type0) (#target1_prop: _ -> prop) (#target2_prop: _ -> prop) (#p: parser_spec source target1 target1_prop) (s: serializer_spec p) (bij: bijection target1 target2 {
  forall x . target2_prop x <==> target1_prop (bij.bij_to_from x)
}) : serializer_spec (parse_spec_bij p target2_prop bij) =
  (fun x -> s (bij.bij_to_from x))

let spec_bij_serializable
  (#source:typ) (#target1 #target2: Type0) (p: spec source target1) (bij: bijection target1 target2) (x: target2) : Tot prop
= p.serializable (bij.bij_to_from x)

let spec_bij (#source:typ) (#target1 #target2: Type0) (p: spec source target1) (bij: bijection target1 target2)
: spec source target2 = {
  serializable = spec_bij_serializable p bij;
  parser = parse_spec_bij p.parser _ bij;
  serializer = serialize_spec_bij p.serializer bij;
}

let parser_spec_literal (x: CBOR.Spec.raw_data_item) (p: unit -> prop { p () }) : Tot (parser_spec (t_literal x) unit p) =
  fun _ -> ()

let serializer_spec_literal (x: CBOR.Spec.raw_data_item) (p: unit -> prop { p () }) : Tot (serializer_spec (parser_spec_literal x p)) = (fun _ -> x)

let spec_literal_serializable (_: unit) : Tot prop = True

let spec_literal (x: CBOR.Spec.raw_data_item) : Tot  (spec (t_literal x) unit) = {
  serializable = spec_literal_serializable;
  parser = parser_spec_literal x _;
  serializer = serializer_spec_literal x _;
}

let parser_spec_choice
  (#source1: typ)
  (#target1: Type0)
  (#target1_prop: _ -> prop)
  (p1: parser_spec source1 target1 target1_prop)
  (#source2: typ)
  (#target2: Type0)
  (#target2_prop: _ -> prop)
  (p2: parser_spec source2 target2 target2_prop)
  (target_prop: (target1 `either` target2) -> prop {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target1_prop x1
    | Inr x2 -> target2_prop x2
    end
  })
: Tot (parser_spec (source1 `t_choice` source2) (target1 `either` target2) target_prop)
= fun x ->
    if source1 x
    then Inl (p1 x)
    else Inr (p2 x)

let serializer_spec_choice
  (#source1: typ)
  (#target1: Type0)
  (#target1_prop: _ -> prop)
  (#p1: parser_spec source1 target1 target1_prop)
  (s1: serializer_spec p1)
  (#source2: typ)
  (#target2: Type0)
  (#target2_prop: _ -> prop)
  (#p2: parser_spec source2 target2 target2_prop)
  (s2: serializer_spec p2 { source1 `typ_disjoint` source2 }) // disjointness needed to avoid the CBOR object serialized from one case to be parsed into the other case
  (target_prop: (target1 `either` target2) -> prop {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target1_prop x1
    | Inr x2 -> target2_prop x2
    end
  })
: Tot (serializer_spec (parser_spec_choice p1 p2 target_prop))
= fun x -> match x with
  | Inl y -> s1 y
  | Inr y -> s2 y

let spec_choice_serializable
  (#source1: typ)
  (#target1: Type0)
  (p1: spec source1 target1)
  (#source2: typ)
  (#target2: Type0)
  (p2: spec source2 target2)
  (x: target1 `either` target2)
: Tot prop  
= match x with
    | Inl x1 -> p1.serializable x1
    | Inr x2 -> p2.serializable x2

let spec_choice
  (#source1: typ)
  (#target1: Type0)
  (p1: spec source1 target1)
  (#source2: typ)
  (#target2: Type0)
  (p2: spec source2 target2 { source1 `typ_disjoint` source2 })
: Tot (spec (source1 `t_choice` source2) (target1 `either` target2))
= {
  serializable = spec_choice_serializable p1 p2;
  parser = parser_spec_choice p1.parser p2.parser _;
  serializer = serializer_spec_choice p1.serializer p2.serializer _;
}
