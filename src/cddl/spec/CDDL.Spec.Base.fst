module CDDL.Spec.Base
module Cbor = CBOR.Spec.API.Type
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
let bounded_typ_gen (e: option Cbor.cbor) = (e': Cbor.cbor { opt_precedes e' e }) -> Tot bool

[@@noextract_to "krml"]
let typ = bounded_typ_gen None

let any : typ = (fun _ -> true)
let t_always_false : typ = (fun _ -> false)

[@@noextract_to "krml"]
let bounded_typ (e: Cbor.cbor) = bounded_typ_gen (Some e)

let coerce_to_bounded_typ
  (b: option Cbor.cbor)
  (t: typ)
: Tot (bounded_typ_gen b)
= t

noextract
let typ_equiv
  (#b: option Cbor.cbor)
  (t1 t2: bounded_typ_gen b)
: Tot prop
= forall x . t1 x == t2 x

let typ_included (f1 f2: typ) : Tot prop =
  forall x . f1 x ==> f2 x

let typ_disjoint (a1 a2: typ) : Tot prop
= (forall (l: Cbor.cbor) . ~ (a1 l /\ a2 l))

let t_literal (i: Cbor.cbor) : typ =
  (fun x -> x = i)

let t_choice (#b: option Cbor.cbor) (t1 t2: bounded_typ_gen b) : bounded_typ_gen b = (fun x -> t1 x || t2 x)

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

let parser_spec (source:typ) (target: Type0) (target_prop: target -> bool) = (c: Cbor.cbor { source c }) -> Tot (y: target { target_prop y })

let serializer_spec (#source:typ) (#target: Type0) (#target_prop: target -> bool) (p: parser_spec source target target_prop) =
  ((x: target { target_prop x }) -> Tot (y: Cbor.cbor { source y /\ p y == x }))

noeq
type spec (source:typ) (target: Type0) (inj: bool) = {
  serializable: target -> bool;
  parser: parser_spec source target serializable;
  serializer: serializer_spec parser;
  parser_inj: squash (inj ==> (forall (c: Cbor.cbor { source c }) . serializer (parser c) == c));
}

let spec_ext
  (#source: typ) (#target: Type0) (#inj: bool) (s: spec source target inj) (source' : typ) : Pure (spec source' target inj)
    (requires typ_equiv source source')
    (ensures fun _ -> True)
= {
  serializable = (fun x -> s.serializable x);
  parser = (fun x -> s.parser x);
  serializer = (fun x -> s.serializer x);
  parser_inj = ();
}

let spec_coerce_target_prop
  (#source:typ) (#target: Type0) (#inj: bool)
  (p: spec source target inj)
  (target_prop' : (target -> bool) {
    forall x . target_prop' x == p.serializable x
  })
: Tot (spec source target inj)
= {
  serializable = target_prop';
  parser = (p.parser <: parser_spec source target target_prop');
  serializer = p.serializer;
  parser_inj = ();
}

let serializable_inj
  (#target1: Type0)
  (target1_prop: (target1 -> bool))
  (#target2: Type0)
  (f21: (target2 -> target1))
  (x: target2)
: Tot bool
= target1_prop (f21 x)

let parse_spec_inj (#source:typ) (#target1 #target2: Type0) (#target1_prop: target1 -> bool) (p: parser_spec source target1 target1_prop) (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x))
: Tot (parser_spec source target2 (serializable_inj target1_prop f21))
= fun c -> let x1 = p c in prf_21_12 x1; f12 x1

let serialize_spec_inj (#source:typ) (#target1 #target2: Type0) (#target1_prop: target1 -> bool) (#p: parser_spec source target1 target1_prop) (s: serializer_spec p) (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x)) (prf_12_21: (x: target2) -> squash (f12 (f21 x) == x))
: Tot (serializer_spec (parse_spec_inj p f12 f21 prf_21_12))
= fun x2 -> prf_12_21 x2; s (f21 x2)

let spec_inj_injective
  (#source:typ) (#target1 #target2: Type0) (#inj: bool)
  (s: spec source target1 inj)
  (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x)) (prf_12_21: (x: target2) -> squash (f12 (f21 x) == x))
  (c: Cbor.cbor { source c })
: Lemma
  (ensures (inj ==> serialize_spec_inj s.serializer f12 f21 prf_21_12 prf_12_21 (parse_spec_inj s.parser f12 f21 prf_21_12 c) == c))
= if inj
  then begin
    prf_21_12 (s.parser c)
  end

let spec_inj
  (#source:typ) (#target1 #target2: Type0) (#inj: bool)
  (s: spec source target1 inj)
  (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x)) (prf_12_21: (x: target2) -> squash (f12 (f21 x) == x))
: Tot (spec source target2 inj)
= {
  serializable = serializable_inj s.serializable f21;
  parser = parse_spec_inj s.parser f12 f21 prf_21_12;
  serializer = serialize_spec_inj s.serializer f12 f21 prf_21_12 prf_12_21;
  parser_inj = Classical.forall_intro (spec_inj_injective s f12 f21 prf_21_12 prf_12_21);
}

let parse_spec_bij (#source:typ) (#target1 #target2: Type0) (#target1_prop: target1 -> bool) (p: parser_spec source target1 target1_prop) (target2_prop: target2 -> bool) (bij: bijection target1 target2 {
  forall x . target2_prop x <==> target1_prop (bij.bij_to_from x)
}) : parser_spec source target2 target2_prop =
  (fun c -> bij.bij_from_to (p c))

let serialize_spec_bij (#source:typ) (#target1 #target2: Type0) (#target1_prop: _ -> bool) (#target2_prop: _ -> bool) (#p: parser_spec source target1 target1_prop) (s: serializer_spec p) (bij: bijection target1 target2 {
  forall x . target2_prop x <==> target1_prop (bij.bij_to_from x)
}) : serializer_spec (parse_spec_bij p target2_prop bij) =
  (fun x -> s (bij.bij_to_from x))

let spec_bij_serializable
  (#source:typ) (#target1 #target2: Type0) (#inj: bool) (p: spec source target1 inj) (bij: bijection target1 target2) (x: target2) : Tot bool
= p.serializable (bij.bij_to_from x)

let spec_bij (#source:typ) (#target1 #target2: Type0) (#inj: bool) (p: spec source target1 inj) (bij: bijection target1 target2)
: spec source target2 inj = {
  serializable = spec_bij_serializable p bij;
  parser = parse_spec_bij p.parser _ bij;
  serializer = serialize_spec_bij p.serializer bij;
  parser_inj = ();
}

let parser_spec_literal (x: Cbor.cbor) (p: unit -> bool { p () }) : Tot (parser_spec (t_literal x) unit p) =
  fun _ -> ()

let serializer_spec_literal (x: Cbor.cbor) (p: unit -> bool { p () }) : Tot (serializer_spec (parser_spec_literal x p)) = (fun _ -> x)

let spec_literal_serializable (_: unit) : Tot bool = true

let spec_literal (x: Cbor.cbor) : Tot  (spec (t_literal x) unit true) = {
  serializable = spec_literal_serializable;
  parser = parser_spec_literal x _;
  serializer = serializer_spec_literal x _;
  parser_inj = ();
}

let spec_choice_serializable
  (#target1: Type0)
  (target1_ser: target1 -> bool)
  (#target2: Type0)
  (target2_ser: target2 -> bool)
  (x: target1 `either` target2)
: Tot bool
= match x with
    | Inl x1 -> target1_ser x1
    | Inr x2 -> target2_ser x2

let parser_spec_choice
  (#source1: typ)
  (#target1: Type0)
  (#target1_prop: _ -> bool)
  (p1: parser_spec source1 target1 target1_prop)
  (#source2: typ)
  (#target2: Type0)
  (#target2_prop: _ -> bool)
  (p2: parser_spec source2 target2 target2_prop)
  (target_prop: (target1 `either` target2) -> bool {
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
  (#target1_prop: _ -> bool)
  (#p1: parser_spec source1 target1 target1_prop)
  (s1: serializer_spec p1)
  (#source2: typ)
  (#target2: Type0)
  (#target2_prop: _ -> bool)
  (#p2: parser_spec source2 target2 target2_prop)
  (s2: serializer_spec p2 { source1 `typ_disjoint` source2 }) // disjointness needed to avoid the CBOR object serialized from one case to be parsed into the other case
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target1_prop x1
    | Inr x2 -> target2_prop x2
    end
  })
: Tot (serializer_spec (parser_spec_choice p1 p2 target_prop))
= fun x -> match x with
  | Inl y -> s1 y
  | Inr y -> s2 y

let spec_choice
  (#source1: typ)
  (#target1: Type0)
  (#inj1: bool)
  (p1: spec source1 target1 inj1)
  (#source2: typ)
  (#target2: Type0)
  (#inj2: bool)
  (p2: spec source2 target2 inj2 { source1 `typ_disjoint` source2 })
: Tot (spec (source1 `t_choice` source2) (target1 `either` target2) (inj1 && inj2))
= {
  serializable = spec_choice_serializable p1.serializable p2.serializable;
  parser = parser_spec_choice p1.parser p2.parser _;
  serializer = serializer_spec_choice p1.serializer p2.serializer _;
  parser_inj = ();
}

let parser_spec_always_false (p: squash False -> bool) : parser_spec t_always_false (squash False) p =
  (fun x -> false_elim ())

let serializer_spec_always_false (p: squash False -> bool) : serializer_spec (parser_spec_always_false p) =
  (fun x -> false_elim ())

let spec_always_false
  (p: (squash False -> bool))
: spec t_always_false (squash False) true
= {
  serializable = p;
  parser = parser_spec_always_false p;
  serializer = serializer_spec_always_false p;
  parser_inj = ();
}
