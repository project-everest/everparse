module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = LowStar.Monotonic.Buffer
module B0 = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

#set-options "--z3rlimit 16"

let gaccessor_synth
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: squash (synth_inverse f g /\ synth_injective f))
: Tot (gaccessor (parse_synth p1 f) p1 (clens_synth g f))
= synth_injective_synth_inverse_synth_inverse_recip f g ();
  gaccessor_prop_equiv (parse_synth p1 f) p1 (clens_synth g f) (gaccessor_synth' p1 f g u);
  gaccessor_synth' p1 f g u

let gaccessor_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
  (input: bytes)
: Lemma
  (gaccessor_synth p1 f g u input == gaccessor_synth' p1 f g u input)
= ()

let gaccessor_synth_inv
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: squash (synth_inverse f g /\ synth_injective f))
: Tot (gaccessor p1 (parse_synth p1 f) (clens_synth_inv g f))
= gaccessor_prop_equiv p1 (parse_synth p1 f) (clens_synth_inv g f) (gaccessor_synth_inv' p1 f g u);
  gaccessor_synth_inv' p1 f g u

let gaccessor_synth_inv_eq
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
  (input: bytes)
: Lemma
  (gaccessor_synth_inv p1 f g u input == gaccessor_synth_inv' p1 f g u input)
= ()
