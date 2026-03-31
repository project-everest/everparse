module LowParse.Pulse.Sum
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.Enum
open LowParse.Spec.Sum

module SZ = FStar.SizeT
module LPC = LowParse.Pulse.Combinators
module LPB = LowParse.Pulse.Base

let serialize_sum_eq_all
  (#kt: Ghost.erased parser_kind) (t: sum) (#p: parser kt (sum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x))))) (x: sum_type t)
: Lemma
  (bare_serialize (serialize_sum t s sc) x ==
    Seq.append (bare_serialize (serialize_enum_key _ s (sum_enum t)) (sum_tag_of_data t x))
               (bare_serialize (serialize_sum_cases t pc sc (sum_tag_of_data t x)) x) /\
    Seq.length (bare_serialize (serialize_sum t s sc) x) ==
    Seq.length (bare_serialize (serialize_enum_key _ s (sum_enum t)) (sum_tag_of_data t x)) +
    Seq.length (bare_serialize (serialize_sum_cases t pc sc (sum_tag_of_data t x)) x))
  [SMTPat (bare_serialize (serialize_sum t s sc) x)]
= serialize_sum_eq t s sc x;
  Seq.lemma_len_append
    (bare_serialize (serialize_enum_key _ s (sum_enum t)) (sum_tag_of_data t x))
    (bare_serialize (serialize_sum_cases t pc sc (sum_tag_of_data t x)) x)

let l2r_leaf_write_sum_pre_tag_lemma
  (#kt: Ghost.erased parser_kind) (t: sum) (#p: parser kt (sum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (x: sum_type t) (offset: SZ.t) (v: Ghost.erased bytes)
  (_: squash (SZ.v offset + Seq.length (bare_serialize (serialize_sum t s sc) x) <= Seq.length v))
: squash (SZ.v offset + Seq.length (bare_serialize (serialize_enum_key _ s (sum_enum t)) (sum_tag_of_data t x)) <= Seq.length v)
= serialize_sum_eq_all t s sc x

let l2r_leaf_write_sum_pre_case_lemma
  (#kt: Ghost.erased parser_kind) (t: sum) (#p: parser kt (sum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (x: sum_type t) (offset: SZ.t) (v: Ghost.erased bytes) (off1: SZ.t) (v1: bytes)
  (_: squash (
    SZ.v offset + Seq.length (bare_serialize (serialize_sum t s sc) x) <= Seq.length v /\
    LPB.l2r_leaf_writer_postcond (serialize_enum_key _ s (sum_enum t)) (sum_tag_of_data t x) offset v off1 v1))
: squash (SZ.v off1 + Seq.length (bare_serialize (serialize_sum_cases t pc sc (sum_tag_of_data t x)) x) <= Seq.length v1)
= serialize_sum_eq_all t s sc x

#push-options "--z3rlimit 128"

let l2r_leaf_write_sum_postcond_lemma
  (#kt: Ghost.erased parser_kind) (t: sum) (#p: parser kt (sum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (x: sum_type t)
  (offset: SZ.t) (v: Ghost.erased bytes) (off1: SZ.t) (v1: bytes) (off2: SZ.t) (v2: bytes)
  (_: squash (
    let tg = sum_tag_of_data t x in
    LPB.l2r_leaf_writer_postcond (serialize_enum_key _ s (sum_enum t)) tg offset v off1 v1 /\
    LPB.l2r_leaf_writer_postcond (serialize_sum_cases t pc sc tg) x off1 (Ghost.hide v1) off2 v2
  ))
: squash (LPB.l2r_leaf_writer_postcond (serialize_sum t s sc) x offset v off2 v2)
= let tg = sum_tag_of_data t x in
  serialize_sum_eq_all t s sc x;
  let bs_tag = bare_serialize (serialize_enum_key _ s (sum_enum t)) tg in
  let bs_case = bare_serialize (serialize_sum_cases t pc sc tg) x in
  let bs_sum = bare_serialize (serialize_sum t s sc) x in
  assert (bs_sum == Seq.append bs_tag bs_case);
  assert (Seq.length bs_sum == Seq.length bs_tag + Seq.length bs_case);
  assert (SZ.v off1 == SZ.v offset + Seq.length bs_tag);
  assert (SZ.v off2 == SZ.v off1 + Seq.length bs_case);
  assert (SZ.v off2 == SZ.v offset + Seq.length bs_sum);
  assert (Seq.length v2 == Seq.length v1);
  assert (Seq.length v1 == Seq.length v);
  assert (Seq.length v2 == Seq.length v);
  Seq.slice_slice v2 0 (SZ.v off1) 0 (SZ.v offset);
  Seq.slice_slice v1 0 (SZ.v off1) 0 (SZ.v offset);
  assert (Seq.slice v2 0 (SZ.v offset) == Seq.slice v 0 (SZ.v offset));
  Seq.slice_slice v2 0 (SZ.v off1) (SZ.v offset) (SZ.v off1);
  Seq.lemma_split (Seq.slice v2 (SZ.v offset) (SZ.v off2)) (SZ.v off1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) 0 (SZ.v off1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) (SZ.v off1 - SZ.v offset) (SZ.v off2 - SZ.v offset);
  Seq.lemma_eq_intro (Seq.slice v2 (SZ.v offset) (SZ.v off2)) bs_sum

#pop-options

#push-options "--z3rlimit 128"

inline_for_extraction
fn l2r_leaf_write_sum
  (#kt: Ghost.erased parser_kind) (t: sum) (#p: parser kt (sum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (w_tag: LPB.l2r_leaf_writer u#0 (serialize_enum_key _ s (sum_enum t)))
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (sc32: ((x: sum_key t) -> Tot (LPB.l2r_leaf_writer u#0 (sc x))))
  (destr: dep_enum_destr (sum_enum t) (LPC.l2r_leaf_write_sum_cases_t t sc))
: LPB.l2r_leaf_writer u#0 #(sum_type t) #(parse_sum_kind kt t pc) #(parse_sum t p pc) (serialize_sum t s sc)
= (x: sum_type t) (out: slice byte) (offset: SZ.t) (#v: Ghost.erased bytes)
{
  let tg = sum_tag_of_data t x;
  l2r_leaf_write_sum_pre_tag_lemma t s sc x offset v ();
  let off1 = w_tag tg out offset;
  with v1 . assert (pts_to out v1);
  l2r_leaf_write_sum_pre_case_lemma t s sc x offset v off1 v1 ();
  let w_case = LPC.l2r_leaf_write_sum_cases t sc sc32 destr tg;
  let off2 = w_case x out off1;
  with v2 . assert (pts_to out v2);
  l2r_leaf_write_sum_postcond_lemma t s sc x offset v off1 v1 off2 v2 ();
  off2
}

#pop-options


(* Dsum *)

let serialize_dsum_eq_all
  (#kt: Ghost.erased parser_kind) (t: dsum) (#p: parser kt (dsum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g) (x: dsum_type t)
: Lemma
  (bare_serialize (serialize_dsum t s f sf g sg) x ==
    Seq.append (bare_serialize (serialize_maybe_enum_key _ s (dsum_enum t)) (dsum_tag_of_data t x))
               (bare_serialize (serialize_dsum_cases t f sf g sg (dsum_tag_of_data t x)) x) /\
    Seq.length (bare_serialize (serialize_dsum t s f sf g sg) x) ==
    Seq.length (bare_serialize (serialize_maybe_enum_key _ s (dsum_enum t)) (dsum_tag_of_data t x)) +
    Seq.length (bare_serialize (serialize_dsum_cases t f sf g sg (dsum_tag_of_data t x)) x))
= serialize_dsum_eq' t s f sf g sg x;
  Seq.lemma_len_append
    (bare_serialize (serialize_maybe_enum_key _ s (dsum_enum t)) (dsum_tag_of_data t x))
    (bare_serialize (serialize_dsum_cases t f sf g sg (dsum_tag_of_data t x)) x)

let l2r_leaf_write_dsum_pre_tag_lemma
  (#kt: Ghost.erased parser_kind) (t: dsum) (#p: parser kt (dsum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (x: dsum_type t) (offset: SZ.t) (v: Ghost.erased bytes)
  (_: squash (SZ.v offset + Seq.length (bare_serialize (serialize_dsum t s f sf g sg) x) <= Seq.length v))
: squash (SZ.v offset + Seq.length (bare_serialize (serialize_maybe_enum_key _ s (dsum_enum t)) (dsum_tag_of_data t x)) <= Seq.length v)
= serialize_dsum_eq_all t s f sf g sg x

let l2r_leaf_write_dsum_pre_case_lemma
  (#kt: Ghost.erased parser_kind) (t: dsum) (#p: parser kt (dsum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (x: dsum_type t) (offset: SZ.t) (v: Ghost.erased bytes) (off1: SZ.t) (v1: bytes)
  (_: squash (
    SZ.v offset + Seq.length (bare_serialize (serialize_dsum t s f sf g sg) x) <= Seq.length v /\
    LPB.l2r_leaf_writer_postcond (serialize_maybe_enum_key _ s (dsum_enum t)) (dsum_tag_of_data t x) offset v off1 v1))
: squash (SZ.v off1 + Seq.length (bare_serialize (serialize_dsum_cases t f sf g sg (dsum_tag_of_data t x)) x) <= Seq.length v1)
= serialize_dsum_eq_all t s f sf g sg x

#push-options "--z3rlimit 128"

let l2r_leaf_write_dsum_postcond_lemma
  (#kt: Ghost.erased parser_kind) (t: dsum) (#p: parser kt (dsum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (x: dsum_type t)
  (offset: SZ.t) (v: Ghost.erased bytes) (off1: SZ.t) (v1: bytes) (off2: SZ.t) (v2: bytes)
  (_: squash (
    let tg = dsum_tag_of_data t x in
    LPB.l2r_leaf_writer_postcond (serialize_maybe_enum_key _ s (dsum_enum t)) tg offset v off1 v1 /\
    LPB.l2r_leaf_writer_postcond (serialize_dsum_cases t f sf g sg tg) x off1 (Ghost.hide v1) off2 v2
  ))
: squash (LPB.l2r_leaf_writer_postcond (serialize_dsum t s f sf g sg) x offset v off2 v2)
= let tg = dsum_tag_of_data t x in
  serialize_dsum_eq_all t s f sf g sg x;
  let bs_tag = bare_serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tg in
  let bs_case = bare_serialize (serialize_dsum_cases t f sf g sg tg) x in
  let bs_dsum = bare_serialize (serialize_dsum t s f sf g sg) x in
  Seq.slice_slice v2 0 (SZ.v off1) 0 (SZ.v offset);
  Seq.slice_slice v1 0 (SZ.v off1) 0 (SZ.v offset);
  Seq.slice_slice v2 0 (SZ.v off1) (SZ.v offset) (SZ.v off1);
  Seq.lemma_split (Seq.slice v2 (SZ.v offset) (SZ.v off2)) (SZ.v off1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) 0 (SZ.v off1 - SZ.v offset);
  Seq.slice_slice v2 (SZ.v offset) (SZ.v off2) (SZ.v off1 - SZ.v offset) (SZ.v off2 - SZ.v offset);
  Seq.lemma_eq_intro (Seq.slice v2 (SZ.v offset) (SZ.v off2)) bs_dsum

#pop-options

(* Dsum helper types *)

inline_for_extraction
let l2r_leaf_write_dsum_type_of_tag
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (LPB.l2r_leaf_writer u#0 (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: LPB.l2r_leaf_writer u#0 sg) (tg: dsum_key t)
: Tot (LPB.l2r_leaf_writer u#0 (serialize_dsum_type_of_tag t f sf g sg tg))
= match tg with
  | Known x' -> LPB.l2r_leaf_writer_ext_squash (sf32 x') (serialize_dsum_type_of_tag t f sf g sg tg) ()
  | Unknown x' -> LPB.l2r_leaf_writer_ext_squash sg32 (serialize_dsum_type_of_tag t f sf g sg tg) ()

inline_for_extraction
let l2r_leaf_write_dsum_cases_aux
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (LPB.l2r_leaf_writer u#0 (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: LPB.l2r_leaf_writer u#0 sg) (tg: dsum_key t)
: Tot (LPB.l2r_leaf_writer u#0 (serialize_dsum_cases t f sf g sg tg))
= [@inline_let] let _ = synth_dsum_case_injective t tg in
  [@inline_let] let _ = synth_dsum_case_inverse t tg in
  LPC.l2r_leaf_write_synth (l2r_leaf_write_dsum_type_of_tag t f sf sf32 sg32 tg)
    (synth_dsum_case t tg) (synth_dsum_case_recip t tg) (fun x -> synth_dsum_case_recip t tg x)

inline_for_extraction
let l2r_leaf_write_dsum_cases_t
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (k: dsum_known_key t) : Tot Type
= LPB.l2r_leaf_writer u#0 (serialize_dsum_cases t f sf g sg (Known k))

inline_for_extraction
let l2r_leaf_write_dsum_cases_t_if
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (#k': Ghost.erased parser_kind) (g: parser k' (dsum_type_of_unknown_tag t)) (sg: serializer g)
  (k: dsum_known_key t)
: Tot (if_combinator _ (fun (x y: l2r_leaf_write_dsum_cases_t t f sf g sg k) -> True))
= fun cond (sv_true: (cond_true cond -> Tot (l2r_leaf_write_dsum_cases_t t f sf g sg k)))
    (sv_false: (cond_false cond -> Tot (l2r_leaf_write_dsum_cases_t t f sf g sg k))) ->
  if cond then sv_true () else sv_false ()

inline_for_extraction
let l2r_leaf_write_dsum_cases
  (t: dsum) (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (LPB.l2r_leaf_writer u#0 (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: LPB.l2r_leaf_writer u#0 sg)
  (destr: dep_enum_destr _ (l2r_leaf_write_dsum_cases_t t f sf g sg)) (tg: dsum_key t)
: Tot (LPB.l2r_leaf_writer u#0 (serialize_dsum_cases t f sf g sg tg))
= match tg with
  | Known k -> destr _ (l2r_leaf_write_dsum_cases_t_if t f sf g sg) (fun _ _ -> ()) (fun _ _ _ _ -> ())
      (fun k -> l2r_leaf_write_dsum_cases_aux t f sf sf32 sg32 (Known k)) k
  | Unknown r -> l2r_leaf_write_dsum_cases_aux t f sf sf32 sg32 (Unknown r)

#push-options "--z3rlimit 128"

inline_for_extraction
fn l2r_leaf_write_dsum
  (#kt: Ghost.erased parser_kind) (t: dsum) (#p: parser kt (dsum_repr_type t))
  (s: serializer p { kt.parser_kind_subkind == Some ParserStrong })
  (w_tag: LPB.l2r_leaf_writer u#0 (serialize_maybe_enum_key _ s (dsum_enum t)))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (sf: (x: dsum_known_key t) -> Tot (serializer (dsnd (f x))))
  (sf32: (x: dsum_known_key t) -> Tot (LPB.l2r_leaf_writer u#0 (sf x)))
  (#k': Ghost.erased parser_kind) (#g: parser k' (dsum_type_of_unknown_tag t)) (#sg: serializer g)
  (sg32: LPB.l2r_leaf_writer u#0 sg)
  (destr: dep_enum_destr _ (l2r_leaf_write_dsum_cases_t t f sf g sg))
: LPB.l2r_leaf_writer u#0 #(dsum_type t) #(parse_dsum_kind kt t f k') #(parse_dsum t p f g) (serialize_dsum t s f sf g sg)
= (x: dsum_type t) (out: slice byte) (offset: SZ.t) (#v: Ghost.erased bytes)
{
  let tg = dsum_tag_of_data t x;
  l2r_leaf_write_dsum_pre_tag_lemma t s f sf g sg x offset v ();
  let off1 = w_tag tg out offset;
  with v1 . assert (pts_to out v1);
  l2r_leaf_write_dsum_pre_case_lemma t s f sf g sg x offset v off1 v1 ();
  let w_case = l2r_leaf_write_dsum_cases t f sf sf32 sg32 destr tg;
  let off2 = w_case x out off1;
  with v2 . assert (pts_to out v2);
  l2r_leaf_write_dsum_postcond_lemma t s f sf g sg x offset v off1 v1 off2 v2 ();
  off2
}

#pop-options
