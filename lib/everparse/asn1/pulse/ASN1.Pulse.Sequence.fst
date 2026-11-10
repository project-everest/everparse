module ASN1.Pulse.Sequence
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module T = LowParse.Tot.Combinators
module TD = LowParse.Tot.Defaultable
module SD = LowParse.Spec.Defaultable
module I = ASN1.Pulse.Identifier
module VR = LowParse.PulseParse.VReader

(* Validators only depend on whether a parser succeeds and how many bytes it
   consumes, not on the value it returns. *)

let consumed (#k: parser_kind) (#t: Type) (p: SB.parser k t) (b: bytes) : GTot (option nat) =
  match SB.parse p b with
  | None -> None
  | Some (_, c) -> Some c

let consumed_ext_prop (#k1: parser_kind) (#t1: Type) (p1: SB.parser k1 t1) (#k2: parser_kind) (#t2: Type) (p2: SB.parser k2 t2) : prop =
  forall b . consumed p1 b == consumed p2 b

inline_for_extraction
fn validate_ext_consumed
  (#t1: Type0) (#k1: Ghost.erased parser_kind) (#p1: SB.parser k1 t1) (v1: LPS.validator p1)
  (#t2: Type0) (#k2: Ghost.erased parser_kind) (p2: SB.parser k2 t2 { consumed_ext_prop p1 p2 })
: LPS.validator #t2 #k2 p2
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  assert (pure (consumed p1 sinput == consumed p2 sinput));
  v1 input poffset
}

(* Components of a sequence item *)

let item_set (item: gen_decorated_parser_twin) : Tot (Set.set asn1_id_t) =
  match item with
  | Mkgendcparser d _ _ -> let (| s, _, _ |) = d in s

let item_dec (item: gen_decorated_parser_twin) : Tot asn1_decorator =
  match item with
  | Mkgendcparser d _ _ -> let (| _, de, _ |) = d in de

let seq_p (items: list gen_decorated_parser_twin) (st: option asn1_id_t)
: Tot (asn1_weak_parser (asn1_sequence_t (List.Tot.map (Mkgendcparser?.d) items)))
= make_asn1_sequence_parser' items st

(* Unfolding lemmas for `make_asn1_sequence_parser'` *)

let seq_nil_none (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (seq_p [] None) b == Some 0)
= ()

let seq_nil_some (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (seq_p [] (Some id)) b == None)
= ()

let seq_cons_some_body
  (items: list gen_decorated_parser_twin { Cons? items })
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (SB.parse (seq_p items (Some id)) b == SB.parse (make_asn1_sequence_parser_body_twin items make_asn1_sequence_parser' id) b)
= let pt = make_asn1_sequence_parser_body_twin items make_asn1_sequence_parser' in
  make_asn1_sequence_parser_body_twin_and_then_cases_injective items make_asn1_sequence_parser';
  let p'' = make_asn1_sequence_parser_body pt (Some id) in
  assert (seq_p items (Some id) == make_asn1_sequence_parser_guard items make_asn1_sequence_parser'' (Some id));
  assert (make_asn1_sequence_parser'' items (Some id) == make_asn1_sequence_parser_body (make_asn1_sequence_parser_body_twin items make_asn1_sequence_parser') (Some id)) by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser'']; zeta; iota]; FStar.Tactics.trefl ());
  TD.defaultable_trivial_eq p'';
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  T.and_then_eq (weaken k (T.parse_ret id)) pt b

let seq_cons_none
  (items: list gen_decorated_parser_twin { Cons? items })
  (b: bytes)
: Lemma
  (consumed #asn1_weak_parser_kind (seq_p items None) b == (
    if Some? (generate_defaultable_items items) && Seq.length b = 0
    then Some 0
    else match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, c1) ->
      match consumed #asn1_weak_parser_kind (seq_p items (Some id)) (Seq.slice b c1 (Seq.length b)) with
      | None -> None
      | Some c2 -> Some (c1 + c2)
  ))
= let pt = make_asn1_sequence_parser_body_twin items make_asn1_sequence_parser' in
  make_asn1_sequence_parser_body_twin_and_then_cases_injective items make_asn1_sequence_parser';
  let p'' = make_asn1_sequence_parser_body pt None in
  assert (seq_p items None == make_asn1_sequence_parser_guard items make_asn1_sequence_parser'' None);
  assert (make_asn1_sequence_parser'' items None == make_asn1_sequence_parser_body (make_asn1_sequence_parser_body_twin items make_asn1_sequence_parser') None) by (FStar.Tactics.norm [delta_only [`%make_asn1_sequence_parser'']; zeta; iota]; FStar.Tactics.trefl ());
  SD.parse_defaultable_eq #asn1_weak_parser_kind (generate_defaultable_items items) p'' b;
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  T.and_then_eq (weaken k parse_asn1_identifier_U32) pt b;
  match SB.parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) -> seq_cons_some_body items id (Seq.slice b c1 (Seq.length b))

let seq_single_some
  (hd: gen_decorated_parser_twin)
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (consumed #asn1_weak_parser_kind (seq_p [hd] (Some id)) b == consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b)
= seq_cons_some_body [hd] id b

let seq_cons_cons_some
  (hd: gen_decorated_parser_twin)
  (tl: list gen_decorated_parser_twin { Cons? tl })
  (id: asn1_id_t)
  (b: bytes)
: Lemma
  (consumed #asn1_weak_parser_kind (seq_p (hd :: tl) (Some id)) b == (
    if Set.mem id (item_set hd)
    then match consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b with
      | None -> None
      | Some c1 ->
        match consumed #asn1_weak_parser_kind (seq_p tl None) (Seq.slice b c1 (Seq.length b)) with
        | None -> None
        | Some c2 -> Some (c1 + c2)
    else if PLAIN? (item_dec hd)
    then None
    else consumed #asn1_weak_parser_kind (seq_p tl (Some id)) b
  ))
= seq_cons_some_body (hd :: tl) id b;
  match hd with
  | Mkgendcparser d p fp ->
    let (| s, de, dk |) = d in
    if Set.mem id s
    then T.nondep_then_eq (parse_asn1_sequence_item_twin hd id) (seq_p tl None) b
    else match de with
    | PLAIN -> T.nondep_then_eq (T.fail_parser asn1_strong_parser_kind (asn1_decorated_t d)) (seq_p tl None) b
    | _ ->
      let Some defv = generate_defaultable_item hd in
      T.nondep_then_eq (weaken asn1_strong_parser_kind (T.parse_ret defv)) (seq_p tl (Some id)) b

(* Validators.

   The pending identifier `st` of the spec (`make_asn1_sequence_parser'`) is
   a *runtime* argument, so that every item of a sequence is validated by a
   single piece of code. (Following the spec's case split statically, with
   one validator for `st = None` and one per `st = Some id`, duplicates the
   tail of the sequence at every OPTIONAL item: the code size is then
   exponential in the number of OPTIONAL items.) *)

inline_for_extraction
fn validate_seq_nil (st: option asn1_id_t)
: LPS.validator #_ #asn1_weak_parser_kind (seq_p [] st)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  match st {
    None -> {
      seq_nil_none (Seq.slice v (SZ.v offset) (Seq.length v));
      true
    }
    Some id -> {
      seq_nil_some id (Seq.slice v (SZ.v offset) (Seq.length v));
      false
    }
  }
}

let pending_id_postcond (st: option asn1_id_t) (offset: SZ.t) (v: bytes) (off: SZ.t) (res: option asn1_id_t) : GTot prop =
  match st with
  | Some id -> res == Some id /\ off == offset /\ SZ.v offset <= Seq.length v
  | None -> VR.vreader_postcond #asn1_strong_parser_kind parse_asn1_identifier_U32 offset v off res

(* The identifier of the next item: the pending one if any, else read it *)
inline_for_extraction
fn get_pending_id
  (st: option asn1_id_t)
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: option asn1_id_t
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (pending_id_postcond st offset v off res))
{
  match st {
    Some id -> {
      Some id
    }
    None -> {
      I.vread_identifier input poffset
    }
  }
}

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_seq_cons
  (items: Ghost.erased (list gen_decorated_parser_twin) { Cons? items })
  (alldef: bool { alldef == Some? (generate_defaultable_items items) })
  (vbody: (id: asn1_id_t) -> LPS.validator #_ #asn1_weak_parser_kind (seq_p items (Some id)))
  (st: option asn1_id_t)
: LPS.validator #_ #asn1_weak_parser_kind (seq_p items st)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  seq_cons_none items (Seq.slice v (SZ.v offset) (Seq.length v));
  let off = !poffset;
  pts_to_len input;
  if (None? st && alldef && off = S.len input) {
    true
  } else {
    let r = get_pending_id st input poffset;
    match r {
      None -> {
        false
      }
      Some id -> {
        with off1 . assert (R.pts_to poffset off1);
        Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
        vbody id input poffset
      }
    }
  }
}

inline_for_extraction
let validate_seq_single_body
  (hd: Ghost.erased gen_decorated_parser_twin)
  (id: asn1_id_t)
  (vt: LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id))
: LPS.validator #_ #asn1_weak_parser_kind (seq_p [Ghost.reveal hd] (Some id))
= Classical.forall_intro (seq_single_some hd id);
  validate_ext_consumed vt (seq_p [Ghost.reveal hd] (Some id))

(* One item of a sequence with more items after it: on success, returns the
   pending identifier for the rest of the sequence *)
let item_step_postcond
  (hd: gen_decorated_parser_twin) (id: asn1_id_t)
  (offset: SZ.t) (v: bytes) (off: SZ.t) (res: option (option asn1_id_t))
: GTot prop
= SZ.v offset <= Seq.length v /\ SZ.v off <= Seq.length v /\ (
  let b = Seq.slice v (SZ.v offset) (Seq.length v) in
  if Set.mem id (item_set hd)
  then match consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b, res with
    | None, None -> True
    | Some c1, Some None -> SZ.v off == SZ.v offset + c1
    | _ -> False
  else if PLAIN? (item_dec hd)
  then res == None
  else res == Some (Some id) /\ off == offset
  )

inline_for_extraction
fn validate_seq_item_step
  (hd: Ghost.erased gen_decorated_parser_twin)
  (id: asn1_id_t)
  (mem: bool { mem == Set.mem id (item_set hd) })
  (plain: bool { plain == PLAIN? (item_dec hd) })
  (vt: LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id))
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: option (option asn1_id_t)
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (item_step_postcond hd id offset v off res))
{
  if mem {
    let ok = vt input poffset;
    if ok {
      Some None
    } else {
      None
    }
  } else if plain {
    None
  } else {
    Some (Some id)
  }
}

inline_for_extraction
fn validate_seq_cons_cons_body
  (hd: Ghost.erased gen_decorated_parser_twin)
  (tl: Ghost.erased (list gen_decorated_parser_twin) { Cons? tl })
  (id: asn1_id_t)
  (mem: bool { mem == Set.mem id (item_set hd) })
  (plain: bool { plain == PLAIN? (item_dec hd) })
  (vt: LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id))
  (vtail: (st: option asn1_id_t) -> LPS.validator #_ #asn1_weak_parser_kind (seq_p tl st))
: LPS.validator #_ #asn1_weak_parser_kind (seq_p (Ghost.reveal hd :: Ghost.reveal tl) (Some id))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  seq_cons_cons_some hd tl id (Seq.slice v (SZ.v offset) (Seq.length v));
  let r = validate_seq_item_step hd id mem plain vt input poffset;
  match r {
    None -> {
      false
    }
    Some st -> {
      with off1 . assert (R.pts_to poffset off1);
      Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
      vtail st input poffset
    }
  }
}

#pop-options

(* Item twins *)

let item_fp (item: gen_decorated_parser_twin) : Tot (asn1_id_t -> asn1_strong_parser (asn1_decorated_pure_t (Mkgendcparser?.d item))) =
  match item with
  | Mkgendcparser _ _ fp -> fp

let item_twin_plain_eq (item: gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (PLAIN? (item_dec item)))
  (ensures (consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin item id) b == consumed #asn1_strong_parser_kind (item_fp item id) b))
= ()

let item_twin_option_eq (item: gen_decorated_parser_twin) (id: asn1_id_t) (b: bytes)
: Lemma
  (requires (OPTION? (item_dec item)))
  (ensures (consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin item id) b == consumed #asn1_strong_parser_kind (item_fp item id) b))
= match item with
  | Mkgendcparser d _ fp ->
    T.parse_synth_eq (fp id) Some b

inline_for_extraction
let validate_item_twin_plain
  (item: Ghost.erased gen_decorated_parser_twin { PLAIN? (item_dec item) })
  (id: asn1_id_t)
  (v: LPS.validator #_ #asn1_strong_parser_kind (item_fp item id))
: LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin item id)
= Classical.forall_intro (Classical.move_requires (item_twin_plain_eq item id));
  validate_ext_consumed v (parse_asn1_sequence_item_twin item id)

inline_for_extraction
let validate_item_twin_option
  (item: Ghost.erased gen_decorated_parser_twin { OPTION? (item_dec item) })
  (id: asn1_id_t)
  (v: LPS.validator #_ #asn1_strong_parser_kind (item_fp item id))
: LPS.validator #_ #asn1_strong_parser_kind (parse_asn1_sequence_item_twin item id)
= Classical.forall_intro (Classical.move_requires (item_twin_option_eq item id));
  validate_ext_consumed v (parse_asn1_sequence_item_twin item id)
