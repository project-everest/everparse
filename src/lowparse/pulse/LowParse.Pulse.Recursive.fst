module LowParse.Pulse.Recursive
#lang-pulse
open LowParse.Spec.Base
include LowParse.Spec.Recursive
open Pulse.Lib.Slice.Util open Pulse.Lib.Trade open Pulse.Lib.Pervasives
open LowParse.Pulse.Base

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module L = LowParse.Pulse.VCList
module C = LowParse.Pulse.Combinators
module Trade = Pulse.Lib.Trade.Util

let validate_recursive_step_count_post
  (p: parse_recursive_param)
  (va: p.header)
  (bound: SZ.t)
  (rem rem' : SZ.t)
  (err: bool)
: Tot prop
= let count = p.count va in
  (err == true ==> count > SZ.v bound) /\
  SZ.v rem' == (if err then SZ.v rem else count)

inline_for_extraction
let validate_recursive_step_count
  (#p: parse_recursive_param u#0 u#0)
  (s: serialize_recursive_param p)
: Tot Type
=
    (#va: Ghost.erased p.header) ->
    (#pm: perm) ->
    (a: S.slice byte) ->
    (bound: SZ.t) ->
    (#rem: Ghost.erased SZ.t) ->
    (prem: R.ref SZ.t) ->
    stt bool
      (pts_to_serialized (serializer_of_tot_serializer s.serialize_header) a #pm va ** R.pts_to prem rem)
      (fun err -> pts_to_serialized (serializer_of_tot_serializer s.serialize_header) a #pm va ** (
        exists* rem' . R.pts_to prem rem' ** pure (
          validate_recursive_step_count_post p va bound rem rem' err
      )))

let parse_nlist_recursive_bound_correct
  (p: parse_recursive_param)
  (n: nat)
  (b: bytes)
: Lemma
  (Some? (parse (L.tot_parse_nlist n (parse_recursive p)) b) ==> n <= Seq.length b)
= match parse (L.tot_parse_nlist n (parse_recursive p)) b with
  | None -> ()
  | Some (_, consumed) ->
    parser_kind_prop_equiv (L.parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)) (L.tot_parse_nlist n (parse_recursive p));
    let open FStar.Mul in
    assert (consumed >= (L.parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)).parser_kind_low);
    assert (consumed >= n * p.parse_header_kind.parser_kind_low);
    FStar.Math.Lemmas.lemma_mult_le_right n 1 p.parse_header_kind.parser_kind_low

#restart-solver

let validate_tot_nlist_recursive_progress
  (p: parse_recursive_param)
  (v: bytes)
  (n: nat)
  (off: nat)
  (off': nat)
: Lemma
  (requires (
    off <= Seq.length v /\
    n > 0 /\
    begin match parse_consume p.parse_header (Seq.slice v off (Seq.length v)) with
    | None -> False
    | Some consumed -> off' == off + consumed
    end
  ))
  (ensures (
    off <= off' /\
    off' <= Seq.length v /\
    n > 0 /\
    begin match parse p.parse_header (Seq.slice v off (Seq.length v)) with
    | Some (h, _) ->
      let pr = parse_consume (L.tot_parse_nlist n (parse_recursive p)) (Seq.slice v (off) (Seq.length v)) in
      let n' = (n - 1) + p.count h in
      let pr' = parse_consume (L.tot_parse_nlist n' (parse_recursive p)) (Seq.slice v (off') (Seq.length v)) in
      (Some? pr == Some? pr') /\
      (Some? pr ==> off + Some?.v pr == off' + Some?.v pr')
    end
  ))
= parse_consume_nlist_recursive_eq' p n (Seq.slice v off (Seq.length v))

#push-options "--z3rlimit 32"

#restart-solver

let validate_tot_nlist_recursive_overflow
  (p: parse_recursive_param)
  (v: bytes)
  (n: nat)
  (off: nat)
: Lemma
  (requires (
    off <= Seq.length v /\
    n > 0 /\
    begin match parse p.parse_header (Seq.slice v off (Seq.length v)) with
    | Some (h, _) ->
      let bound = (Seq.length v - off) - n in
      p.count h > bound
    | None -> False
    end
  ))
  (ensures (
    off <= Seq.length v /\
    None? (parse_consume (L.tot_parse_nlist n (parse_recursive p)) (Seq.slice v off (Seq.length v)))
  ))
=
  parser_kind_prop_equiv p.parse_header_kind p.parse_header;
  parse_consume_nlist_recursive_eq' p n (Seq.slice v off (Seq.length v));
  parse_nlist_recursive_bound_correct p (n) (Seq.slice v (off) (Seq.length v));
  let Some (h, consumed) = parse p.parse_header (Seq.slice v off (Seq.length v)) in
  let offset = off + consumed in
  parse_nlist_recursive_bound_correct p (p.count h + (n - 1)) (Seq.slice v (offset) (Seq.length v))

#pop-options

#restart-solver

inline_for_extraction
fn validate_tot_nlist_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (w: validator (parser_of_tot_parser p.parse_header))
  (f: validate_recursive_step_count s)
  (n0: SZ.t)
: validator #(L.nlist (SZ.v n0) p.t) #(L.parse_nlist_kind (SZ.v n0) (parse_recursive_kind p.parse_header_kind)) (L.tot_parse_nlist (SZ.v n0) (parse_recursive p))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset0: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  let mut pn = n0;
  let mut pres = true;
  while (
    let res = !pres;
    let n = !pn;
    (res && (SZ.gt n 0sz))
  ) invariant b . exists* res n offset .
    pts_to pres res **
    pts_to pn n **
    pts_to poffset offset **
    pts_to input #pm v **
    pure (
      SZ.v offset <= Seq.length v /\
      b == (res && (SZ.gt n 0sz)) /\ (
        let pr0 = parse_consume (L.tot_parse_nlist (SZ.v n0) (parse_recursive p)) (Seq.slice v (SZ.v offset0) (Seq.length v)) in
        let pr = parse_consume (L.tot_parse_nlist (SZ.v n) (parse_recursive p)) (Seq.slice v (SZ.v offset) (Seq.length v)) in
        Some? pr0 == (res && Some? pr) /\
        (Some? pr0 ==> (SZ.v offset0 + Some?.v pr0 == SZ.v offset + Some?.v pr))
    ))
  {
    let off = !poffset;
    let n = !pn;
    let pr0 = Ghost.hide (parse_consume (L.tot_parse_nlist (SZ.v n0) (parse_recursive p)) (Seq.slice v (SZ.v offset0) (Seq.length v)));
    let pr = Ghost.hide (parse_consume (L.tot_parse_nlist (SZ.v n) (parse_recursive p)) (Seq.slice v (SZ.v off) (Seq.length v)));
    assert (pure (Some? pr0 == (Some? pr)));
    assert (pure (Some? pr0 ==> (SZ.v offset0 + Some?.v pr0 == SZ.v off + Some?.v pr)));
    parse_consume_nlist_recursive_eq' p (SZ.v n) (Seq.slice v (SZ.v off) (Seq.length v));
    parse_nlist_recursive_bound_correct p (SZ.v n) (Seq.slice v (SZ.v off) (Seq.length v));
    if SZ.gt n (SZ.sub (S.len input) off) {
      pres := false;
    } else {
      let res1 = w input poffset;
      if not res1 {
        pres := false;
      } else {
        let offset = !poffset;
        let input1 = peek_trade_gen (serializer_of_tot_serializer s.serialize_header) input off offset;
        parser_kind_prop_equiv p.parse_header_kind p.parse_header;
        with gv . assert (pts_to_serialized (serializer_of_tot_serializer s.serialize_header) input1 #pm gv);
        parse_nlist_recursive_bound_correct p (p.count gv + (SZ.v n - 1)) (Seq.slice v (SZ.v offset) (Seq.length v));
        let bound = SZ.sub (SZ.sub (S.len input) off) n;
        let res2 = f #gv #pm input1 bound pn;
        elim_trade _ _;
        let count = !pn;
        if (res2 || SZ.gt count bound) {
          validate_tot_nlist_recursive_overflow p v (SZ.v n) (SZ.v off);
          pres := false
        } else {
          validate_tot_nlist_recursive_progress p v (SZ.v n) (SZ.v off) (SZ.v offset);
          let n' : SZ.t = SZ.add (SZ.sub n 1sz) count;
          pn := n';
          let pr' = Ghost.hide (parse_consume (L.tot_parse_nlist (SZ.v n') (parse_recursive p)) (Seq.slice v (SZ.v offset) (Seq.length v)));
          assert (pure (Some? pr0 == (Some? pr')));
          assert (pure (Some? pr0 ==> (SZ.v offset0 + Some?.v pr0 == SZ.v offset + Some?.v pr')));
        }
      }
    }
  } ;
  !pres
}

inline_for_extraction
fn validate_nlist_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (w: validator (parser_of_tot_parser p.parse_header))
  (f: validate_recursive_step_count s)
  (n0: SZ.t)
: validator #(L.nlist (SZ.v n0) p.t) #(L.parse_nlist_kind (SZ.v n0) (parse_recursive_kind p.parse_header_kind)) (L.parse_nlist (SZ.v n0) (parser_of_tot_parser (parse_recursive p)))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset0: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  L.tot_parse_nlist_parse_nlist (SZ.v n0) (parse_recursive p) (Seq.slice (Ghost.reveal v) (SZ.v offset0) (Seq.length (Ghost.reveal v)));
  validate_tot_nlist_recursive s w f n0 input poffset
}

inline_for_extraction
fn validate_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (w: validator (parser_of_tot_parser p.parse_header))
  (f: validate_recursive_step_count s)
: validator #p.t #(parse_recursive_kind p.parse_header_kind) (parse_recursive p)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  L.parse_nlist_eq 1 (parser_of_tot_parser (parse_recursive p)) (Seq.slice v (SZ.v offset) (Seq.length v));
  Classical.forall_intro (L.parse_nlist_eq 0 (parser_of_tot_parser (parse_recursive p)));
  validate_nlist_recursive s w f 1sz input poffset
}

inline_for_extraction
let jump_recursive_step_count
  (#p: parse_recursive_param u#0 u#0)
  (s: serialize_recursive_param p)
: Tot Type
=
    (#va: Ghost.erased p.header) ->
    (#pm: perm) ->
    (a: S.slice byte) ->
    (bound: SZ.t) ->
    stt SZ.t
      (pts_to_serialized (serializer_of_tot_serializer s.serialize_header) a #pm va ** pure (p.count va <= SZ.v bound))
      (fun res -> pts_to_serialized (serializer_of_tot_serializer s.serialize_header) a #pm va ** pure (p.count va == SZ.v res))

#push-options "--z3rlimit 32"

#restart-solver
inline_for_extraction
fn jump_tot_nlist_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (w: jumper (parser_of_tot_parser p.parse_header))
  (f: jump_recursive_step_count s)
  (n0: SZ.t)
: jumper #(L.nlist (SZ.v n0) p.t) #(L.parse_nlist_kind (SZ.v n0) (parse_recursive_kind p.parse_header_kind)) (L.tot_parse_nlist (SZ.v n0) (parse_recursive p))
=
  (input: S.slice byte)
  (offset0: R.ref SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  let mut poffset = offset0;
  let mut pn = n0;
  while (
    let n = !pn;
    (SZ.gt n 0sz)
  ) invariant b . exists* n offset .
    pts_to pn n **
    pts_to poffset offset **
    pts_to input #pm v **
    pure (
      SZ.v offset <= Seq.length v /\
      b == (SZ.gt n 0sz) /\ (
        let pr0 = parse_consume (L.tot_parse_nlist (SZ.v n0) (parse_recursive p)) (Seq.slice v (SZ.v offset0) (Seq.length v)) in
        let pr = parse_consume (L.tot_parse_nlist (SZ.v n) (parse_recursive p)) (Seq.slice v (SZ.v offset) (Seq.length v)) in
        Some? pr0 /\ Some? pr /\
        (SZ.v offset0 + Some?.v pr0 == SZ.v offset + Some?.v pr)
    ))
  {
    with gn . assert (pts_to pn gn);
    with goffset . assert (pts_to poffset goffset);
    parse_consume_nlist_recursive_eq' p (SZ.v gn) (Seq.slice v (SZ.v goffset) (Seq.length v));
    let off = !poffset;
    let off1 = w input off;
    poffset := off1;
    let input1 = peek_trade_gen (serializer_of_tot_serializer s.serialize_header) input off off1;
    with gv . assert (pts_to_serialized (serializer_of_tot_serializer s.serialize_header) input1 #pm gv);
    parse_nlist_recursive_bound_correct p (p.count gv + (SZ.v gn - 1)) (Seq.slice v (SZ.v off1) (Seq.length v));
    let n = !pn;
    let count = f #gv #pm input1 (SZ.sub (S.len input) off1);
    elim_trade _ _;
    pn := SZ.add (SZ.sub n 1sz) count;
  } ;
  !poffset
}

#pop-options

#restart-solver
inline_for_extraction
fn jump_nlist_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (w: jumper (parser_of_tot_parser p.parse_header))
  (f: jump_recursive_step_count s)
  (n0: SZ.t)
: jumper #(L.nlist (SZ.v n0) p.t) #(L.parse_nlist_kind (SZ.v n0) (parse_recursive_kind p.parse_header_kind)) (L.parse_nlist (SZ.v n0) (parser_of_tot_parser (parse_recursive p)))
=
  (input: S.slice byte)
  (offset0: R.ref SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  L.tot_parse_nlist_parse_nlist (SZ.v n0) (parse_recursive p) (Seq.slice (Ghost.reveal v) (SZ.v offset0) (Seq.length (Ghost.reveal v)));
  jump_tot_nlist_recursive s w f n0 input offset0
}

inline_for_extraction
fn jump_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (w: jumper (parser_of_tot_parser p.parse_header))
  (f: jump_recursive_step_count s)
: jumper #p.t #(parse_recursive_kind p.parse_header_kind) (parse_recursive p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  L.parse_nlist_eq 1 (parser_of_tot_parser (parse_recursive p)) (Seq.slice v (SZ.v offset) (Seq.length v));
  Classical.forall_intro (L.parse_nlist_eq 0 (parser_of_tot_parser (parse_recursive p)));
  jump_nlist_recursive s w f 1sz input offset
}

inline_for_extraction
let impl_pred_t
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (base: (p.t -> bool))
: Tot Type
=
  (a: S.slice byte) ->
  (n: SZ.t) ->
  (#pm: perm) ->
  (#va: Ghost.erased (L.nlist (SZ.v n) p.t)) ->
  stt bool
    (pts_to_serialized (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s))) a #pm va ** pure (SZ.v n > 0))
    (fun res -> pts_to_serialized (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s))) a #pm va ** pure (SZ.v n > 0 /\ res == base (List.Tot.hd va)))

let parse_nlist_recursive_cons_payload_t
  (p: parse_recursive_param)
  (n: pos)
  (h: p.header)
: Tot Type
= L.nlist (p.count h) p.t & L.nlist (n - 1) p.t

let parse_nlist_recursive_cons_payload
  (p: parse_recursive_param)
  (n: pos)
  (h: p.header)
: Tot (parser _ (parse_nlist_recursive_cons_payload_t p n h))
= L.weaken parse_recursive_payload_kind
    (L.parse_nlist (p.count h) (parser_of_tot_parser (parse_recursive p)) `C.nondep_then`
    L.parse_nlist (n - 1) (parser_of_tot_parser (parse_recursive p)))

let synth_nlist_recursive_cons
  (p: parse_recursive_param)
  (n: pos)
  (hcrem: dtuple2 p.header (parse_nlist_recursive_cons_payload_t p n))
: Tot (L.nlist n p.t)
= match hcrem with
  (| h, (c, rem) |) -> p.synth_ (| h, c |) :: rem

let synth_nlist_recursive_cons_injective
  (p: parse_recursive_param)
  (n: pos)
: Lemma
  (C.synth_injective (synth_nlist_recursive_cons p n))
= ()

let parse_nlist_recursive_cons
  (p: parse_recursive_param)
  (n: pos)
: Tot (parser _ (L.nlist n p.t))
= (parser_of_tot_parser p.parse_header `C.parse_dtuple2` (parse_nlist_recursive_cons_payload p n))
    `L.parse_synth` synth_nlist_recursive_cons p n

let tot_nondep_then_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: tot_parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: tot_parser k2 t2)
  (b: bytes)
: Lemma
  (parse (C.tot_nondep_then p1 p2) b == (match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse p2 b' with
    | Some (x2, consumed2) ->
      Some ((x1, x2), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  ))
= C.nondep_then_eq #k1 p1 #k2 p2 b

#push-options "--z3rlimit 32"

#restart-solver

let parse_nlist_recursive_cons_eq
  (p: parse_recursive_param)
  (n: pos)
  (b: bytes)
: Lemma
  (ensures (parse (parse_nlist_recursive_cons p n) b == parse (L.parse_nlist n (parser_of_tot_parser (parse_recursive p))) b))
  [SMTPat (parse (parse_nlist_recursive_cons p n) b)]
= L.parse_nlist_eq n (parser_of_tot_parser (parse_recursive p)) b;
  parse_recursive_eq p b;
  L.tot_parse_synth_eq (parse_recursive_alt p (parse_recursive p)) p.synth_ b;
  L.parse_synth_eq (C.parse_dtuple2 (parser_of_tot_parser p.parse_header) (parse_nlist_recursive_cons_payload p n)) (synth_nlist_recursive_cons p n) b;
  C.parse_dtuple2_eq (parser_of_tot_parser p.parse_header) (parse_nlist_recursive_cons_payload p n) b;
  match parse p.parse_header b with
  | None -> ()
  | Some (h, consumed) ->
    let b' = Seq.slice b consumed (Seq.length b) in
    C.nondep_then_eq (L.parse_nlist (p.count h) (parser_of_tot_parser (parse_recursive p))) (L.parse_nlist (n - 1) (parser_of_tot_parser (parse_recursive p))) b';
    L.tot_parse_nlist_parse_nlist (p.count h) (parse_recursive p) b'

#pop-options

let synth_nlist_recursive_cons_recip
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: pos)
  (l: L.nlist n p.t)
: Tot (dtuple2 p.header (parse_nlist_recursive_cons_payload_t p n))
= let a :: q = l in
  let (| h, c |) = s.synth_recip a in
  (| h, (c, q) |)

let synth_nlist_recursive_cons_recip_inverse
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: pos)
: Lemma
  (C.synth_inverse (synth_nlist_recursive_cons p n) (synth_nlist_recursive_cons_recip s n))
= ()

let serialize_nlist_recursive_cons_payload
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: pos)
  (h: p.header)
: Tot (serializer (parse_nlist_recursive_cons_payload p n h))
= L.serialize_weaken
    parse_recursive_payload_kind
    (L.serialize_nlist (p.count h) (serialize_recursive s) `C.serialize_nondep_then`
    L.serialize_nlist (n - 1) (serialize_recursive s))

let serialize_nlist_recursive_cons
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: pos)
: Tot (serializer (parse_nlist_recursive_cons p n))
= C.serialize_synth
    _
    (synth_nlist_recursive_cons p n)
    (C.serialize_dtuple2
      s.serialize_header
      (serialize_nlist_recursive_cons_payload s n)
    )
    (synth_nlist_recursive_cons_recip s n)
    ()

let synth_nlist_append
  (t: Type)
  (n1 n2: nat)
  (l: (L.nlist n1 t & L.nlist n2 t))
: Tot (L.nlist (n1 + n2) t)
= List.Tot.append_length (fst l) (snd l);
  List.Tot.append (fst l) (snd l)

let synth_nlist_append_injective
  (t: Type)
  (n1 n2: nat)
: Lemma
  (ensures (C.synth_injective (synth_nlist_append t n1 n2)))
  [SMTPat (synth_nlist_append t n1 n2)]
= C.synth_injective_intro' #(L.nlist n1 t & L.nlist n2 t) #(L.nlist (n1 + n2) t) (synth_nlist_append t n1 n2) (fun x1 x2 ->
    List.Tot.append_length_inv_head
      (fst x1) (snd x1)
      (fst x2) (snd x2)
  )

let parse_recursive_cons_payload_eq_nlist
  (p: parse_recursive_param)
  (n: pos)
  (h: p.header)
  (b: bytes)
: Lemma
  (parse (C.parse_synth (parse_nlist_recursive_cons_payload p n h) (synth_nlist_append p.t (p.count h) (n - 1))) b ==
    parse (L.parse_nlist (p.count h + (n - 1)) (parser_of_tot_parser (parse_recursive p))) b
  )
= C.parse_synth_eq
    (parse_nlist_recursive_cons_payload p n h)
    (synth_nlist_append p.t (p.count h) (n - 1))
    b;
  C.nondep_then_eq
    (L.parse_nlist (p.count h) (parser_of_tot_parser (parse_recursive p)))
    (L.parse_nlist (n - 1) (parser_of_tot_parser (parse_recursive p)))
    b;
  L.parse_nlist_sum (parser_of_tot_parser (parse_recursive p)) (p.count h) (n - 1) b

let rec synth_nlist_append_recip
  (t: Type)
  (n1 n2: nat)
  (l: L.nlist (n1 + n2) t)
: Tot (L.nlist n1 t & L.nlist n2 t)
  (decreases n1)
= if n1 = 0
  then ([], l)
  else
    let a :: q = l in
    let (l1, l2) = synth_nlist_append_recip t (n1 - 1) n2 q in
    (a :: l1, l2)

let rec synth_nlist_append_recip_inverse
  (t: Type)
  (n1 n2: nat)
: Lemma
  (ensures (C.synth_inverse (synth_nlist_append t n1 n2) (synth_nlist_append_recip t n1 n2)))
  (decreases n1)
  [SMTPat (synth_nlist_append_recip t n1 n2)]
= C.synth_inverse_intro' #(L.nlist n1 t & L.nlist n2 t) #(L.nlist (n1 + n2) t) (synth_nlist_append t n1 n2) (synth_nlist_append_recip t n1 n2) (fun l ->
    if n1 = 0
    then ()
    else begin
      let a :: q = l in
      synth_nlist_append_recip_inverse t (n1 - 1) n2;
      assert (synth_nlist_append t (n1 - 1) n2 (synth_nlist_append_recip t (n1 - 1) n2 q) == q)
    end
  )

let parse_nlist_recursive_bound_correct'
  (p: parse_recursive_param)
  (n: nat)
  (b: bytes)
: Lemma
  (Some? (parse (L.parse_nlist n (parser_of_tot_parser (parse_recursive p))) b) ==> n <= Seq.length b)
= L.tot_parse_nlist_parse_nlist n (parse_recursive p) b;
  parse_nlist_recursive_bound_correct p n b

let serialize_recursive_bound_correct
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (count: nat)
  (c: L.nlist count p.t)
: Lemma
  (count <= Seq.length (L.serialize_nlist count (serializer_of_tot_serializer (serialize_recursive s)) c))
= parse_nlist_recursive_bound_correct' p count (L.serialize_nlist count (serializer_of_tot_serializer (serialize_recursive s)) c)

inline_for_extraction
fn impl_nlist_forall_pred_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (j: jumper (parser_of_tot_parser p.parse_header))
  (f: jump_recursive_step_count s)
  (pr: pred_recursive_t s)
  (g: impl_pred_t s pr.base)
  (n0: SZ.t)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (L.nlist (SZ.v n0) p.t))
  requires pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v
  returns res: bool
  ensures pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v ** pure (res == List.Tot.for_all pr.pred v)
{
  let mut pn = n0;
  let mut pres = true;
  let mut ppi = input;
  Trade.refl (pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v);
  while (
    let res = !pres;
    let n = !pn;
    (res && (SZ.gt n 0sz))
  ) invariant b . exists* res n pi vi . (
    pts_to pres res **
    pts_to pn n **
    pts_to ppi pi **
    pts_to_serialized (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s))) pi #pm vi **
    trade (pts_to_serialized (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s))) pi #pm vi)
      (pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v
    ) **
    pure (
      b == (res && (SZ.v n > 0)) /\
      List.Tot.for_all pr.pred v == (res && List.Tot.for_all pr.pred vi)
  )) {
    let n = !pn;
    with pi'. assert pts_to ppi pi';
    let pi = !ppi;
    rewrite each pi' as pi;
    with vi . assert (pts_to_serialized (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s))) pi #pm vi);
    pr.prf (List.Tot.hd vi);
    let res = g pi n;
    if not res {
      pres := false
    } else {
      pts_to_serialized_ext_trade
        (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s)))
        (serialize_nlist_recursive_cons s (SZ.v n))
        pi;
      Trade.trans
        _
        (pts_to_serialized (L.serialize_nlist (SZ.v n) (serializer_of_tot_serializer (serialize_recursive s))) pi #pm vi)
        _;
      C.pts_to_serialized_synth_l2r_trade
        (C.serialize_dtuple2
          (serializer_of_tot_serializer s.serialize_header)
          (serialize_nlist_recursive_cons_payload s (SZ.v n))
        )
        (synth_nlist_recursive_cons p (SZ.v n))
        (synth_nlist_recursive_cons_recip s (SZ.v n))
        pi;
      Trade.trans
        _ _
        (pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v);
      with vi . assert (
        pts_to_serialized
          (C.serialize_dtuple2
            (serializer_of_tot_serializer s.serialize_header)
            (serialize_nlist_recursive_cons_payload s (SZ.v n))
          )
          pi #pm vi
      );
      let ph, pc = C.split_dtuple2
        (serializer_of_tot_serializer s.serialize_header)
        j
        (serialize_nlist_recursive_cons_payload s (SZ.v n))
        pi;
      unfold (C.split_dtuple2_post (serializer_of_tot_serializer s.serialize_header) (serialize_nlist_recursive_cons_payload s (SZ.v n)) pi pm vi (ph, pc));
      unfold (C.split_dtuple2_post' (serializer_of_tot_serializer s.serialize_header) (serialize_nlist_recursive_cons_payload s (SZ.v n)) pi pm vi ph pc);
      Trade.trans
        _ _
        (pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v);
      with h c . assert (pts_to_serialized (serializer_of_tot_serializer s.serialize_header) ph #pm h ** pts_to_serialized (serialize_nlist_recursive_cons_payload s (SZ.v n) h) pc #pm c);
      List.Tot.for_all_append pr.pred (fst c) (snd c);
      synth_nlist_append_recip_inverse p.t (p.count h) (SZ.v n - 1); // FIXME: WHY WHY WHY does this pattern not trigger?
      C.pts_to_serialized_synth_trade
        (serialize_nlist_recursive_cons_payload s (SZ.v n) h)
        (synth_nlist_append p.t (p.count h) (SZ.v n - 1))
        (synth_nlist_append_recip p.t (p.count h) (SZ.v n - 1))
        pc;
      Classical.forall_intro (parse_recursive_cons_payload_eq_nlist p (SZ.v n) h);
      C.pts_to_serialized_ext_trade
        (C.serialize_synth
          _
          (synth_nlist_append p.t (p.count h) (SZ.v n - 1))
          (serialize_nlist_recursive_cons_payload s (SZ.v n) h)
          (synth_nlist_append_recip p.t (p.count h) (SZ.v n - 1))
          ()
        )
        (L.serialize_nlist (p.count h + (SZ.v n - 1)) (serializer_of_tot_serializer (serialize_recursive s)))
        pc;
      with c' . assert (pts_to_serialized (L.serialize_nlist (p.count h + (SZ.v n - 1)) (serializer_of_tot_serializer (serialize_recursive s))) pc #pm c');
      pts_to_serialized_length
        (L.serialize_nlist (p.count h + (SZ.v n - 1)) (serializer_of_tot_serializer (serialize_recursive s)))
        pc;
      serialize_recursive_bound_correct s (p.count h + (SZ.v n - 1)) c';
      let count = f ph (S.len pc);
      Trade.elim_hyp_l _ _ _;
      Trade.trans
        _ _
        (pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v);
      Trade.trans
        _ _
        (pts_to_serialized (L.serialize_nlist (SZ.v n0) (serializer_of_tot_serializer (serialize_recursive s))) input #pm v);
      pn := SZ.add (SZ.sub n 1sz) count;
      ppi := pc;
    }
  };
  elim_trade _ _;
  !pres
}

inline_for_extraction
fn impl_pred_recursive
  (#p: Ghost.erased parse_recursive_param)
  (s: Ghost.erased (serialize_recursive_param p))
  (j: jumper (parser_of_tot_parser p.parse_header))
  (f: jump_recursive_step_count s)
  (pr: pred_recursive_t s)
  (g: impl_pred_t s pr.base)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased p.t)
  requires pts_to_serialized (serializer_of_tot_serializer (serialize_recursive s)) input #pm v
  returns res: bool
  ensures pts_to_serialized (serializer_of_tot_serializer (serialize_recursive s)) input #pm v ** pure (res == pr.pred v)
{
  L.pts_to_serialized_nlist_1 (serializer_of_tot_serializer (serialize_recursive s)) input;
  let res = impl_nlist_forall_pred_recursive s j f pr g 1sz input;
  elim_trade _ _;
  res
}
