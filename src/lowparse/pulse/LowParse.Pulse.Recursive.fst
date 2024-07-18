module LowParse.Pulse.Recursive
open LowParse.Spec.Base
include LowParse.Spec.Recursive
open LowParse.Pulse.Util
open LowParse.Pulse.Base

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module L = LowParse.Pulse.VCList
module C = LowParse.Pulse.Combinators

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
      (pts_to_serialized s.serialize_header a #pm va ** R.pts_to prem rem)
      (fun err -> pts_to_serialized s.serialize_header a #pm va ** (
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

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction
```pulse
fn validate_nlist_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (w: validator p.parse_header)
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
    S.pts_to input #pm v **
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
    parse_consume_nlist_recursive_eq' p (SZ.v n) (Seq.slice v (SZ.v off) (Seq.length v));
    parse_nlist_recursive_bound_correct p (SZ.v n) (Seq.slice v (SZ.v off) (Seq.length v));
    if SZ.gt n (SZ.sub (S.len input) off) {
      pres := false;
    } else {
      let res1 = w input poffset;
      if not res1 {
        pres := false;
      } else {
        let off1 = !poffset;
        let input1 = peek_stick_gen s.serialize_header input off off1;
        parser_kind_prop_equiv p.parse_header_kind p.parse_header;
        with gv . assert (pts_to_serialized s.serialize_header input1 #pm gv);
        parse_nlist_recursive_bound_correct p (p.count gv + (SZ.v n - 1)) (Seq.slice v (SZ.v off1) (Seq.length v));
        let bound = SZ.sub (SZ.sub (S.len input) off) n;
        let res2 = f #gv #pm input1 bound pn;
        elim_stick _ _;
        let count = !pn;
        if (res2 || SZ.gt count bound) {
          pres := false
        } else {
          pn := SZ.add (SZ.sub n 1sz) count;
        }
      }
    }
  } ;
  !pres
}
```

#pop-options

inline_for_extraction
```pulse
fn validate_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (w: validator p.parse_header)
  (f: validate_recursive_step_count s)
: validator #p.t #(parse_recursive_kind p.parse_header_kind) (parse_recursive p)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  L.tot_parse_nlist_eq 1 (parse_recursive p) (Seq.slice v (SZ.v offset) (Seq.length v));
  Classical.forall_intro (L.tot_parse_nlist_eq 0 (parse_recursive p));
  validate_nlist_recursive s w f 1sz input poffset
}
```

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
      (pts_to_serialized s.serialize_header a #pm va ** pure (p.count va <= SZ.v bound))
      (fun res -> pts_to_serialized s.serialize_header a #pm va ** pure (p.count va == SZ.v res))

#push-options "--z3rlimit 32"

#restart-solver
inline_for_extraction
```pulse
fn jump_nlist_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
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
    S.pts_to input #pm v **
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
    let input1 = peek_stick_gen s.serialize_header input off off1;
    with gv . assert (pts_to_serialized s.serialize_header input1 #pm gv);
    parse_nlist_recursive_bound_correct p (p.count gv + (SZ.v gn - 1)) (Seq.slice v (SZ.v off1) (Seq.length v));
    let n = !pn;
    let count = f #gv #pm input1 (SZ.sub (S.len input) off1);
    elim_stick _ _;
    pn := SZ.add (SZ.sub n 1sz) count;
  } ;
  !poffset
}
```

#pop-options

inline_for_extraction
```pulse
fn jump_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
  (f: jump_recursive_step_count s)
: jumper #p.t #(parse_recursive_kind p.parse_header_kind) (parse_recursive p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  L.tot_parse_nlist_eq 1 (parse_recursive p) (Seq.slice v (SZ.v offset) (Seq.length v));
  Classical.forall_intro (L.tot_parse_nlist_eq 0 (parse_recursive p));
  jump_nlist_recursive s w f 1sz input offset
}
```

inline_for_extraction
let impl_pred_t
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (base: Ghost.erased (t -> bool))
: Tot Type
=
  (a: S.slice byte) ->
  (#pm: perm) ->
  (#va: Ghost.erased t) ->
  stt bool
    (pts_to_serialized s a #pm va)
    (fun res -> pts_to_serialized s a #pm va ** pure (res == Ghost.reveal base va))

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
= L.tot_weaken parse_recursive_payload_kind
    (L.tot_parse_nlist (p.count h) (parse_recursive p) `C.tot_nondep_then`
    L.tot_parse_nlist (n - 1) (parse_recursive p))

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
= (p.parse_header `C.tot_parse_dtuple2` (parse_nlist_recursive_cons_payload p n))
    `L.tot_parse_synth` synth_nlist_recursive_cons p n

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
  (ensures (parse (parse_nlist_recursive_cons p n) b == parse (L.tot_parse_nlist n (parse_recursive p)) b))
  [SMTPat (parse (parse_nlist_recursive_cons p n) b)]
= L.tot_parse_nlist_eq n (parse_recursive p) b;
  parse_recursive_eq p b;
  L.tot_parse_synth_eq (parse_recursive_alt p (parse_recursive p)) p.synth_ b;
  L.tot_parse_synth_eq (C.tot_parse_dtuple2 p.parse_header (parse_nlist_recursive_cons_payload p n)) (synth_nlist_recursive_cons p n) b;
  match parse p.parse_header b with
  | None -> ()
  | Some (h, consumed) ->
    let b' = Seq.slice b consumed (Seq.length b) in
    tot_nondep_then_eq (L.tot_parse_nlist (p.count h) (parse_recursive p)) (L.tot_parse_nlist (n - 1) (parse_recursive p)) b';
    ()

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
= L.tot_serialize_weaken
    parse_recursive_payload_kind
    (L.tot_serialize_nlist (p.count h) (serialize_recursive s) `C.tot_serialize_nondep_then`
    L.tot_serialize_nlist (n - 1) (serialize_recursive s))

let serialize_nlist_recursive_cons
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n: pos)
: Tot (serializer (parse_nlist_recursive_cons p n))
= C.tot_serialize_synth
    _
    (synth_nlist_recursive_cons p n)
    (C.tot_serialize_dtuple2
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
  (parse (C.tot_parse_synth (parse_nlist_recursive_cons_payload p n h) (synth_nlist_append p.t (p.count h) (n - 1))) b ==
    parse (L.tot_parse_nlist (p.count h + (n - 1)) (parse_recursive p)) b
  )
= C.tot_parse_synth_eq
    (parse_nlist_recursive_cons_payload p n h)
    (synth_nlist_append p.t (p.count h) (n - 1))
    b;
  tot_nondep_then_eq
    (L.tot_parse_nlist (p.count h) (parse_recursive p))
    (L.tot_parse_nlist (n - 1) (parse_recursive p))
    b;
  tot_parse_nlist_sum (parse_recursive p) (p.count h) (n - 1) b

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

let serialize_recursive_bound_correct
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (count: nat)
  (c: L.nlist count p.t)
: Lemma
  (count <= Seq.length (L.tot_serialize_nlist count (serialize_recursive s) c))
= parse_nlist_recursive_bound_correct p count (L.tot_serialize_nlist count (serialize_recursive s) c)

inline_for_extraction
```pulse
fn impl_nlist_forall_pred_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (w: jumper (parse_recursive p)) // for code conciseness purposes
  (j: jumper p.parse_header)
  (f: jump_recursive_step_count s)
  (pr: pred_recursive_t s)
  (g: impl_pred_t (serialize_recursive s) pr.base)
  (n0: SZ.t)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (L.nlist (SZ.v n0) p.t))
  requires pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v
  returns res: bool
  ensures pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v ** pure (res == List.Tot.for_all pr.pred v)
{
  let mut pn = n0;
  let mut pres = true;
  let mut ppi = input;
  stick_id (pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v);
  while (
    let res = !pres;
    let n = !pn;
    (res && (SZ.gt n 0sz))
  ) invariant b . exists* res n pi vi . (
    pts_to pres res **
    pts_to pn n **
    pts_to ppi pi **
    pts_to_serialized (L.tot_serialize_nlist (SZ.v n) (serialize_recursive s)) pi #pm vi **
    (pts_to_serialized (L.tot_serialize_nlist (SZ.v n) (serialize_recursive s)) pi #pm vi @==>
      pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v
    ) **
    pure (
      b == (res && (SZ.v n > 0)) /\
      List.Tot.for_all pr.pred v == (res && List.Tot.for_all pr.pred vi)
  )) {
    let n = !pn;
    let pi = !ppi;
    with vi . assert (pts_to_serialized (L.tot_serialize_nlist (SZ.v n) (serialize_recursive s)) pi #pm vi);
    let px = L.nlist_hd (serialize_recursive s) w (SZ.v n) pi;
    pr.prf (List.Tot.hd vi);
    let res = g px;
    elim_stick (pts_to_serialized (serialize_recursive s) px #pm _) _;
    if not res {
      pres := false
    } else {
      pts_to_serialized_ext_stick
        (L.tot_serialize_nlist (SZ.v n) (serialize_recursive s))
        (serialize_nlist_recursive_cons s (SZ.v n))
        pi;
      stick_trans
        _
        (pts_to_serialized (L.tot_serialize_nlist (SZ.v n) (serialize_recursive s)) pi #pm vi)
        _;
      C.pts_to_serialized_synth_l2r_stick
        (C.tot_serialize_dtuple2
          s.serialize_header
          (serialize_nlist_recursive_cons_payload s (SZ.v n))
        )
        (synth_nlist_recursive_cons p (SZ.v n))
        (synth_nlist_recursive_cons_recip s (SZ.v n))
        pi;
      stick_trans
        _ _
        (pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v);
      with vi . assert (
        pts_to_serialized
          (C.tot_serialize_dtuple2
            s.serialize_header
            (serialize_nlist_recursive_cons_payload s (SZ.v n))
          )
          pi #pm vi
      );
      let spl = C.split_dtuple2
        s.serialize_header
        j
        (serialize_nlist_recursive_cons_payload s (SZ.v n))
        pi;
      match spl { S.SlicePair ph pc -> {
        unfold (C.split_dtuple2_post s.serialize_header (serialize_nlist_recursive_cons_payload s (SZ.v n)) pi pm vi spl);
        unfold (C.split_dtuple2_post' s.serialize_header (serialize_nlist_recursive_cons_payload s (SZ.v n)) pi pm vi ph pc);
        stick_trans
          _ _
          (pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v);
        with h c . assert (pts_to_serialized s.serialize_header ph #pm h ** pts_to_serialized (serialize_nlist_recursive_cons_payload s (SZ.v n) h) pc #pm c);
        List.Tot.for_all_append pr.pred (fst c) (snd c);
        synth_nlist_append_recip_inverse p.t (p.count h) (SZ.v n - 1); // FIXME: WHY WHY WHY does this pattern not trigger?
        C.pts_to_serialized_synth_stick
          (serialize_nlist_recursive_cons_payload s (SZ.v n) h)
          (synth_nlist_append p.t (p.count h) (SZ.v n - 1))
          (synth_nlist_append_recip p.t (p.count h) (SZ.v n - 1))
          pc;
        Classical.forall_intro (parse_recursive_cons_payload_eq_nlist p (SZ.v n) h);
        C.pts_to_serialized_ext_stick
          (L.tot_serialize_synth
            _
            (synth_nlist_append p.t (p.count h) (SZ.v n - 1))
            (serialize_nlist_recursive_cons_payload s (SZ.v n) h)
            (synth_nlist_append_recip p.t (p.count h) (SZ.v n - 1))
            ()
          )
          (L.tot_serialize_nlist (p.count h + (SZ.v n - 1)) (serialize_recursive s))
          pc;
        with c' . assert (pts_to_serialized (L.tot_serialize_nlist (p.count h + (SZ.v n - 1)) (serialize_recursive s)) pc #pm c');
        pts_to_serialized_length
          (L.tot_serialize_nlist (p.count h + (SZ.v n - 1)) (serialize_recursive s))
          pc;
        serialize_recursive_bound_correct s (p.count h + (SZ.v n - 1)) c';
        let count = f ph (S.len pc);
        stick_elim_partial_l _ _ _;
        stick_trans
          _ _
          (pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v);
        stick_trans
          _ _
          (pts_to_serialized (L.tot_serialize_nlist (SZ.v n0) (serialize_recursive s)) input #pm v);
        pn := SZ.add (SZ.sub n 1sz) count;
        ppi := pc;
      }}
    }
  };
  elim_stick _ _;
  !pres
}
```

inline_for_extraction
```pulse
fn impl_pred_recursive
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (w: jumper (parse_recursive p)) // for code conciseness purposes
  (j: jumper p.parse_header)
  (f: jump_recursive_step_count s)
  (pr: pred_recursive_t s)
  (g: impl_pred_t (serialize_recursive s) pr.base)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased p.t)
  requires pts_to_serialized (serialize_recursive s) input #pm v
  returns res: bool
  ensures pts_to_serialized (serialize_recursive s) input #pm v ** pure (res == pr.pred v)
{
  L.pts_to_serialized_nlist_1 (serialize_recursive s) input;
  let res = impl_nlist_forall_pred_recursive s w j f pr g 1sz input;
  elim_stick _ _;
  res
}
```
