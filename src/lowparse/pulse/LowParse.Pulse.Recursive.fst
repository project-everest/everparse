module LowParse.Pulse.Recursive
open LowParse.Spec.Base
include LowParse.Spec.Recursive
open LowParse.Pulse.Util
open LowParse.Pulse.Base

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference

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

module L = LowParse.Spec.VCList

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
