module LowParse.Pulse.VCList
include LowParse.Spec.VCList
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util

#push-options "--z3rlimit 16"

let rec serialize_nlist_append
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n1: nat)
  (l1: nlist n1 t)
  (n2: nat)
  (l2: nlist n2 t)
: Lemma
  (ensures (let l = List.Tot.append l1 l2 in
    List.Tot.length l == n1 + n2 /\
    serialize (serialize_nlist (n1 + n2) s) l == Seq.append (serialize (serialize_nlist n1 s) l1) (serialize (serialize_nlist n2 s) l2)
  ))
  (decreases n1)
= if n1 = 0
  then begin
    serialize_nlist_nil p s;
    Seq.append_empty_l (serialize (serialize_nlist n2 s) l2)
  end    
  else begin
    let a :: q = l1 in
    serialize_nlist_append s (n1 - 1) q n2 l2;
    serialize_nlist_cons ((n1 - 1) + n2) s a (List.Tot.append q l2);
    serialize_nlist_cons (n1 - 1) s a q;
    Seq.append_assoc
      (serialize s a)
      (serialize (serialize_nlist (n1 - 1) s) q)
      (serialize (serialize_nlist n2 s) l2)
  end

#pop-options

inline_for_extraction
```pulse
fn jump_nlist
   (#t: Type0)
   (#k: Ghost.erased parser_kind)
   (#p: parser k t)
   (j: jumper p)
   (n0: SZ.t)
: jumper #(nlist (SZ.v n0) t) #(parse_nlist_kind (SZ.v n0) k) (parse_nlist (SZ.v n0) p)
=
  (input: slice byte)
  (offset0: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let mut pn = n0;
  let mut poffset = offset0;
  while (
    let n = !pn;
    (SZ.gt n 0sz)
  ) invariant b . exists* n offset . (
    pts_to input #pm v ** R.pts_to pn n ** R.pts_to poffset offset ** pure (
    SZ.v offset <= Seq.length v /\ (
    let pr0 = parse_consume (parse_nlist (SZ.v n0) p) (Seq.slice v (SZ.v offset0) (Seq.length v)) in
    let pr = parse_consume (parse_nlist (SZ.v n) p) (Seq.slice v (SZ.v offset) (Seq.length v)) in
    Some? pr0 /\ Some? pr /\
    SZ.v offset0 + Some?.v pr0 == SZ.v offset + Some?.v pr /\
    b == (SZ.v n > 0)
  ))) {
    let n = !pn;
    let offset = !poffset;
    parse_nlist_eq (SZ.v n) p (Seq.slice v (SZ.v offset) (Seq.length v));
    let offset' = j input offset;
    pn := (SZ.sub n 1sz);
    poffset := offset';
  };
  !poffset
}
```

```pulse
ghost
fn nlist_cons_as_nondep_then
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n: pos)
  (input: slice byte)
  (#pm: perm)
  (#v: nlist n t)
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
ensures exists* v' .
  pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm v' **
  trade (pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm v') (pts_to_serialized (serialize_nlist n s) input #pm v) **
  pure (
    v == (fst v' :: snd v')
  )
{
  synth_inverse_1 t (n - 1);
  synth_inverse_2 t (n - 1);
  Trade.rewrite_with_trade
    (pts_to_serialized (serialize_nlist n s) input #pm v)
    (pts_to_serialized (serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then s (serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ()) input #pm v);
  pts_to_serialized_synth_l2r_trade
    (serialize_nondep_then s (serialize_nlist' (n - 1) s))
    (synth_nlist (n - 1))
    (synth_nlist_recip (n - 1))
    input;
  Trade.trans (pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm _) _ _
}
```

inline_for_extraction
```pulse
fn nlist_hd
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
returns input' : slice byte
ensures exists* v' .
  pts_to_serialized s input' #pm v' **
  trade (pts_to_serialized s input' #pm v') (pts_to_serialized (serialize_nlist n s) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.hd v
  )
{
  nlist_cons_as_nondep_then s n input;
  let res = nondep_then_fst #_ #(nlist (n - 1) t) s j #(parse_nlist_kind (n - 1) k) #(coerce_eq () (parse_nlist (n - 1) p)) (coerce_eq () (serialize_nlist (n - 1) s <: serializer #(parse_nlist_kind (n - 1) k) (parse_nlist (n - 1) p))) input; // FIXME: WHY WHY WHY are those reveal (hide (...)) NOT reduced?
  Trade.trans (pts_to_serialized s res #pm _) _ _;
  res
}
```

inline_for_extraction
```pulse
fn nlist_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (j: jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
returns input' : slice byte
ensures exists* v' .
  pts_to_serialized (serialize_nlist (n - 1) s) input' #pm v' **
  trade (pts_to_serialized (serialize_nlist (n - 1) s) input' #pm v') (pts_to_serialized (serialize_nlist n s) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.tl v
  )
{
  nlist_cons_as_nondep_then s n input;
  let res = nondep_then_snd #_ #(nlist (n - 1) t) s j #(parse_nlist_kind (n - 1) k) #(coerce_eq () (parse_nlist (n - 1) p)) (coerce_eq () (serialize_nlist (n - 1) s <: serializer (parse_nlist (n - 1) p))) input; // FIXME: same as above
  Trade.trans (pts_to_serialized (serialize_nlist (n - 1) s) res #pm _) _ _;
  res
}
```

inline_for_extraction
```pulse
fn nlist_nth
   (#t: Type0)
   (#k: Ghost.erased parser_kind)
   (#p: parser k t)
   (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
   (j: jumper p)
   (n0: Ghost.erased nat)
  (input: slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist n0 t))
  (i0: SZ.t { SZ.v i0 < n0 })
requires
  pts_to_serialized (serialize_nlist n0 s) input #pm v0
returns input' : slice byte
ensures exists* v .
  pts_to_serialized s input' #pm v **
  trade (pts_to_serialized s input' #pm v) (pts_to_serialized (serialize_nlist n0 s) input #pm v0) **
  pure (v == List.Tot.index v0 (SZ.v i0))
{
  Trade.refl (pts_to_serialized (serialize_nlist n0 s) input #pm v0);
  let mut pi = 0sz;
  let mut pres = input;
  while (
    let i = !pi;
    (SZ.lt i i0)
  ) invariant b . exists* i res (n: nat) (v: nlist n t) . (
    R.pts_to pi i ** R.pts_to pres res **
    pts_to_serialized (serialize_nlist n s) res #pm v **
    trade (pts_to_serialized (serialize_nlist n s) res #pm v) (pts_to_serialized (serialize_nlist n0 s) input #pm v0) **
    pure (
      SZ.v i <= SZ.v i0 /\
      (b == (SZ.v i < SZ.v i0)) /\
      n == n0 - SZ.v i /\
      List.Tot.index v0 (SZ.v i0) == List.Tot.index v (SZ.v i0 - SZ.v i)
  )) {
    let res = !pres;
    let i = !pi;
    let res2 = nlist_tl s j (n0 - SZ.v i) res;
    pi := (SZ.add i 1sz);
    pres := res2;
    Trade.trans
      (pts_to_serialized (serialize_nlist (n0 - SZ.v i - 1) s) res2 #pm _)
      _
      _
  };
  let res = !pres;
  let res2 = nlist_hd s j (n0 - SZ.v i0) res;
  Trade.trans
    (pts_to_serialized s res2 #pm _) _ _;
  res2
}
```

let synth_nlist_1
  (#t: Type)
  (x: t)
: Tot (nlist 1 t)
= [x]

let synth_nlist_1_recip
  (#t: Type)
  (x: nlist 1 t)
: Tot t
= List.Tot.hd x

let parse_nlist_1_eq
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (b: bytes)
: Lemma
  (parse (parse_nlist 1 p) b == parse (parse_synth p synth_nlist_1) b)
= parse_nlist_eq 1 p b;
  parse_synth_eq p synth_nlist_1 b

```pulse
ghost
fn pts_to_serialized_nlist_1
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_serialized s input #pm v
  ensures exists* v' . pts_to_serialized (serialize_nlist 1 s) input #pm v' **
    trade (pts_to_serialized (serialize_nlist 1 s) input #pm v')
      (pts_to_serialized s input #pm v) **
    pure ((v' <: list t) == [v])
{
  pts_to_serialized_synth_trade s synth_nlist_1 synth_nlist_1_recip input;
  Classical.forall_intro (parse_nlist_1_eq p);
  pts_to_serialized_ext_trade
    (serialize_synth p synth_nlist_1 s synth_nlist_1_recip ())
    (serialize_nlist 1 s)
    input;
  Trade.trans
    (pts_to_serialized (serialize_nlist 1 s) input #pm _)
    _ _
}
```

module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch.Util

let nlist_match_array
  (#tarray: Type0)
  (#telem: Type0)
  (#t: Type)
  (varray: (tarray -> GTot (option (with_perm (A.array telem)))))
  (vmatch: (tarray -> telem -> t -> slprop))
  (n: nat)
  (a: tarray)
  (l: LowParse.Spec.VCList.nlist n t)
: Tot slprop
= exists* (ar: with_perm (A.array telem)) c .
    A.pts_to ar.v #ar.p c **
    PM.seq_list_match c l (vmatch a) **
    pure (varray a == Some ar)

```pulse
ghost
fn nlist_match_array_intro
  (#tarray: Type0)
  (#telem: Type0)
  (#t: Type0)
  (varray: (tarray -> GTot (option (with_perm (A.array telem)))))
  (vmatch: (tarray -> telem -> t -> slprop))
  (n: nat)
  (a: tarray)
  (l: nlist n t)
  (ar: with_perm (A.array telem))
  (c: Seq.seq telem)
requires
    (A.pts_to ar.v #ar.p c **
      PM.seq_list_match c l (vmatch a) **
      pure (varray a == Some ar)
    )
ensures
    (nlist_match_array varray vmatch n a l)
{
  fold (nlist_match_array varray vmatch n a l)
}
```

module GR = Pulse.Lib.GhostReference

let serialize_nlist_singleton
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (x: t)
: Lemma
  (let l = [x] in
    List.Tot.length l == 1 /\
    serialize (serialize_nlist 1 s) l == serialize s x)
= serialize_nlist_cons 0 s x [];
  serialize_nlist_nil p s;
  Seq.append_empty_r (serialize s x)

let serialize_nlist_cons'
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (a: t)
  (q: nlist n t)
: Lemma
  (ensures (
    let l = a :: q in
    List.Tot.length l == n + 1 /\
    serialize (serialize_nlist (n + 1) s) l == Seq.append (serialize s a) (serialize (serialize_nlist n s) q)
  ))
= serialize_nlist_cons n s a q

let seq_slice_append_ijk
  (#t: Type)
  (s: Seq.seq t)
  (i j k: nat)
: Lemma
  (requires (i <= j /\ j <= k /\ k <= Seq.length s))
  (ensures (
    i <= j /\ j <= k /\ k <= Seq.length s /\
    Seq.slice s i k == Seq.append (Seq.slice s i j) (Seq.slice s j k)
  ))
= Seq.lemma_split (Seq.slice s i k) (j - i)

#push-options "--z3rlimit 16"

#restart-solver

inline_for_extraction
```pulse
fn l2r_write_nlist_as_array
  (#tarray: Type0)
  (#telem: Type0)
  (#t: Type0)
  (varray: (tarray -> option (with_perm (A.array telem))))
  (vmatch: (tarray -> telem -> t -> slprop))
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p  { k.parser_kind_subkind == Some ParserStrong })
  (w: ((a: tarray) -> l2r_writer (vmatch a) s))
  (n: SZ.t)
: l2r_writer #_ #_ (nlist_match_array varray vmatch (SZ.v n)) #_ #_ (LowParse.Spec.VCList.serialize_nlist (SZ.v n) s)
=
  (arr: _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  unfold (nlist_match_array varray vmatch (SZ.v n) arr x);
  let a = Some?.v (varray arr);
  with c . assert (A.pts_to a.v #a.p c);
  let pl1 : GR.ref (list t) = GR.alloc #(list t) [];
  let mut pres = offset;
  let mut pi = 0sz;
  Trade.refl (PM.seq_list_match c x (vmatch arr));
  PM.seq_list_match_length (vmatch arr) _ _;
  while (
    let i = !pi;
    SZ.lt i n
  ) invariant b . exists* res i l1 c2 l2 v1 . (
    A.pts_to a.v #a.p c **
    R.pts_to pres res **
    R.pts_to pi i **
    GR.pts_to pl1 l1 **
    PM.seq_list_match c2 l2 (vmatch arr) **
    pts_to out v1 **
    trade
      (PM.seq_list_match c2 l2 (vmatch arr))
      (PM.seq_list_match c x (vmatch arr)) **
    pure (
      SZ.v i <= SZ.v n /\
      b == (SZ.v i < SZ.v n) /\
      Seq.length c == SZ.v n /\
      Seq.equal c2 (Seq.slice c (SZ.v i) (SZ.v n)) /\
      SZ.v offset <= SZ.v res /\
      SZ.v res <= Seq.length v /\
      Seq.length v1 == Seq.length v /\
      Seq.slice v1 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset) /\
      List.Tot.length l1 == SZ.v i /\
      Seq.slice v1 (SZ.v offset) (SZ.v res) `Seq.equal` bare_serialize (serialize_nlist (SZ.v i) s) l1 /\
      List.Tot.append l1 l2 == Ghost.reveal x /\
      True
    )
  ) {
    let i = !pi;
    let off = !pres;
    PM.seq_list_match_length (vmatch arr) _ _;
    with l1 . assert (GR.pts_to pl1 l1);
    with c2 l2 . assert (PM.seq_list_match c2 l2 (vmatch arr));
    serialize_nlist_append s (SZ.v i) l1 (SZ.v n - SZ.v i) l2;
    PM.seq_list_match_cons_elim_trade c2 l2 (vmatch arr);
    let e = A.op_Array_Access a.v i;
    let c2' : Ghost.erased (Seq.seq telem) = Seq.tail c2;
    with ve l2' . assert (vmatch arr (Seq.head c2) ve ** PM.seq_list_match c2' l2' (vmatch arr));
    List.Tot.append_assoc l1 [ve] l2';
    let i' = SZ.add i 1sz;
    let ni' : Ghost.erased nat = Ghost.hide (SZ.v n - SZ.v i');
    serialize_nlist_cons' (ni') s ve l2';
    serialize_nlist_singleton s ve;
    serialize_nlist_append s (SZ.v i) l1 1 [ve];
    Trade.rewrite_with_trade
      (vmatch arr _ _)
      (vmatch arr e ve);
    with v1 . assert (pts_to out v1);
    assert (pure (
      SZ.v off + Seq.length (bare_serialize s ve) <= Seq.length v1
    ));
    let res = w arr e out off;
    with v1' . assert (pts_to out v1');
    Trade.elim (vmatch arr e ve) _;
    pi := i';
    List.Tot.append_length l1 [ve];
    let l1' : Ghost.erased (list t) = List.Tot.append l1 [ve];
    GR.op_Colon_Equals pl1 l1';
    pres := res;
    Trade.elim_hyp_l _ _ _;
    Trade.trans _ _ (PM.seq_list_match c x (vmatch arr));
    assert (pure (Seq.equal c2' (Seq.slice c (SZ.v i') (SZ.v n))));
    assert (pure (SZ.v offset <= SZ.v res));
    assert (pure (SZ.v res <= Seq.length v));
    assert (pure (Seq.length v1' == Seq.length v));
    Seq.slice_slice v1 0 (SZ.v off) 0 (SZ.v offset);
    Seq.slice_slice v1' 0 (SZ.v off) 0 (SZ.v offset);
    assert (pure (Seq.slice v1' 0 (SZ.v offset) `Seq.equal` Seq.slice v 0 (SZ.v offset)));
    assert (pure (List.Tot.length l1' == SZ.v i'));
    Seq.slice_slice v1 0 (SZ.v off) (SZ.v offset) (SZ.v off);
    Seq.slice_slice v1' 0 (SZ.v off) (SZ.v offset) (SZ.v off);
    seq_slice_append_ijk v1' (SZ.v offset) (SZ.v off) (SZ.v res);
    assert (pure (Seq.slice v1' (SZ.v offset) (SZ.v off) == bare_serialize (serialize_nlist (SZ.v i) s) l1));
    assert (pure (Seq.slice v1' (SZ.v off) (SZ.v res) == bare_serialize s ve));
    assert (pure (Seq.slice v1' (SZ.v offset) (SZ.v res) == Seq.append (Seq.slice v1' (SZ.v offset) (SZ.v off)) (Seq.slice v1' (SZ.v off) (SZ.v res))));
    assert (pure (Seq.slice v1' (SZ.v offset) (SZ.v res) `Seq.equal` bare_serialize (serialize_nlist (SZ.v i') s) l1'));
    assert (pure (List.Tot.append l1' l2' == Ghost.reveal x));
    ()
  };
  with l1 . assert (GR.pts_to pl1 l1);
  GR.free pl1;
  PM.seq_list_match_length (vmatch arr) _ _;
  List.Tot.append_l_nil l1;
  Trade.elim _ _;
  fold (nlist_match_array varray vmatch (SZ.v n) arr x);
  !pres
}
```

#pop-options
