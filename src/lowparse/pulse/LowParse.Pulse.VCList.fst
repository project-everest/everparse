module LowParse.Pulse.VCList

#lang-pulse
include LowParse.Spec.VCList
include LowParse.Pulse.Combinators
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module GR = Pulse.Lib.GhostReference
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch.Util
module S = Pulse.Lib.Slice

#set-options "--z3rlimit 20"


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

inline_for_extraction
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

ghost
fn nlist_cons_as_nondep_then_intro
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
  pure (
    v == (fst v' :: snd v')
  )
{
  synth_inverse_1 t (n - 1);
  synth_inverse_2 t (n - 1);
  rewrite
    pts_to_serialized
      (serialize_nlist n s)
      input #pm v
  as
    pts_to_serialized
      (serialize_synth _ (synth_nlist (n - 1)) (serialize_nondep_then s (serialize_nlist' (n - 1) s)) (synth_nlist_recip (n - 1)) ())
      input #pm v;
  pts_to_serialized_synth_l2r
    (serialize_nondep_then s (serialize_nlist' (n - 1) s))
    (synth_nlist (n - 1))
    (synth_nlist_recip (n - 1))
    input;
}

ghost
fn nlist_cons_as_nondep_then_elim
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (n: nat)
  (input: slice byte)
  (#pm: perm)
  (#v: (t & nlist n t))
requires
  pts_to_serialized (serialize_nondep_then s (serialize_nlist n s)) input #pm v
ensures
  pts_to_serialized (serialize_nlist (n + 1) s) input #pm (fst v :: snd v)
{
  pts_to_serialized_synth_intro
    (serialize_nondep_then s (serialize_nlist' n s))
    (synth_nlist n)
    (synth_nlist_recip n)
    input
}

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
  Trade.trans (pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm _) _ (pts_to_serialized (serialize_nlist n s) input #pm v)
}

let nlist_hd_tl_post'
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd tl: slice byte)
: slprop
= pts_to_serialized s hd #pm (List.Tot.hd v) **
  pts_to_serialized (serialize_nlist (n - 1) s) tl #pm (List.Tot.tl v) **
  Trade.trade
    (pts_to_serialized s hd #pm (List.Tot.hd v) **
      pts_to_serialized (serialize_nlist (n - 1) s) tl #pm (List.Tot.tl v))
    (pts_to_serialized (serialize_nlist n s) input #pm v)

let nlist_hd_tl_post
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd_tl: (slice byte & slice byte))
: slprop
= nlist_hd_tl_post' s sq n input pm v (fst hd_tl) (snd hd_tl)

inline_for_extraction
fn nlist_hd_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  pts_to_serialized (serialize_nlist n s) input #pm v
returns res : (slice byte & slice byte)
ensures
  nlist_hd_tl_post s sq n input pm v res
{
  nlist_cons_as_nondep_then s n input;
  with v' . assert (pts_to_serialized (serialize_nondep_then s (serialize_nlist (n - 1) s)) input #pm v');
  let res = split_nondep_then #_ #(nlist (n - 1) t) s j #(parse_nlist_kind (n - 1) k) #(coerce_eq () (parse_nlist (n - 1) p)) (coerce_eq () (serialize_nlist (n - 1) s <: serializer (parse_nlist (n - 1) p))) input; // FIXME: same as above
  let s1, s2 = res;
  unfold (split_nondep_then_post s (serialize_nlist (n - 1) s) input pm v' (s1, s2));
  unfold (split_nondep_then_post' s (serialize_nlist (n - 1) s) input pm v' s1 s2);
  Trade.trans _ _ (pts_to_serialized (serialize_nlist n s) input #pm v);
  fold (nlist_hd_tl_post' s sq n input pm v s1 s2);
  fold (nlist_hd_tl_post s sq n input pm v res);
  res
}

ghost fn nlist_as_nondep_then_nondep_then_left
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (#t': Type0)
  (#k': parser_kind)
  (#p': parser k' t')
  (s': serializer p')
  (input: slice byte)
  (#pm: perm)
  (#v: (nlist n t & t'))
requires
  pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v
ensures (
  exists* v' .
  pts_to_serialized (serialize_nondep_then s (serialize_nondep_then (serialize_nlist (n - 1) s) s')) input #pm v' **
  Trade.trade
    (pts_to_serialized (serialize_nondep_then s (serialize_nondep_then (serialize_nlist (n - 1) s) s')) input #pm v')
    (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v) **
  pure (
    fst v' == List.Tot.hd (fst v) /\
    (fst (snd v') <: list t) == List.Tot.tl (fst v) /\
    snd (snd v') == snd v
  )
)
{
  let res = ghost_split_nondep_then
    (serialize_nlist n s)
    s'
    input;
  nlist_cons_as_nondep_then_intro s n (fst res);
  join_nondep_then (serialize_nondep_then s (serialize_nlist (n - 1) s)) (fst res) s' (snd res) input;
  with v1 . assert (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s (serialize_nlist (n - 1) s)) s') input #pm v1);
  intro
    (Trade.trade
      (pts_to_serialized (serialize_nondep_then (serialize_nondep_then s (serialize_nlist (n - 1) s)) s') input #pm v1)
      (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v)
    )
    #emp
    fn _
  {
    let res = ghost_split_nondep_then
      (serialize_nondep_then s (serialize_nlist (n - 1) s))
      s'
      input;
    nlist_cons_as_nondep_then_elim s (n - 1) (fst res);
    join_nondep_then (serialize_nlist n s) (fst res) s' (snd res) input
  };
  pts_to_serialized_nondep_then_assoc_l2r
    s
    (serialize_nlist (n - 1) s)
    s'
    input;
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v)
}

inline_for_extraction
fn nlist_hd_tl_nondep_then_left
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: jumper p)
  (n: Ghost.erased nat)
  (n_pos: squash (n > 0))
  (#t': Type0)
  (#k': Ghost.erased parser_kind)
  (#p': parser k' t')
  (s': serializer p')
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t & t'))
requires
  pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v
returns res : (slice byte & slice byte)
ensures (
  let (hd, tl) = res in
  exists* v' .
  pts_to_serialized s hd #pm (List.Tot.hd (fst v)) **
  pts_to_serialized (serialize_nondep_then (serialize_nlist (n - 1) s) s') tl #pm v' **
  Trade.trade
    (pts_to_serialized s hd #pm (List.Tot.hd (fst v)) **
  pts_to_serialized (serialize_nondep_then (serialize_nlist (n - 1) s) s') tl #pm v')
    (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v) **
  pure (
    (fst v' <: list t) == List.Tot.tl (fst v) /\
    snd v' == snd v
  )
)
{
  nlist_as_nondep_then_nondep_then_left s sq n s' input;
  with v1 . assert (
    pts_to_serialized (serialize_nondep_then s (serialize_nondep_then (serialize_nlist (n - 1) s) s')) input #pm v1
  );
  let hd, tl = split_nondep_then
    #_ #(nlist (n - 1) t & t')
    s
    j
    #(and_then_kind (parse_nlist_kind (n - 1) k) k')
    #(coerce_eq () (nondep_then #_ #(nlist (n - 1) t) (parse_nlist (n - 1) p) #_ #t' p'))
    (coerce_eq () (serialize_nondep_then (serialize_nlist (n - 1) s) s'))
    input;
  unfold (split_nondep_then_post 
    s
    (serialize_nondep_then (serialize_nlist (n - 1) s) s')
    input
    pm
    v1
    (hd, tl)
  );
  unfold (split_nondep_then_post'
    s
    (serialize_nondep_then (serialize_nlist (n - 1) s) s')
    input
    pm
    v1
    hd tl
  );
  Trade.trans _ _ (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v);
  (hd, tl)
}

inline_for_extraction
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

inline_for_extraction
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

inline_for_extraction
fn nlist_hd_nondep_then_left
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: jumper p)
  (n: Ghost.erased nat)
  (n_pos: squash (n > 0))
  (#t': Type0)
  (#k': Ghost.erased parser_kind)
  (#p': parser k' t')
  (s': serializer p')
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t & t'))
requires
  pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v
returns hd : slice byte
ensures (
  pts_to_serialized s hd #pm (List.Tot.hd (fst v)) **
  Trade.trade
    (pts_to_serialized s hd #pm (List.Tot.hd (fst v)))
    (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v)
)
{
  let hd, tl = nlist_hd_tl_nondep_then_left s sq j n () s' input;
  Trade.elim_hyp_r _ _ _;
  hd
}

inline_for_extraction
fn nlist_tl_nondep_then_left
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: jumper p)
  (n: Ghost.erased nat)
  (n_pos: squash (n > 0))
  (#t': Type0)
  (#k': Ghost.erased parser_kind)
  (#p': parser k' t')
  (s': serializer p')
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t & t'))
requires
  pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v
returns tl : slice byte
ensures (
  exists* v' .
  pts_to_serialized (serialize_nondep_then (serialize_nlist (n - 1) s) s') tl #pm v' **
  Trade.trade
    (pts_to_serialized (serialize_nondep_then (serialize_nlist (n - 1) s) s') tl #pm v')
    (pts_to_serialized (serialize_nondep_then (serialize_nlist n s) s') input #pm v) **
  pure (
    (fst v' <: list t) == List.Tot.tl (fst v) /\
    snd v' == snd v
  )
)
{
  let hd, tl = nlist_hd_tl_nondep_then_left s sq j n () s' input;
  Trade.elim_hyp_l _ _ _;
  tl
}

inline_for_extraction
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
    with 'res. assert R.pts_to pres 'res;
    let res = !pres;
    rewrite each 'res as res;
    let i = !pi;
    let res2 = nlist_tl s j (n0 - SZ.v i) res;
    pi := (SZ.add i 1sz);
    pres := res2;
    Trade.trans
      (pts_to_serialized (serialize_nlist (n0 - SZ.v i - 1) s) res2 #pm _)
      _
      _
  };
  with 'res. assert R.pts_to pres 'res;
  let res = !pres;
  rewrite each 'res as res;
  let res2 = nlist_hd s j (n0 - SZ.v i0) res;
  Trade.trans
    (pts_to_serialized s res2 #pm _) _ _;
  res2
}

inline_for_extraction
let impl_order_t
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (order: (t -> t -> bool))
=
    (a1: slice byte) ->
    (a2: slice byte) ->
    (#p1: perm) ->
    (#p2: perm) ->
    (#v1: Ghost.erased t) ->
    (#v2: Ghost.erased t) ->
    stt bool
      (pts_to_serialized s a1 #p1 v1 ** pts_to_serialized s a2 #p2 v2)
      (fun res -> pts_to_serialized s a1 #p1 v1 ** pts_to_serialized s a2 #p2 v2 ** pure (res == order v1 v2))

inline_for_extraction
fn nlist_sorted
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: jumper p)
  (order: Ghost.erased (t -> t -> bool))
  (impl_order: impl_order_t s order)
  (n: SZ.t)
  (a: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist (SZ.v n) t))
requires
    (pts_to_serialized (serialize_nlist (SZ.v n) s) a #pm v)
returns res: bool
ensures
    (pts_to_serialized (serialize_nlist (SZ.v n) s) a #pm v ** pure (res == List.Tot.sorted order v))
{
  if (n = 0sz) {
    true
  } else {
    let pl = nlist_hd_tl s sq j (SZ.v n) a;
    let s1, s2 = pl;
    unfold (nlist_hd_tl_post s sq (SZ.v n) a pm v pl);
    unfold (nlist_hd_tl_post' s sq (SZ.v n) a pm v s1 s2);
    let mut phd = s1;
    let mut ptl = s2;
    let n' : SZ.t = SZ.sub n 1sz;
    let mut pi = n';
    let mut pres = true;
    while (
      let i = !pi;
      let res = !pres;
      (res && SZ.gt i 0sz)
    ) invariant cont . exists* shd stl i res hd tl .
      R.pts_to phd shd **
      R.pts_to ptl stl **
      R.pts_to pi i **
      R.pts_to pres res **
      pts_to_serialized s shd #pm hd **
      pts_to_serialized (serialize_nlist (SZ.v i) s) stl #pm tl **
      Trade.trade
        (pts_to_serialized s shd #pm hd **
          pts_to_serialized (serialize_nlist (SZ.v i) s) stl #pm tl)
        (pts_to_serialized (serialize_nlist (SZ.v n) s) a #pm v) **
      pure (
        List.Tot.sorted order v == (res && List.Tot.sorted order (hd :: tl)) /\
        cont == (res && SZ.gt i 0sz)
      )
    {
      with gi . assert (R.pts_to pi gi);
      with 'stl. assert R.pts_to ptl 'stl;
      let stl = !ptl;
      rewrite each 'stl as stl;
      with tl . assert (pts_to_serialized (serialize_nlist (SZ.v gi) s) stl #pm tl);
      let pl = nlist_hd_tl s sq j (SZ.v gi) stl;
      let s1, s2 = pl;
      unfold (nlist_hd_tl_post s sq (SZ.v gi) stl pm tl pl);
      unfold (nlist_hd_tl_post' s sq (SZ.v gi) stl pm tl s1 s2);
      with 'phd. assert R.pts_to phd 'phd;
      let shd = !phd;
      rewrite each 'phd as shd;
      let res = impl_order shd s1;
      if (res) {
        Trade.elim_hyp_l _ _ (pts_to_serialized (serialize_nlist (SZ.v n) s) a #pm v);
        Trade.trans _ _ (pts_to_serialized (serialize_nlist (SZ.v n) s) a #pm v);
        phd := s1;
        ptl := s2;
        let i = !pi;
        let i' : SZ.t = SZ.sub i 1sz;
        pi := i';
      } else {
        Trade.elim _ (pts_to_serialized (serialize_nlist (SZ.v gi) s) stl #pm tl);
        pres := false;
      }
    };
    Trade.elim _ _;
    !pres
  }
}

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

inline_for_extraction
fn compute_remaining_size_nlist_as_array
  (#tarray: Type0)
  (#telem: Type0)
  (#t: Type0)
  (varray: (tarray -> option (with_perm (A.array telem))))
  (vmatch: (tarray -> telem -> t -> slprop))
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p  { k.parser_kind_subkind == Some ParserStrong })
  (w: ((a: tarray) -> compute_remaining_size (vmatch a) s))
  (n: SZ.t)
: compute_remaining_size #_ #_ (nlist_match_array varray vmatch (SZ.v n)) #_ #_ (LowParse.Spec.VCList.serialize_nlist (SZ.v n) s)
=
  (arr: _)
  (#x: _)
  (out: _)
  (#v: _)
{
  unfold (nlist_match_array varray vmatch (SZ.v n) arr x);
  with telem (ar : with_perm (A.array _)) (c : _).
    assert A.pts_to #telem ar.v #ar.p c;
  let a = Some?.v (varray arr);
  rewrite each ar as a;
  with c . assert (A.pts_to a.v #a.p c);
  let mut pres = true;
  let mut pi = 0sz;
  Trade.refl (PM.seq_list_match c x (vmatch arr));
  PM.seq_list_match_length (vmatch arr) _ _;
  while (
    let res = !pres;
    let i = !pi;
    (res && (SZ.lt i n))
  ) invariant b . exists* res i c2 l2 v1 . (
    A.pts_to a.v #a.p c **
    R.pts_to pres res **
    R.pts_to pi i **
    PM.seq_list_match c2 l2 (vmatch arr) **
    R.pts_to out v1 **
    trade
      (PM.seq_list_match c2 l2 (vmatch arr))
      (PM.seq_list_match c x (vmatch arr))
    ** pure (
      SZ.v i <= SZ.v n /\
      b == (res && (SZ.v i < SZ.v n)) /\
      Seq.length c == SZ.v n /\
      (res == false ==> SZ.v v < Seq.length (serialize (serialize_nlist (SZ.v n) s) x)) /\
      (res == true ==> (
        Seq.equal c2 (Seq.slice c (SZ.v i) (SZ.v n)) /\
        List.Tot.length l2 == SZ.v n - SZ.v i /\
        SZ.v v - Seq.length (serialize (serialize_nlist (SZ.v n) s) x) == SZ.v v1 - Seq.length (serialize (serialize_nlist (SZ.v n - SZ.v i) s) l2)
      )) /\
      True
    )
  ) {
    let i = !pi;
    PM.seq_list_match_length (vmatch arr) _ _;
    with c2 l2 . assert (PM.seq_list_match c2 l2 (vmatch arr));
    PM.seq_list_match_cons_elim_trade c2 l2 (vmatch arr);
    let e = A.op_Array_Access a.v i;
    with ve l2'.
      assert (vmatch arr (Seq.head c2) ve ** PM.seq_list_match (Seq.tail c2) l2' (vmatch arr));
    let ni' : Ghost.erased nat = Ghost.hide (SZ.v n - SZ.v i - 1);
    serialize_nlist_cons' (ni') s ve l2';
    Trade.rewrite_with_trade
      (vmatch arr _ _)
      (vmatch arr e ve);
    let res = w arr e out;
    Trade.elim (vmatch arr e ve) _;
    if (res) {
      let i' = SZ.add i 1sz;
      pi := i';
      Trade.elim_hyp_l _ _ _;
      Trade.trans _ _ (PM.seq_list_match c x (vmatch arr));
    } else {
      Trade.elim _ (PM.seq_list_match c2 l2 (vmatch arr));
      pres := false;
    }
  };
  Trade.elim _ _;
  fold (nlist_match_array varray vmatch (SZ.v n) arr x);
  !pres
}

inline_for_extraction
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
  with telem (ar : with_perm (A.array _)) (c : _).
    assert A.pts_to #telem ar.v #ar.p c;
  rewrite each ar as a;
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
    with ve l2' . assert (vmatch arr (Seq.head c2) ve ** PM.seq_list_match (Seq.tail c2) l2' (vmatch arr));
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

let nlist_match_slice
  (#tslice: Type0)
  (#telem: Type0)
  (#t: Type)
  (vslice: (tslice -> GTot (option (with_perm (S.slice telem)))))
  (vmatch: (tslice -> telem -> t -> slprop))
  (n: nat)
  (a: tslice)
  (l: LowParse.Spec.VCList.nlist n t)
: Tot slprop
= exists* (ar: with_perm (S.slice telem)) c .
    pts_to ar.v #ar.p c **
    PM.seq_list_match c l (vmatch a) **
    pure (vslice a == Some ar)

ghost fn nlist_match_slice_elim
  (#tslice: Type0)
  (#telem: Type0)
  (#t: Type0)
  (vslice: (tslice -> GTot (option (with_perm (S.slice telem)))))
  (vmatch: (tslice -> telem -> t -> slprop))
  (n: nat)
  (a: tslice)
  (l: LowParse.Spec.VCList.nlist n t)
requires nlist_match_slice vslice vmatch n a l
returns ar: Ghost.erased (with_perm (S.slice telem))
ensures exists* c .
    pts_to (Ghost.reveal ar).v #ar.p c **
    PM.seq_list_match c l (vmatch a) **
    pure (vslice a == Some (Ghost.reveal ar))
{
  unfold (nlist_match_slice vslice vmatch n a l);
  with ar c . assert (
    pts_to #telem (ar <: with_perm (S.slice telem)).v #ar.p c **
    PM.seq_list_match c l (vmatch a)
  );
  ar
}

ghost
fn nlist_match_slice_intro
  (#tslice: Type0)
  (#telem: Type0)
  (#t: Type0)
  (vslice: (tslice -> GTot (option (with_perm (S.slice telem)))))
  (vmatch: (tslice -> telem -> t -> slprop))
  (n: nat)
  (a: tslice)
  (l: nlist n t)
  (ar: with_perm (S.slice telem))
  (c: Seq.seq telem)
requires
    (pts_to ar.v #ar.p c **
      PM.seq_list_match c l (vmatch a) **
      pure (vslice a == Some ar)
    )
ensures
    (nlist_match_slice vslice vmatch n a l)
{
  fold (nlist_match_slice vslice vmatch n a l)
}

inline_for_extraction
fn compute_remaining_size_nlist_as_slice
  (#tslice: Type0)
  (#telem: Type0)
  (#t: Type0)
  (vslice: (tslice -> option (with_perm (S.slice telem))))
  (vmatch: (tslice -> telem -> t -> slprop))
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p  { k.parser_kind_subkind == Some ParserStrong })
  (w: ((a: tslice) -> compute_remaining_size (vmatch a) s))
  (n: SZ.t)
: compute_remaining_size #_ #_ (nlist_match_slice vslice vmatch (SZ.v n)) #_ #_ (LowParse.Spec.VCList.serialize_nlist (SZ.v n) s)
=
  (arr: _)
  (#x: _)
  (out: _)
  (#v: _)
{
  unfold (nlist_match_slice vslice vmatch (SZ.v n) arr x);
  with telem (ar : with_perm (S.slice _)) (c : _).
    assert S.pts_to #telem ar.v #ar.p c;
  let a = Some?.v (vslice arr);
  rewrite each ar as a;

  let mut pres = true;
  let mut pi = 0sz;
  Trade.refl (PM.seq_list_match c x (vmatch arr));
  PM.seq_list_match_length (vmatch arr) _ _;
  while (
    let res = !pres;
    let i = !pi;
    (res && (SZ.lt i n))
  ) invariant b . exists* res i c2 l2 v1 . (
    pts_to a.v #a.p c **
    R.pts_to pres res **
    R.pts_to pi i **
    PM.seq_list_match c2 l2 (vmatch arr) **
    R.pts_to out v1 **
    trade
      (PM.seq_list_match c2 l2 (vmatch arr))
      (PM.seq_list_match c x (vmatch arr))
    ** pure (
      SZ.v i <= SZ.v n /\
      b == (res && (SZ.v i < SZ.v n)) /\
      Seq.length c == SZ.v n /\
      (res == false ==> SZ.v v < Seq.length (serialize (serialize_nlist (SZ.v n) s) x)) /\
      (res == true ==> (
        Seq.equal c2 (Seq.slice c (SZ.v i) (SZ.v n)) /\
        List.Tot.length l2 == SZ.v n - SZ.v i /\
        SZ.v v - Seq.length (serialize (serialize_nlist (SZ.v n) s) x) == SZ.v v1 - Seq.length (serialize (serialize_nlist (SZ.v n - SZ.v i) s) l2)
      )) /\
      True
    )
  ) {
    let i = !pi;
    PM.seq_list_match_length (vmatch arr) _ _;
    with c2 l2 . assert (PM.seq_list_match c2 l2 (vmatch arr));
    PM.seq_list_match_cons_elim_trade c2 l2 (vmatch arr);
    let e = S.op_Array_Access a.v i;
    with ve l2'.
      assert (vmatch arr (Seq.head c2) ve ** PM.seq_list_match (Seq.tail c2) l2' (vmatch arr));
    let ni' : Ghost.erased nat = Ghost.hide (SZ.v n - SZ.v i - 1);
    serialize_nlist_cons' (ni') s ve l2';
    Trade.rewrite_with_trade
      (vmatch arr _ _)
      (vmatch arr e ve);
    let res = w arr e out;
    Trade.elim (vmatch arr e ve) _;
    if (res) {
      let i' = SZ.add i 1sz;
      pi := i';
      Trade.elim_hyp_l _ _ _;
      Trade.trans _ _ (PM.seq_list_match c x (vmatch arr));
    } else {
      Trade.elim _ (PM.seq_list_match c2 l2 (vmatch arr));
      pres := false;
    }
  };
  Trade.elim _ _;
  fold (nlist_match_slice vslice vmatch (SZ.v n) arr x);
  !pres
}

inline_for_extraction
fn l2r_write_nlist_as_slice
  (#tslice: Type0)
  (#telem: Type0)
  (#t: Type0)
  (vslice: (tslice -> option (with_perm (S.slice telem))))
  (vmatch: (tslice -> telem -> t -> slprop))
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p  { k.parser_kind_subkind == Some ParserStrong })
  (w: ((a: tslice) -> l2r_writer (vmatch a) s))
  (n: SZ.t)
: l2r_writer #_ #_ (nlist_match_slice vslice vmatch (SZ.v n)) #_ #_ (LowParse.Spec.VCList.serialize_nlist (SZ.v n) s)
=
  (arr: _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  unfold (nlist_match_slice vslice vmatch (SZ.v n) arr x);
  with telem (ar : with_perm (S.slice _)) (c : _).
    assert S.pts_to #telem ar.v #ar.p c;
  let a = Some?.v (vslice arr);
  rewrite each ar as a;

  let pl1 : GR.ref (list t) = GR.alloc #(list t) [];
  let mut pres = offset;
  let mut pi = 0sz;
  Trade.refl (PM.seq_list_match c x (vmatch arr));
  PM.seq_list_match_length (vmatch arr) _ _;
  while (
    let i = !pi;
    SZ.lt i n
  ) invariant b . exists* res i l1 c2 l2 v1 . (
    pts_to a.v #a.p c **
    R.pts_to pres res **
    R.pts_to pi i **
    GR.pts_to pl1 l1 **
    PM.seq_list_match c2 l2 (vmatch arr) **
    S.pts_to out v1 **
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
    let e = S.op_Array_Access a.v i;
    with ve l2'.
      assert (vmatch arr (Seq.head c2) ve ** PM.seq_list_match (Seq.tail c2) l2' (vmatch arr));
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
  fold (nlist_match_slice vslice vmatch (SZ.v n) arr x);
  !pres
}

let nlist_match_slice0
  (#telem: Type0)
  (#t: Type)
  (vmatch: (telem -> t -> slprop))
= nlist_match_slice Some (fun _ -> vmatch)

let nlist_match_slice_wf
  (#telem: Type0)
  (#t: Type)
  (n: nat)
  (a: _)
  (l: LowParse.Spec.VCList.nlist n t)
  (vmatch: (telem -> (x: t { x << l }) -> slprop))
: Tot slprop
= exists* (ar: with_perm (S.slice telem)) c .
    pts_to ar.v #ar.p c **
    PM.seq_list_match c l (vmatch) **
    pure (Some a == Some ar)

let nlist_match_slice_wf_eq
  (#telem: Type0)
  (#t: Type)
  (vmatch: (telem -> t -> slprop))
  (n: nat)
  (a: _)
  (l: LowParse.Spec.VCList.nlist n t)
: Lemma
  (nlist_match_slice0 vmatch n a l == nlist_match_slice_wf n a l vmatch)
= assert_norm (nlist_match_slice0 vmatch n a l == nlist_match_slice_wf n a l vmatch)

ghost fn nlist_match_slice0_elim
  (#telem: Type0)
  (#t: Type0)
  (vmatch: (telem -> t -> slprop))
  (n: nat)
  (a: with_perm (S.slice telem))
  (l: LowParse.Spec.VCList.nlist n t)
requires nlist_match_slice0 vmatch n a l
ensures exists* c .
    pts_to a.v #a.p c **
    PM.seq_list_match c l (vmatch)
{
  unfold (nlist_match_slice0 vmatch n a l);
  let ar' = nlist_match_slice_elim Some (fun _ -> vmatch) n a l;
  with c . assert (
    pts_to #telem (ar' <: with_perm (S.slice telem)).v #ar'.p c
  );
  rewrite (pts_to #telem (ar' <: with_perm (S.slice telem)).v #ar'.p c)
    as (pts_to a.v #a.p c)
}

ghost
fn nlist_match_slice0_intro
  (#telem: Type0)
  (#t: Type0)
  (vmatch: (telem -> t -> slprop))
  (n: nat)
  (a: with_perm (S.slice telem))
  (l: nlist n t)
  (c: Seq.seq telem)
requires
    (pts_to a.v #a.p c **
      PM.seq_list_match c l (vmatch)
    )
ensures
    (nlist_match_slice0 vmatch n a l)
{
  fold (nlist_match_slice Some (fun _ -> vmatch) n a l);
  fold (nlist_match_slice0 vmatch n a l)
}

ghost fn nlist_match_slice0_elim_trade
  (#telem: Type0)
  (#t: Type0)
  (vmatch: (telem -> t -> slprop))
  (n: nat)
  (a: with_perm (S.slice telem))
  (l: LowParse.Spec.VCList.nlist n t)
requires nlist_match_slice0 vmatch n a l
ensures exists* c .
    pts_to a.v #a.p c **
    PM.seq_list_match c l (vmatch) **
    Trade.trade
      (pts_to a.v #a.p c **
        PM.seq_list_match c l (vmatch))
      (nlist_match_slice0 vmatch n a l)
{
  nlist_match_slice0_elim vmatch n a l;
  with c . assert (pts_to a.v #a.p c);
  intro
    (Trade.trade
      (pts_to a.v #a.p c **
        PM.seq_list_match c l (vmatch)
      )
      (nlist_match_slice0 vmatch n a l)
    )
    #emp
    fn _
  {
    nlist_match_slice0_intro vmatch n a l c
  };
}

inline_for_extraction
fn l2r_write_nlist_as_slice0
  (#telem: Type0)
  (#t: Type0)
  (vmatch: (telem -> t -> slprop))
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p  { k.parser_kind_subkind == Some ParserStrong })
  (w: (l2r_writer (vmatch) s))
  (n: Ghost.erased nat) // because it is known as the length of the slice
: l2r_writer #_ #_ (nlist_match_slice0 vmatch (n)) #_ #_ (LowParse.Spec.VCList.serialize_nlist (n) s)
=
  (arr: _)
  (#x: _)
  (out: _)
  (offset: _)
  (#v: _)
{
  unfold (nlist_match_slice0 vmatch (n) arr x);
  let ar = nlist_match_slice_elim Some (fun _ -> vmatch) n arr x;
  with c . assert (pts_to (Ghost.reveal ar).v #ar.p c);
  rewrite (pts_to (Ghost.reveal ar).v #ar.p c) as (pts_to arr.v #arr.p c);
  S.pts_to_len arr.v;
  PM.seq_list_match_length vmatch c x;
  let n' = S.len arr.v;
  nlist_match_slice_intro Some (fun _ -> vmatch) (SZ.v n') arr x arr c;
  let res = l2r_write_nlist_as_slice Some (fun _ -> vmatch) s (fun _ -> w) n' arr out offset;
  fold (nlist_match_slice0 vmatch (n) arr x);
  res
}
