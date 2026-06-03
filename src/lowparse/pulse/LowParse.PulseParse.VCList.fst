module LowParse.PulseParse.VCList
#lang-pulse
include LowParse.Spec.VCList
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice.Util
open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base
open LowParse.Spec.Combinators

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module LPV = LowParse.Pulse.VCList
module U32 = FStar.UInt32

(* pts_to_parsed for nlist 1: convert between pts_to_parsed p and pts_to_parsed (parse_nlist 1 p) *)

ghost
fn pts_to_parsed_nlist_1_intro
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires PPB.pts_to_parsed p input #pm v
  ensures exists* v' .
    PPB.pts_to_parsed (parse_nlist 1 p) input #pm v' **
    trade (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v')
      (PPB.pts_to_parsed p input #pm v) **
    pure ((v' <: list t) == [v])
{
  unfold (PPB.pts_to_parsed p input #pm v);
  with w . assert (pts_to input #pm w);
  parse_nlist_eq 1 p w;
  parse_synth_eq p LPV.synth_nlist_1 w;
  let v' : Ghost.erased (nlist 1 t) = Ghost.hide [v];
  fold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v')
      (PPB.pts_to_parsed p input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v');
      with w' . assert (pts_to input #pm w');
      parse_nlist_eq 1 p w';
      parse_synth_eq p LPV.synth_nlist_1 w';
      fold (PPB.pts_to_parsed p input #pm v)
    };
}

ghost
fn pts_to_parsed_nlist_1_elim
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#v: nlist 1 t)
  requires PPB.pts_to_parsed (parse_nlist 1 p) input #pm v
  ensures exists* v' .
    PPB.pts_to_parsed p input #pm v' **
    trade (PPB.pts_to_parsed p input #pm v')
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v) **
    pure (v == [v'])
{
  unfold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v);
  with w . assert (pts_to input #pm w);
  parse_nlist_eq 1 p w;
  parse_synth_eq p LPV.synth_nlist_1 w;
  let v' = Ghost.hide (List.Tot.hd v);
  fold (PPB.pts_to_parsed p input #pm v');
  intro
    (Trade.trade
      (PPB.pts_to_parsed p input #pm v')
      (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v)
    )
    #emp
    fn _ {
      unfold (PPB.pts_to_parsed p input #pm v');
      with w' . assert (pts_to input #pm w');
      parse_nlist_eq 1 p w';
      parse_synth_eq p LPV.synth_nlist_1 w';
      fold (PPB.pts_to_parsed (parse_nlist 1 p) input #pm v)
    };
}

(* pts_to_parsed ext for nlist: convert between equivalent nlist parsers *)

let pts_to_parsed_nlist_ext_aux
  (#t: Type0)
  (#k1: parser_kind) (#p1: parser k1 t)
  (#k2: parser_kind) (#p2: parser k2 t)
  (n: nat)
  (prf: (b: bytes) -> Lemma (parse p1 b == parse p2 b))
  (b: bytes)
: Lemma (parse (parse_nlist n p1) b == parse (parse_nlist n p2) b)
= parse_nlist_ext n p1 p2 b (fun b' -> prf b')

ghost
fn pts_to_parsed_nlist_ext
  (#t: Type0)
  (#k1: parser_kind) (#p1: parser k1 t)
  (#k2: parser_kind) (#p2: parser k2 t)
  (n: nat)
  (prf: (b: bytes) -> Lemma (parse p1 b == parse p2 b))
  (input: slice byte)
  (#pm: perm)
  (#v: nlist n t)
  requires PPB.pts_to_parsed (parse_nlist n p1) input #pm v
  ensures PPB.pts_to_parsed (parse_nlist n p2) input #pm v
{
  Classical.forall_intro (pts_to_parsed_nlist_ext_aux #t #k1 #p1 #k2 #p2 n prf);
  PPB.pts_to_parsed_ext (parse_nlist n p2) input
}

(* nlist_hd_tl for pts_to_parsed: split a parsed nlist into head and tail sub-slices.
   Requires ParserStrong to split raw bytes at the correct boundary. *)

let nlist_hd_tl_post'
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd tl: slice byte)
: slprop
= PPB.pts_to_parsed p hd #(pm /. 2.0R) (List.Tot.hd v) **
  PPB.pts_to_parsed (parse_nlist (n - 1) p) tl #(pm /. 2.0R) (List.Tot.tl v) **
  Trade.trade
    (PPB.pts_to_parsed p hd #(pm /. 2.0R) (List.Tot.hd v) **
      PPB.pts_to_parsed (parse_nlist (n - 1) p) tl #(pm /. 2.0R) (List.Tot.tl v))
    (PPB.pts_to_parsed (parse_nlist n p) input #pm v)

let nlist_hd_tl_post
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (n: pos)
  (input: slice byte)
  (pm: perm)
  (v: (nlist n t))
  (hd_tl: (slice byte & slice byte))
: slprop
= nlist_hd_tl_post' p sq n input pm v (fst hd_tl) (snd hd_tl)

inline_for_extraction
fn nlist_hd_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns res : (slice byte & slice byte)
ensures
  nlist_hd_tl_post p sq n input pm v res
{
  PPB.pts_to_parsed_elim input;
  with w . assert (pts_to input #pm w);
  parse_nlist_eq (Ghost.reveal n) p w;
  parser_kind_prop_equiv k p;
  let off = j input 0sz;
  let input1, input2 = split_trade input off;
  with w1 . assert (pts_to input1 #pm w1);
  with w2 . assert (pts_to input2 #pm w2);
  parse_strong_prefix p w w1;
  let vh = Ghost.hide (List.Tot.hd (Ghost.reveal v));
  let vt : Ghost.erased (nlist (n - 1) t) = Ghost.hide (List.Tot.tl (Ghost.reveal v));
  PPB.pts_to_parsed_intro p input1 vh;
  PPB.pts_to_parsed_intro (parse_nlist (n - 1) p) input2 vt;
  // Trade chain: (parsed hd ** parsed tl) -> (pts_to input1 ** pts_to input2) -> (pts_to input) -> (parsed nlist)
  Trade.prod
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh)
    (pts_to input1 #pm w1)
    (PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input2 #pm w2);
  Trade.trans
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh ** PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input1 #pm w1 ** pts_to input2 #pm w2)
    (pts_to input #pm w);
  // Use existing trade from pts_to_parsed_elim: (pts_to input #pm w) -> (parsed nlist)
  Trade.trans
    (PPB.pts_to_parsed p input1 #(pm /. 2.0R) vh ** PPB.pts_to_parsed (parse_nlist (n - 1) p) input2 #(pm /. 2.0R) vt)
    (pts_to input #pm w)
    (PPB.pts_to_parsed (parse_nlist n p) input #pm v);
  rewrite each vh as (List.Tot.hd (Ghost.reveal v));
  rewrite each vt as (List.Tot.tl (Ghost.reveal v));
  fold (nlist_hd_tl_post' p sq n input pm v input1 input2);
  fold (nlist_hd_tl_post p sq n input pm v (input1, input2));
  (input1, input2)
}

(* nlist_hd: get head element sub-slice *)

inline_for_extraction
fn nlist_hd
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns input' : slice byte
ensures exists* v' .
  PPB.pts_to_parsed p input' #(pm /. 2.0R) v' **
  trade (PPB.pts_to_parsed p input' #(pm /. 2.0R) v') (PPB.pts_to_parsed (parse_nlist n p) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.hd v
  )
{
  let (hd, tl) = nlist_hd_tl sq j n input;
  unfold (nlist_hd_tl_post p sq n input pm v (hd, tl));
  unfold (nlist_hd_tl_post' p sq n input pm v hd tl);
  Trade.elim_hyp_r _ _ _;
  hd
}

(* nlist_tl: get tail sub-slice *)

inline_for_extraction
fn nlist_tl
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n: Ghost.erased pos)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist n t))
requires
  PPB.pts_to_parsed (parse_nlist n p) input #pm v
returns input' : slice byte
ensures exists* v' .
  PPB.pts_to_parsed (parse_nlist (n - 1) p) input' #(pm /. 2.0R) v' **
  trade (PPB.pts_to_parsed (parse_nlist (n - 1) p) input' #(pm /. 2.0R) v') (PPB.pts_to_parsed (parse_nlist n p) input #pm v) **
  pure (
    Cons? v /\
    v' == List.Tot.tl v
  )
{
  let (hd, tl) = nlist_hd_tl sq j n input;
  unfold (nlist_hd_tl_post p sq n input pm v (hd, tl));
  unfold (nlist_hd_tl_post' p sq n input pm v hd tl);
  Trade.elim_hyp_l _ _ _;
  tl
}

(* Validator combinators *)

let parse_consume (#k: Ghost.erased parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: GTot (option nat)
= match parse p b with
  | Some (_, consumed) -> Some consumed
  | None -> None

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_nlist
  (n: SZ.t)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: LPS.validator p)
: LPS.validator #(nlist (SZ.v n) t) #(parse_nlist_kind (SZ.v n) k) (parse_nlist (SZ.v n) p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  pts_to_len input;
  let mut pcontinue = true;
  let mut pcount = n;
  while (
    let c = !pcontinue;
    let r = !pcount;
    (c && SZ.gt r 0sz)
  ) invariant exists* c r off .
    R.pts_to pcontinue c **
    R.pts_to pcount r **
    R.pts_to poffset off **
    pts_to input #pm v_bytes **
    pure (
      SZ.v off <= Seq.length v_bytes /\
      SZ.v r <= SZ.v n /\ (
      let s0 = Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes) in
      let s = Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes) in
      Some? (parse (parse_nlist (SZ.v n) p) s0) == (c && Some? (parse (parse_nlist (SZ.v r) p) s)) /\
      (Some? (parse (parse_nlist (SZ.v n) p) s0) ==>
        (SZ.v offset + snd (Some?.v (parse (parse_nlist (SZ.v n) p) s0)) ==
         SZ.v off + snd (Some?.v (parse (parse_nlist (SZ.v r) p) s))))
    ))
  {
    let off = !poffset;
    let r = !pcount;
    parse_nlist_eq (SZ.v r) p (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    let is_valid = v input poffset;
    if is_valid {
      pcount := SZ.sub r 1sz
    } else {
      pcontinue := false
    }
  };
  let c = !pcontinue;
  if c {
    let off = !poffset;
    parse_nlist_eq 0 p (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    true
  } else {
    false
  }
}

#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lv: LPS.validator lp)
  (lr: PPB.leaf_reader lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (w: LPS.validator p)
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.validator #(vlarray t (U32.v min) (U32.v max)) #(parse_vclist_kind (U32.v min) (U32.v max) lk k) (parse_vclist (U32.v min) (U32.v max) lp p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vclist_eq (U32.v min) (U32.v max) lp p sinput;
  let offset_val = !poffset;
  let is_valid_len = lv input poffset;
  if is_valid_len {
    let off = !poffset;
    let count = PPB.read_parsed_from_validator_success lr input offset_val off;
    if (U32.lt count min || U32.lt max count) {
      false
    } else {
      SZ.fits_u64_implies_fits_32 ();
      let n = SZ.uint32_to_sizet count;
      let consumed_n = Ghost.hide (SZ.v off - SZ.v offset);
      Seq.lemma_eq_elim
        (Seq.slice sinput consumed_n (Seq.length sinput))
        (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
      validate_nlist n w input poffset
    }
  } else {
    false
  }
}
#pop-options

#push-options "--z3rlimit 32"

inline_for_extraction
fn jump_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max } )
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
  (lr: PPB.leaf_reader lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: LPS.jumper p)
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
: LPS.jumper #(vlarray t (U32.v min) (U32.v max)) #(parse_vclist_kind (U32.v min) (U32.v max) lk k) (parse_vclist (U32.v min) (U32.v max) lp p)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  parse_vclist_eq (U32.v min) (U32.v max) lp p sinput;
  pts_to_len input;
  let off1 = lj input offset;
  let count = PPB.read_parsed_from_validator_success lr input offset off1;
  SZ.fits_u64_implies_fits_32 ();
  let n = SZ.uint32_to_sizet count;
  Seq.lemma_eq_elim
    (Seq.slice sinput (SZ.v off1 - SZ.v offset) (Seq.length sinput))
    (Seq.slice v_bytes (SZ.v off1) (Seq.length v_bytes));
  LPV.jump_nlist j n input off1
}

#pop-options

(* nlist_nth: access the i-th element of an nlist *)

ghost fn trade_trans_nounify
  (a1 a2 a2' a3: slprop)
requires
  trade a1 a2 ** trade a2' a3 ** pure (a2 == a2')
ensures
  trade a1 a3
{
  rewrite each a2' as a2;
  Trade.trans a1 a2 a3
}

let nlist_nth_inv
  (#t: Type0)
  (n0: Ghost.erased nat)
  (v0: list t)
  (i0: SZ.t)
  (i: SZ.t)
  (n: nat)
  (v: list t)
: Tot prop
= SZ.v i0 < n0 /\
  SZ.v i <= SZ.v i0 /\
  n == n0 - SZ.v i /\
  List.Tot.length v0 == Ghost.reveal n0 /\
  List.Tot.length v == n /\
  List.Tot.index v0 (SZ.v i0) == List.Tot.index v (SZ.v i0 - SZ.v i)

inline_for_extraction
fn nlist_nth
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n0: Ghost.erased nat)
  (input: slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist n0 t))
  (i0: SZ.t { SZ.v i0 < n0 })
requires
  PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0
returns input' : slice byte
ensures exists* v' pm' .
  PPB.pts_to_parsed p input' #pm' v' **
  trade (PPB.pts_to_parsed p input' #pm' v') (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0) **
  pure (v' == List.Tot.index v0 (SZ.v i0))
{
  Trade.refl (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0);
  let mut pi = 0sz;
  let mut pres = input;
  while (
    let i = !pi;
    (SZ.lt i i0)
  ) invariant exists* i res (n: nat) (v: nlist n t) pm' . (
    R.pts_to pi i ** R.pts_to pres res **
    PPB.pts_to_parsed (parse_nlist n p) res #pm' v **
    trade (PPB.pts_to_parsed (parse_nlist n p) res #pm' v) (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0) **
    pure (
      nlist_nth_inv #t n0 v0 i0 i n v
    )
  ) {
    with 'res. assert R.pts_to pres 'res;
    let res = !pres;
    rewrite each 'res as res;
    let i = !pi;
    with v pm' . assert (PPB.pts_to_parsed (parse_nlist (n0 - SZ.v i) p) res #pm' v);
    let res2 = nlist_tl sq j (n0 - SZ.v i) res;
    pi := (SZ.add i 1sz);
    pres := res2;
    with v' pm'' . assert (PPB.pts_to_parsed (parse_nlist (n0 - SZ.v i - 1) p) res2 #pm'' v');
    trade_trans_nounify _ _ _
      (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0);
  };
  with 'res. assert R.pts_to pres 'res;
  let res = !pres;
  rewrite each 'res as res;
  let i = !pi;
  with v pm' . assert (PPB.pts_to_parsed (parse_nlist (n0 - SZ.v i) p) res #pm' v);
  let res2 = nlist_hd sq j (n0 - SZ.v i0) res;
  trade_trans_nounify
    _ _ _ (PPB.pts_to_parsed (parse_nlist n0 p) input #pm v0);
  res2
}

(* accessor_nlist_nth: accessor for the i-th element of an nlist *)

include LowParse.CLens

let clens_nlist_nth (#t: Type) (n: nat) (i: nat { i < n })
: Tot (clens (nlist n t) t)
= {
  clens_cond = (fun _ -> True);
  clens_get = (fun (v: nlist n t) -> List.Tot.index v i);
}

inline_for_extraction
fn accessor_nlist_nth
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (j: LPS.jumper p)
  (n0: Ghost.erased nat)
  (i0: SZ.t { SZ.v i0 < n0 })
: PPB.accessor (parse_nlist n0 p) p (clens_nlist_nth n0 (SZ.v i0))
=
  (input: S.slice byte)
  (#pm: perm)
  (#v0: Ghost.erased (nlist n0 t))
{
  let res = nlist_nth sq j n0 input i0;
  with v' pm' . assert (PPB.pts_to_parsed p res #pm' v');
  res
}

(* accessor_vclist_payload: accessor from vclist to nlist *)

module L = FStar.List.Tot
module LPC = LowParse.Pulse.Combinators

let clens_vclist_payload
  (min: nat)
  (max: nat { min <= max })
  (#t: Type)
  (n: Ghost.erased nat)
: Tot (clens (vlarray t min max) (nlist (Ghost.reveal n) t))
= {
  clens_cond = (fun (l: vlarray t min max) -> L.length l == Ghost.reveal n);
  clens_get = (fun (l: vlarray t min max) ->
    (l <: Ghost (nlist (Ghost.reveal n) t) (requires (L.length l == Ghost.reveal n)) (ensures fun _ -> True)));
}

let synth_vclist_dtuple2_injective
  (min: nat)
  (max: nat { min <= max })
  (#t: Type)
: Lemma (synth_injective (parse_vclist_dtuple2_synth min max #t))
= ()

let synth_vclist_dtuple2_recip
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#t: Type)
  (x: vlarray t min max)
: GTot (dtuple2 (bounded_count min max) (fun (n: bounded_count min max) -> nlist (U32.v n) t))
= (| U32.uint_to_t (L.length x), x |)

let synth_vclist_dtuple2_inverse
  (min: nat)
  (max: nat { min <= max /\ max < 4294967296 })
  (#t: Type)
: Lemma (synth_inverse (parse_vclist_dtuple2_synth min max #t) (synth_vclist_dtuple2_recip min max #t))
= ()

inline_for_extraction
let mk_jump_vclist_tag
  (min: Ghost.erased nat)
  (max: Ghost.erased nat { min <= max })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
: LPS.jumper (parse_vclist_dtuple2_tag_parser min max lp)
= LPC.jump_synth (LPC.jump_filter lj (bounded_count_prop min max)) (synth_bounded_count min max)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"

inline_for_extraction
fn accessor_vclist_payload
  (min: Ghost.erased nat)
  (max: Ghost.erased nat { min <= max /\ max < 4294967296 })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (n: Ghost.erased nat)
  (sq: squash (lk.parser_kind_subkind == Some ParserStrong /\
    LPS.pts_to_serialized_ext_trade_gen_precond
      (parse_vclist min max lp p)
      (parse_synth
        (parse_dtuple2
          (parse_vclist_dtuple2_tag_parser min max lp)
          (parse_vclist_dtuple2_payload_parser min max p))
        (parse_vclist_dtuple2_synth min max #t))))
: PPB.accessor
    (parse_vclist min max lp p)
    (parse_nlist (Ghost.reveal n) p)
    (clens_vclist_payload min max n)
=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (vlarray t min max))
{
  (* Step 1: ghost reinterpret as parse_synth parse_dtuple2 synth *)
  PPB.pts_to_parsed_ext_trade_gen
    (parse_synth
      (parse_dtuple2
        (parse_vclist_dtuple2_tag_parser min max lp)
        (parse_vclist_dtuple2_payload_parser min max p))
      (parse_vclist_dtuple2_synth min max #t))
    input;
  with v1 . assert (PPB.pts_to_parsed
    (parse_synth
      (parse_dtuple2
        (parse_vclist_dtuple2_tag_parser min max lp)
        (parse_vclist_dtuple2_payload_parser min max p))
      (parse_vclist_dtuple2_synth min max #t))
    input #pm v1);

  (* Step 2: ghost unwrap synth *)
  synth_vclist_dtuple2_injective min max #t;
  synth_vclist_dtuple2_inverse min max #t;
  PPC.pts_to_parsed_synth_l2r_trade
    (parse_dtuple2
      (parse_vclist_dtuple2_tag_parser min max lp)
      (parse_vclist_dtuple2_payload_parser min max p))
    (parse_vclist_dtuple2_synth min max #t)
    (synth_vclist_dtuple2_recip min max #t)
    input;
  with v2 . assert (PPB.pts_to_parsed
    (parse_dtuple2
      (parse_vclist_dtuple2_tag_parser min max lp)
      (parse_vclist_dtuple2_payload_parser min max p))
    input #pm v2);
  Trade.trans _ _ (PPB.pts_to_parsed (parse_vclist min max lp p) input #pm v);

  (* Step 3: accessor_dtuple2_snd — jump past the tag *)
  let gbc : Ghost.erased (bounded_count min max) = Ghost.hide (dfst v2);
  let s3 = PPC.accessor_dtuple2_snd
    (mk_jump_vclist_tag min max lj)
    (parse_vclist_dtuple2_payload_parser min max p)
    gbc
    ()
    input;
  Trade.trans _ _ (PPB.pts_to_parsed (parse_vclist min max lp p) input #pm v);

  (* Step 4: ghost reinterpret weakened nlist as parse_nlist *)
  with v3 pm3 . assert (PPB.pts_to_parsed
    (parse_vclist_dtuple2_payload_parser min max p (Ghost.reveal gbc))
    s3 #pm3 v3);
  PPB.pts_to_parsed_ext_trade_gen (parse_nlist n p) s3;
  with v4 . assert (PPB.pts_to_parsed (parse_nlist n p) s3 #pm3 v4);
  Trade.trans
    (PPB.pts_to_parsed (parse_nlist n p) s3 #pm3 v4)
    (PPB.pts_to_parsed (parse_vclist_dtuple2_payload_parser min max p (Ghost.reveal gbc)) s3 #pm3 v3)
    (PPB.pts_to_parsed (parse_vclist min max lp p) input #pm v);
  s3
}

#pop-options

(* ============================================================================ *)
(* Copyful parser + free for vclist                                             *)
(* ============================================================================ *)

module SM = Pulse.Lib.SeqMatch
module V = Pulse.Lib.Vec
module Seq = FStar.Seq

unfold let vclist_lowtype (el: Type0) = option (SZ.t & V.vec el)

let vmatch_vclist
  (#el #eh: Type0)
  (elem_vmatch: el -> eh -> slprop)
  (x: option (SZ.t & V.vec el))
  (l: list eh)
: slprop
= match x with
  | None -> pure (l == [])
  | Some nv -> exists* (s: Seq.seq el).
      V.pts_to (snd nv) s ** SM.seq_list_match s l elem_vmatch **
      pure (V.is_full_vec (snd nv) /\ Seq.length s == L.length l /\ SZ.v (fst nv) == L.length l /\ L.length l > 0)

(* pure helpers *)

let nil_of_length_zero (#a: Type) (l: list a)
: Lemma (requires L.length l == 0) (ensures l == [])
= ()

let rec splitAt_index_hd_vc (#a:Type) (i:nat) (l:list a)
  : Lemma (requires i < L.length l)
    (ensures (L.lemma_splitAt_snd_length i l; L.hd (snd (L.splitAt i l)) == L.index l i))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_index_hd_vc (i-1) xs)

let rec splitAt_tl_vc (#a:Type) (i:nat) (l:list a)
  : Lemma (requires i < L.length l)
    (ensures (L.lemma_splitAt_snd_length i l; L.tl (snd (L.splitAt i l)) == snd (L.splitAt (i+1) l)))
    (decreases i)
  = if i = 0 then ()
    else (match l with x :: xs -> splitAt_tl_vc (i-1) xs)

(* copyful_parse_nlist: fill a Vec from a parsed nlist of runtime-known positive length *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn copyful_parse_nlist
  (#eh: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k eh)
  (#el: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (w: PPB.copyful_parse elem_vmatch p)
  (j: LPS.jumper p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (gn: Ghost.erased nat)
  (n: SZ.t { SZ.v n == Ghost.reveal gn /\ Ghost.reveal gn > 0 })
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (nlist (Ghost.reveal gn) eh))
requires
  PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn) p) input #pm v
returns vec: V.vec el
ensures
  PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn) p) input #pm v **
  (exists* (s: Seq.seq el).
    V.pts_to vec s **
    SM.seq_list_match s (Ghost.reveal v <: list eh) elem_vmatch **
    pure (V.is_full_vec vec /\ Seq.length s == Ghost.reveal gn))
{
  let fl : Ghost.erased (list eh) = Ghost.hide (Ghost.reveal v <: list eh);
  let sl : Ghost.erased (Seq.seq eh) = Ghost.hide (Seq.seq_of_list (Ghost.reveal fl));
  (* seed element 0 *)
  let (hd0, tl0) = nlist_hd_tl sq j (Ghost.hide (Ghost.reveal gn <: pos)) input;
  unfold (nlist_hd_tl_post p sq (Ghost.reveal gn) input pm v (hd0, tl0));
  unfold (nlist_hd_tl_post' p sq (Ghost.reveal gn) input pm v hd0 tl0);
  let el0 = w hd0;
  let vec = V.alloc el0 n;
  V.pts_to_len vec;
  Seq.lemma_seq_of_list_index (Ghost.reveal fl) 0;
  rewrite (elem_vmatch el0 (List.Tot.hd (Ghost.reveal v)))
    as (elem_vmatch el0 (L.index (Ghost.reveal fl) 0));
  SM.seq_seq_match_singleton_intro elem_vmatch (Seq.create (SZ.v n) el0) (Ghost.reveal sl) 0 el0 (L.index (Ghost.reveal fl) 0);
  Trade.elim_hyp_l
    (PPB.pts_to_parsed p hd0 #(pm /. 2.0R) (List.Tot.hd (Ghost.reveal v)))
    (PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn - 1) p) tl0 #(pm /. 2.0R) (List.Tot.tl (Ghost.reveal v)))
    (PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn) p) input #pm v);
  splitAt_tl_vc 0 (Ghost.reveal fl);
  let mut pi = 1sz;
  let mut pcur = tl0;
  while (let i = !pi; SZ.lt i n)
  invariant exists* i cur pm_cur (m: nat) (rem: nlist m eh) (s1: Seq.seq el).
    R.pts_to pi i ** R.pts_to pcur cur **
    PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem **
    Trade.trade
      (PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem)
      (PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn) p) input #pm v) **
    V.pts_to vec s1 **
    SM.seq_seq_match elem_vmatch s1 (Ghost.reveal sl) 0 (SZ.v i) **
    pure (
      1 <= SZ.v i /\ SZ.v i <= SZ.v n /\
      m == Ghost.reveal gn - SZ.v i /\
      Seq.length s1 == SZ.v n /\
      (Ghost.reveal rem <: list eh) == snd (L.splitAt (SZ.v i) (Ghost.reveal fl)) /\
      L.length (Ghost.reveal rem) == m
    )
  {
    let i = !pi;
    let cur = !pcur;
    with pm_cur m rem s1.
      assert (PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem **
              V.pts_to vec s1 **
              SM.seq_seq_match elem_vmatch s1 (Ghost.reveal sl) 0 (SZ.v i));
    let (hd, tl) = nlist_hd_tl sq j (Ghost.hide (m <: pos)) cur;
    unfold (nlist_hd_tl_post p sq m cur pm_cur rem (hd, tl));
    unfold (nlist_hd_tl_post' p sq m cur pm_cur rem hd tl);
    let elx = w hd;
    V.op_Array_Assignment vec i elx;
    with s1'. assert (V.pts_to vec s1');
    SM.seq_seq_match_rewrite_seq elem_vmatch s1 s1' (Ghost.reveal sl) (Ghost.reveal sl) 0 (SZ.v i);
    splitAt_index_hd_vc (SZ.v i) (Ghost.reveal fl);
    Seq.lemma_seq_of_list_index (Ghost.reveal fl) (SZ.v i);
    splitAt_tl_vc (SZ.v i) (Ghost.reveal fl);
    rewrite (elem_vmatch elx (List.Tot.hd (Ghost.reveal rem)))
      as (elem_vmatch (Seq.index s1' (SZ.v i)) (Seq.index (Ghost.reveal sl) (SZ.v i)));
    SM.seq_seq_match_enqueue_right elem_vmatch s1' (Ghost.reveal sl) 0 (SZ.v i) (Seq.index s1' (SZ.v i)) (Seq.index (Ghost.reveal sl) (SZ.v i));
    Trade.elim_hyp_l
      (PPB.pts_to_parsed p hd #(pm_cur /. 2.0R) (List.Tot.hd (Ghost.reveal rem)))
      (PPB.pts_to_parsed (parse_nlist (m - 1) p) tl #(pm_cur /. 2.0R) (List.Tot.tl (Ghost.reveal rem)))
      (PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem);
    Trade.trans
      (PPB.pts_to_parsed (parse_nlist (m - 1) p) tl #(pm_cur /. 2.0R) (List.Tot.tl (Ghost.reveal rem)))
      (PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem)
      (PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn) p) input #pm v);
    pcur := tl;
    pi := SZ.add i 1sz;
  };
  let i = !pi;
  let cur = !pcur;
  with pm_cur m rem s_final.
    assert (PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem **
            V.pts_to vec s_final **
            SM.seq_seq_match elem_vmatch s_final (Ghost.reveal sl) 0 (SZ.v i));
  Trade.elim
    (PPB.pts_to_parsed (parse_nlist m p) cur #pm_cur rem)
    (PPB.pts_to_parsed (parse_nlist (Ghost.reveal gn) p) input #pm v);
  SM.seq_seq_match_seq_list_match elem_vmatch s_final (Ghost.reveal fl);
  vec
}

#pop-options

let nlist_length_fact (#t: Type) (n: nat) (l: nlist n t)
: Lemma (L.length (l <: list t) == n)
= ()

(* Helper to introduce vmatch_vclist on the Some (nonempty) case.
   The high-level list is taken as an opaque erased parameter so that
   folding the match-based predicate typechecks (a transparent
   refinement-typed list term triggers a spurious well-foundedness
   guard during fold elaboration). *)
inline_for_extraction
fn vmatch_vclist_some_intro
  (#el #eh: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (n: SZ.t)
  (vec: V.vec el)
  (#s: Ghost.erased (Seq.seq el))
  (#l: Ghost.erased (list eh))
  (l_out: Ghost.erased (list eh))
requires
  V.pts_to vec s ** SM.seq_list_match s l elem_vmatch **
  pure (V.is_full_vec vec /\ Seq.length s == L.length l /\ SZ.v n == L.length l /\
        L.length l > 0 /\ Ghost.reveal l == Ghost.reveal l_out)
returns r: vclist_lowtype el
ensures
  vmatch_vclist elem_vmatch r (Ghost.reveal l_out) **
  pure (r == Some (Ghost.reveal n, vec))
{
  fold (vmatch_vclist elem_vmatch (Some (n, vec)) (Ghost.reveal l));
  rewrite (vmatch_vclist elem_vmatch (Some (n, vec)) (Ghost.reveal l))
    as (vmatch_vclist elem_vmatch (Some (n, vec)) (Ghost.reveal l_out));
  Some (n, vec)
}

(* copyful_parse_vclist *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn copyful_parse_vclist
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max })
  (#lk: Ghost.erased parser_kind)
  (#lp: parser lk U32.t)
  (lj: LPS.jumper lp)
  (lr: PPB.leaf_reader lp)
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#el: Type0)
  (#elem_vmatch: el -> t -> slprop)
  (w: PPB.copyful_parse elem_vmatch p)
  (j: LPS.jumper p)
  (sq: squash (k.parser_kind_subkind == Some ParserStrong))
  (u: squash (lk.parser_kind_subkind == Some ParserStrong /\ FStar.SizeT.fits_u64))
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased (vlarray t (U32.v min) (U32.v max)))
requires
  PPB.pts_to_parsed (parse_vclist (U32.v min) (U32.v max) lp p) input #pm v
returns res: vclist_lowtype el
ensures
  PPB.pts_to_parsed (parse_vclist (U32.v min) (U32.v max) lp p) input #pm v **
  vmatch_vclist elem_vmatch res (Ghost.reveal v)
{
  (* read the runtime element count from the length prefix *)
  PPB.pts_to_parsed_elim input;
  with w_bytes. assert (S.pts_to input #pm w_bytes);
  pts_to_len input;
  Seq.lemma_eq_elim (Seq.slice w_bytes 0 (Seq.length w_bytes)) w_bytes;
  parse_vclist_eq (U32.v min) (U32.v max) lp p w_bytes;
  let off1 = lj input 0sz;
  let count = PPB.read_parsed_from_validator_success lr input 0sz off1;
  SZ.fits_u64_implies_fits_32 ();
  let n = SZ.uint32_to_sizet count;
  assert (pure (U32.v count == L.length (Ghost.reveal v)));
  Trade.elim
    (S.pts_to input #pm w_bytes)
    (PPB.pts_to_parsed (parse_vclist (U32.v min) (U32.v max) lp p) input #pm v);
  if (SZ.gt n 0sz) {
    (* nonempty: get the nlist payload slice, then fill the Vec *)
    Classical.forall_intro (parse_vclist_dtuple2_eq (U32.v min) (U32.v max) lp p);
    let payload = accessor_vclist_payload (U32.v min) (U32.v max) lj #k #t #p (Ghost.hide (U32.v count)) () input;
    with pm3 v3. assert (PPB.pts_to_parsed (parse_nlist (U32.v count) p) payload #pm3 v3);
    let vec = copyful_parse_nlist w j sq (Ghost.hide (U32.v count)) n payload;
    Trade.elim
      (PPB.pts_to_parsed (parse_nlist (U32.v count) p) payload #pm3 v3)
      (PPB.pts_to_parsed (parse_vclist (U32.v min) (U32.v max) lp p) input #pm v);
    nlist_length_fact (U32.v count) v3;
    let vh : Ghost.erased (list t) = Ghost.hide (Ghost.reveal v <: list t);
    assert (pure ((v3 <: list t) == Ghost.reveal vh));
    let res = vmatch_vclist_some_intro n vec vh;
    rewrite (vmatch_vclist elem_vmatch res (Ghost.reveal vh))
      as (vmatch_vclist elem_vmatch res (Ghost.reveal v));
    res
  } else {
    (* empty list *)
    nil_of_length_zero (Ghost.reveal v <: list t);
    let res : vclist_lowtype el = None #(SZ.t & V.vec el);
    fold (vmatch_vclist elem_vmatch (None #(SZ.t & V.vec el)) (Ghost.reveal v <: list t));
    rewrite (vmatch_vclist elem_vmatch (None #(SZ.t & V.vec el)) (Ghost.reveal v <: list t))
      as (vmatch_vclist elem_vmatch res (Ghost.reveal v));
    res
  }
}

#pop-options

(* free_vclist *)

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
fn free_vclist
  (#eh #el: Type0)
  (#elem_vmatch: el -> eh -> slprop)
  (free_elem: PPB.free_t elem_vmatch)
: PPB.free_t #(vclist_lowtype el) #(list eh) (vmatch_vclist elem_vmatch)
=
  (x: vclist_lowtype el)
  (#v: Ghost.erased (list eh))
{
  match x {
    None -> {
      unfold (vmatch_vclist elem_vmatch (None #(SZ.t & V.vec el)) (Ghost.reveal v));
    }
    Some y -> {
      unfold (vmatch_vclist elem_vmatch (Some y) (Ghost.reveal v));
      let nn = fst y;
      with s. assert (V.pts_to (snd y) s ** SM.seq_list_match s (Ghost.reveal v) elem_vmatch);
      V.pts_to_len (snd y);
      SM.seq_list_match_length elem_vmatch s (Ghost.reveal v);
      SM.seq_list_match_seq_seq_match elem_vmatch s (Ghost.reveal v);
      let mut pi = 0sz;
      while (let i = !pi; SZ.lt i nn)
      invariant exists* i. R.pts_to pi i ** V.pts_to (snd y) s **
        SM.seq_seq_match elem_vmatch s (Seq.seq_of_list (Ghost.reveal v)) (SZ.v i) (L.length (Ghost.reveal v)) **
        pure (SZ.v i <= SZ.v nn /\ Seq.length s == SZ.v nn /\ L.length (Ghost.reveal v) == SZ.v nn)
      {
        let i = !pi;
        SM.seq_seq_match_dequeue_left elem_vmatch s (Seq.seq_of_list (Ghost.reveal v)) (SZ.v i) (L.length (Ghost.reveal v));
        let elem = V.op_Array_Access (snd y) i;
        free_elem elem;
        pi := SZ.add i 1sz;
      };
      SM.seq_seq_match_empty_elim elem_vmatch s (Seq.seq_of_list (Ghost.reveal v)) (L.length (Ghost.reveal v));
      V.free (snd y);
    }
  }
}

#pop-options
