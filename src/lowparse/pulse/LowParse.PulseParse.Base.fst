module LowParse.PulseParse.Base
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base
module LPS = LowParse.Pulse.Base

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module S = Pulse.Lib.Slice

let pts_to_parsed_prop
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (w: Seq.seq byte)
  (v: t)
: Tot prop
= match parse p w with
  | None -> False
  | Some (v', consumed) -> v' == v /\
    consumed == Seq.length w

let pts_to_parsed
  (#k: parser_kind) (#t: Type) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  exists* w . S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v)

ghost fn pts_to_parsed_intro
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#pm: perm)
  (#w: Seq.seq byte)
  (v: t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v)
ensures
  pts_to_parsed p input #(pm /. 2.0R) v **
  Trade.trade
    (pts_to_parsed p input #(pm /. 2.0R) v)
    (S.pts_to input #pm w)
{
  S.share input;
  fold (pts_to_parsed p input #(pm /. 2.0R) v);
  intro
    (Trade.trade
      (pts_to_parsed p input #(pm /. 2.0R) v)
      (S.pts_to input #pm w)
    )
    #((S.pts_to input #(pm /. 2.0R) w))
    fn _ {
      unfold (pts_to_parsed p input #(pm /. 2.0R) v);
      S.gather input
    };
}

ghost fn pts_to_parsed_intro_injective
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (#w: Seq.seq byte)
  (v: t)
requires
  S.pts_to input #pm w **
  pure (pts_to_parsed_prop p w v /\
    k.parser_kind_injective == true
  )
ensures
  pts_to_parsed p input #(pm) v **
  Trade.trade
    (pts_to_parsed p input #(pm) v)
    (S.pts_to input #pm w)
{
  fold (pts_to_parsed p input #(pm) v);
  intro
    (Trade.trade
      (pts_to_parsed p input #(pm) v)
      (S.pts_to input #pm w)
    )
    #emp
    fn _ {
      unfold (pts_to_parsed p input #(pm) v);
      with w' . assert (S.pts_to input #pm w');
      parse_injective p w w';
      assert pure (Seq.equal w w')
    };
}

ghost fn pts_to_parsed_elim
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (#pm: perm)
  (#v: t)
  (input: slice byte)
requires
  pts_to_parsed p input #(pm) v
ensures exists* w .
  S.pts_to input #pm w **
  Trade.trade
    (S.pts_to input #pm w)
    (pts_to_parsed p input #(pm) v) **
  pure (pts_to_parsed_prop p w v)
{
  unfold (pts_to_parsed p input #(pm) v);
  with w . assert (S.pts_to input #pm w);
  intro
    (Trade.trade
      (S.pts_to input #pm w)
      (pts_to_parsed p input #(pm) v)
    )
    #emp
    fn _ {
      fold (pts_to_parsed p input #(pm) v);
    };
}

ghost fn pts_to_parsed_ext
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_parsed p1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_parsed p2 input #pm v
{
  unfold (pts_to_parsed p1 input #pm v);
  fold (pts_to_parsed p2 input #pm v)
}

ghost fn pts_to_parsed_ext_trade
  (#t: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (input: slice byte)
  (#pm: perm)
  (#v: t)
  requires pts_to_parsed p1 input #pm v ** pure (
    forall x . parse p1 x == parse p2 x
  )
  ensures pts_to_parsed p2 input #pm v **
    Trade.trade
      (pts_to_parsed p2 input #pm v)
      (pts_to_parsed p1 input #pm v)
{
    pts_to_parsed_ext p2 input;
    intro
      (Trade.trade
        (pts_to_parsed p2 input #pm v)
        (pts_to_parsed p1 input #pm v)
      )
      #emp
      fn _ {
        pts_to_parsed_ext p1 input
      }
}

ghost fn pts_to_parsed_ext_gen
  (#t1: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#t2:Type0)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v1: t1)
  requires pts_to_parsed p1 input #pm v1 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* (v2: t2) . pts_to_parsed p2 input #pm v2 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_post t1 t2 v1 v2
  )
{
  unfold (pts_to_parsed p1 input #pm v1);
  fold (pts_to_parsed p2 input #pm v1)
}

ghost fn pts_to_parsed_ext_trade_gen
  (#t1: Type0)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (#t2:Type0)
  (#k2: parser_kind)
  (p2: parser k2 t2)
  (input: slice byte)
  (#pm: perm)
  (#v1: t1)
  requires pts_to_parsed p1 input #pm v1 ** pure (
    LPS.pts_to_serialized_ext_trade_gen_precond p1 p2
  )
  ensures exists* (v2: t2) . pts_to_parsed p2 input #pm v2 **
    Trade.trade
      (pts_to_parsed p2 input #pm v2)
      (pts_to_parsed p1 input #pm v1) **
    pure (
      LPS.pts_to_serialized_ext_trade_gen_post t1 t2 v1 v2
    )
{
  pts_to_parsed_ext_gen p2 input;
  with v2 . assert (pts_to_parsed p2 input #pm v2);
  intro
    (Trade.trade
      (pts_to_parsed p2 input #pm v2)
      (pts_to_parsed p1 input #pm v1)
    )
    #emp
    fn _ {
      pts_to_parsed_ext_gen p1 input;
      with v1' . rewrite (pts_to_parsed p1 input #pm v1')
        as (pts_to_parsed p1 input #pm v1)
    }
}

ghost fn pts_to_serialized_parsed
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (#s: serializer p)
  (#v: t)
  (#pm: perm)
  (input: S.slice byte)
requires
  LPS.pts_to_serialized s input #pm v
ensures
  pts_to_parsed p input #pm v **
  Trade.trade
    (pts_to_parsed p input #pm v)
    (LPS.pts_to_serialized s input #pm v)
{
  LPS.pts_to_serialized_elim_trade s input;
  pts_to_parsed_intro_injective p input v;
  Trade.trans (pts_to_parsed p input #pm v) _ _
}

ghost fn pts_to_parsed_serialized
  (#k: parser_kind) (#t: Type0) (#p: parser k t)
  (s: serializer p)
  (#v: t)
  (#pm: perm)
  (input: S.slice byte)
requires
  pts_to_parsed p input #pm v
ensures
  LPS.pts_to_serialized s input #pm v **
  Trade.trade
    (LPS.pts_to_serialized s input #pm v)
    (pts_to_parsed p input #pm v)
{
  pts_to_parsed_elim input;
  with w . assert (S.pts_to input #pm w);
  parse_injective p w (serialize s v);
  LPS.pts_to_serialized_intro_trade s input v;
  Trade.trans (LPS.pts_to_serialized s input #pm v) _ _
}

let pts_to_parsed_strong_prefix_prop
  (#k: parser_kind) (#t: Type) (p: parser k t)
  (w: Seq.seq byte)
  (v: t)
: Tot prop
= k.parser_kind_subkind == Some ParserStrong /\
  begin match parse p w with
  | None -> False
  | Some (v', consumed) -> v' == v
  end

let pts_to_parsed_strong_prefix
  (#k: parser_kind) (#t: Type) (p: parser k t)
  ([@@@mkey]input: slice byte)
  (#[exact (`1.0R)] pm: perm)
  (v: t)
: slprop =
  exists* v' .
  S.pts_to input #pm v' **
  pure (
    pts_to_parsed_strong_prefix_prop p v' v
  )

ghost fn pts_to_parsed_strong_prefix_intro
  (#k: parser_kind) (#t: Type0) (p: parser k t)
  (input: slice byte)
  (#pm: perm)
  (v: t)
  (#v': bytes)
requires
  S.pts_to input #pm v' **
  pure (
    pts_to_parsed_strong_prefix_prop p v' v
  )
ensures
  pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v **
  Trade.trade
    (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v)
    (S.pts_to input #pm v')
{
  S.share input;
  fold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
  intro
    (Trade.trade
      (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v)
      (S.pts_to input #pm v')
    )
    #(S.pts_to input #(pm /. 2.0R) v')
    fn _ {
      unfold (pts_to_parsed_strong_prefix p input #(pm /. 2.0R) v);
      S.gather input
    };
}

module R = Pulse.Lib.Reference

inline_for_extraction
let leaf_reader
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t (pts_to_parsed p input #pm v) (fun res ->
    pts_to_parsed p input #pm v **
    pure (res == Ghost.reveal v)
  )

inline_for_extraction
let reader
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  (t': Type0) ->
  (f: ((x: t { x == Ghost.reveal v }) -> Tot t')) ->
  stt t' (pts_to_parsed p input #pm v) (fun x' -> pts_to_parsed p input #pm v ** pure (x' == f v))

inline_for_extraction
fn leaf_reader_of_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: reader p)
: leaf_reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  r input #pm #v t id
}

inline_for_extraction
fn reader_of_leaf_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: leaf_reader p)
: reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  let x = r input #pm #v;
  f x
}

inline_for_extraction
fn leaf_reader_of_serialized
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: LPS.leaf_reader s)
: leaf_reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  pts_to_parsed_serialized s input;
  let res = r input;
  pts_to_serialized_parsed input;
  Trade.trans (pts_to_parsed p input #pm v) (LPS.pts_to_serialized s input #pm v) (pts_to_parsed p input #pm v);
  Trade.elim (pts_to_parsed p input #pm v) (pts_to_parsed p input #pm v);
  res
}

inline_for_extraction
fn serialized_of_leaf_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (s: serializer p)
  (r: leaf_reader p)
: LPS.leaf_reader #t #k #p s
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
{
  pts_to_serialized_parsed input;
  let res = r input;
  pts_to_parsed_serialized s input;
  Trade.trans (LPS.pts_to_serialized s input #pm v) (pts_to_parsed p input #pm v) (LPS.pts_to_serialized s input #pm v);
  Trade.elim (LPS.pts_to_serialized s input #pm v) (LPS.pts_to_serialized s input #pm v);
  res
}

inline_for_extraction
fn reader_of_serialized
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (r: LPS.reader s)
: reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  pts_to_parsed_serialized s input;
  let res = r input #pm #v t' f;
  pts_to_serialized_parsed input;
  Trade.trans (pts_to_parsed p input #pm v) (LPS.pts_to_serialized s input #pm v) (pts_to_parsed p input #pm v);
  Trade.elim (pts_to_parsed p input #pm v) (pts_to_parsed p input #pm v);
  res
}

inline_for_extraction
fn read_parsed_from_validator_success
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t {k.parser_kind_subkind == Some ParserStrong})
  (r: leaf_reader p)
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  requires (pts_to input #pm v ** pure (LPS.validator_success #k #t p offset v (off)))
  returns v' : t
  ensures pts_to input #pm v ** pure (
    LPS.validator_success #k #t p offset v off /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v off - SZ.v offset)
  )
{
  parser_kind_prop_equiv k p;
  let input1, input23 = split_trade input offset;
  with v23 . assert (pts_to input23 #pm v23);
  Trade.elim_hyp_l (pts_to input1 #pm _) (pts_to input23 #pm v23) _;
  let consumed = SZ.sub off offset;
  let input2, input3 = split_trade input23 consumed;
  with v2 . assert (pts_to input2 #pm v2);
  Trade.elim_hyp_r (pts_to input2 #pm v2) (pts_to input3 #pm _) (pts_to input23 #pm v23);
  Trade.trans (pts_to input2 #pm v2) (pts_to input23 #pm _) (pts_to input #pm _);
  let gv1 = Ghost.hide (fst (Some?.v (parse p v23)));
  parse_strong_prefix p v23 v2;
  pts_to_parsed_intro p input2 gv1;
  let res = r input2;
  Trade.elim (pts_to_parsed p input2 #(pm /. 2.0R) gv1) (pts_to input2 #pm v2);
  Trade.elim (pts_to input2 #pm v2) (pts_to input #pm v);
  res
}

inline_for_extraction
fn ifthenelse_reader
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (cond: bool)
  (iftrue: squash (cond == true) -> reader p)
  (iffalse: squash (cond == false) -> reader p)
: reader #t #k p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  if cond {
    iftrue () input #pm #v t' f
  } else {
    iffalse () input #pm #v t' f
  }
}

inline_for_extraction
fn reader_ext
  (#t: Type0)
  (#k1: Ghost.erased parser_kind)
  (#p1: parser k1 t)
  (r1: reader p1)
  (#k2: Ghost.erased parser_kind)
  (p2: parser k2 t { forall x . parse p1 x == parse p2 x })
: reader #t #k2 p2
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  (t': Type0)
  (f: _)
{
  pts_to_parsed_ext_trade p1 input;
  let res = r1 input #pm #v t' f;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn peek_trade_gen
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t {k.parser_kind_subkind == Some ParserStrong})
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  requires (pts_to input #pm v ** pure (LPS.validator_success #k #t p offset v off))
  returns input': slice byte
  ensures exists* v' . pts_to_parsed p input' #(pm /. 2.0R) v' ** Trade.trade (pts_to_parsed p input' #(pm /. 2.0R) v') (pts_to input #pm v) ** pure (
    LPS.validator_success #k #t p offset v off /\
    parse p (Seq.slice v (SZ.v offset) (Seq.length v)) == Some (v', SZ.v off - SZ.v offset)
  )
{
  parser_kind_prop_equiv k p;
  let input1, input23 = split_trade input offset;
  with v23 . assert (pts_to input23 #pm v23);
  Trade.elim_hyp_l (pts_to input1 #pm _) (pts_to input23 #pm v23) _;
  let consumed = SZ.sub off offset;
  let input2, input3 = split_trade input23 consumed;
  with v2 . assert (pts_to input2 #pm v2);
  Trade.elim_hyp_r (pts_to input2 #pm v2) (pts_to input3 #pm _) (pts_to input23 #pm v23);
  Trade.trans (pts_to input2 #pm v2) (pts_to input23 #pm _) (pts_to input #pm _);
  let gv1 = Ghost.hide (fst (Some?.v (parse p v23)));
  parse_strong_prefix p v23 v2;
  pts_to_parsed_intro p input2 gv1;
  Trade.trans (pts_to_parsed p input2 #(pm /. 2.0R) gv1) (pts_to input2 #pm v2) (pts_to input #pm v);
  input2
}

(* zero_copy_parse: PulseParse version using pts_to_parsed instead of pts_to_serialized *)

let pts_to_parsed_with_perm
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (input: LPS.with_perm (S.slice byte))
  (v: t)
: Tot slprop
= pts_to_parsed p input.v #input.p v

inline_for_extraction
let zero_copy_parse
  (#t' #t: Type0)
  (vmatch: t' -> t -> slprop)
  (#k: parser_kind)
  (p: parser k t)
=
  (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t) ->
  stt t'
    (pts_to_parsed p input #pm v)
    (fun res ->
      vmatch res v **
      Trade.trade
        (vmatch res v)
        (pts_to_parsed p input #pm v)
    )

inline_for_extraction
fn zero_copy_parse_id
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
: zero_copy_parse #_ #_ (pts_to_parsed_with_perm p) #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = { LPS.v = input; LPS.p = pm };
  Trade.rewrite_with_trade
    (pts_to_parsed p input #pm v)
    (pts_to_parsed_with_perm p res v);
  res
}

inline_for_extraction
fn zero_copy_parse_lens
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: zero_copy_parse vmatch1 p)
  (#t2': Type0)
  (#vmatch2: t2' -> t -> slprop)
  (lens: LPS.vmatch_lens vmatch1 vmatch2)
: zero_copy_parse #_ #_ vmatch2 #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let tmp = r input;
  let res = lens tmp _;
  Trade.trans (vmatch2 res _) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_read
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: leaf_reader p)
: zero_copy_parse #_ #_ (LPS.eq_as_slprop t) #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  let res = r input;
  fold (LPS.eq_as_slprop t res v);
  intro (Trade.trade (LPS.eq_as_slprop t res v) (pts_to_parsed p input #pm v)) #(pts_to_parsed p input #pm v) fn _{
    unfold (LPS.eq_as_slprop t res v)
  };
  res
}

inline_for_extraction
fn zero_copy_parse_ignore
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
: zero_copy_parse #_ #_ (LPS.vmatch_ignore #t) #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  fold (LPS.vmatch_ignore () (Ghost.reveal v));
  intro (Trade.trade (LPS.vmatch_ignore () (Ghost.reveal v)) (pts_to_parsed p input #pm v)) #(pts_to_parsed p input #pm v) fn _{
    unfold (LPS.vmatch_ignore () (Ghost.reveal v))
  };
  ()
}

inline_for_extraction
fn zero_copy_parse_ext
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (r: zero_copy_parse vmatch1 p)
  (#k': Ghost.erased parser_kind)
  (p': parser k' t {
    forall b . parse p b == parse p' b
  })
: zero_copy_parse #_ #_ vmatch1 #_ p'
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  pts_to_parsed_ext_trade p input;
  let res = r input;
  Trade.trans (vmatch1 res v) _ _;
  res
}

inline_for_extraction
fn zero_copy_parse_ifthenelse
  (#t1'  #t: Type0)
  (#vmatch1: t1' -> t -> slprop)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t)
  (cond: bool)
  (rtrue: squash (cond == true) -> zero_copy_parse vmatch1 p)
  (rfalse: squash (cond == false) -> zero_copy_parse vmatch1 p)
: zero_copy_parse #_ #_ vmatch1 #_ p
=
  (input: slice byte)
  (#pm: perm)
  (#v: Ghost.erased _)
{
  if (cond) {
    rtrue () input
  } else {
    rfalse () input
  }
}

include LowParse.CLens

inline_for_extraction
let accessor
  (#k1: parser_kind) (#t1: Type0) (p1: parser k1 t1)
  (#k2: parser_kind) (#t2: Type0) (p2: parser k2 t2)
  (cl: clens t1 t2)
: Tot Type
= (input: slice byte) ->
  (#pm: perm) ->
  (#v: Ghost.erased t1) ->
  stt (slice byte)
    (pts_to_parsed p1 input #pm v ** pure (cl.clens_cond v))
    (fun result -> exists* v2 pm' .
      pts_to_parsed p2 result #pm' v2 **
      pure (cl.clens_cond v /\ v2 == cl.clens_get v) **
      Trade.trade
        (pts_to_parsed p2 result #pm' v2)
        (pts_to_parsed p1 input #pm v))
