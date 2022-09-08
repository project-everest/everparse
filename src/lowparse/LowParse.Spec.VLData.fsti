module LowParse.Spec.VLData
include LowParse.Spec.FLData
include LowParse.Spec.AllIntegers // for bounded_integer, in_bounds, etc.

module Seq = FStar.Seq
module U32 = FStar.UInt32
module M = LowParse.Math

#reset-options "--z3rlimit 64 --max_fuel 64 --max_ifuel 64 --z3refresh --z3cliopt smt.arith.nl=false"

let parse_vldata_payload_size
  (sz: integer_size)
: Pure nat
  (requires True)
  (ensures (fun y -> y == pow2 (FStar.Mul.op_Star 8 sz) - 1 ))
= match sz with
  | 1 -> 255
  | 2 -> 65535
  | 3 -> 16777215
  | 4 -> 4294967295

#reset-options

// unfold
let parse_vldata_payload_kind
  (sz: integer_size)
  (k: parser_kind)
: parser_kind
= strong_parser_kind 0 (parse_vldata_payload_size sz) (
    match k.parser_kind_metadata with
    | Some ParserKindMetadataFail -> Some ParserKindMetadataFail
    | _ -> None
  )

let parse_vldata_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (i: bounded_integer sz { f i == true } )
: Tot (parser (parse_vldata_payload_kind sz k) t)
= weaken (parse_vldata_payload_kind sz k) (parse_fldata p (U32.v i))

#set-options "--z3rlimit 64"

let parse_fldata_and_then_cases_injective
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vldata_payload sz f p))
= parser_kind_prop_equiv k p;
  let g
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1 b2: bytes)
  : Lemma
    (requires (and_then_cases_injective_precond (parse_vldata_payload sz f p) len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g'
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1: bytes)
  : Lemma
    (forall (b2: bytes) . and_then_cases_injective_precond (parse_vldata_payload sz f p) len1 len2 b1 b2 ==> len1 == len2)
  = Classical.forall_intro (Classical.move_requires (g len1 len2 b1))
  in
  Classical.forall_intro_3 g'

#reset-options

// unfold
let parse_vldata_gen_kind
  (sz: integer_size)
  (k: parser_kind)
: Tot parser_kind
= strong_parser_kind sz (sz + parse_vldata_payload_size sz) (
    match k.parser_kind_metadata with
    | Some ParserKindMetadataFail -> Some ParserKindMetadataFail
    | _ -> None
  )

let parse_vldata_gen_kind_correct
  (sz: integer_size)
  (k: parser_kind)
: Lemma
  ( (parse_vldata_gen_kind sz k) == (and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz k)))
= let kl = parse_vldata_gen_kind sz k in
  let kr = and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz k) in
  assert_norm (kl == kr)

val parse_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_vldata_gen_kind sz k) t)

val parse_vldata_gen_eq_def
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vldata_payload sz f p) /\
  parse_vldata_gen_kind sz k == and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz k) /\
  parse_vldata_gen sz f p ==
  and_then
    #_
    #(parse_filter_refine #(bounded_integer sz) f)
    (parse_filter #_ #(bounded_integer sz) (parse_bounded_integer sz) f)
    #_
    #t
    (parse_vldata_payload sz f p))

let parse_vldata_gen_eq
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (let res = parse (parse_vldata_gen sz f p) input in
    match parse (parse_bounded_integer sz) input with
  | None -> res == None
  | Some (len, consumed_len) ->
    consumed_len == sz /\ (
    if f len
    then begin
      if Seq.length input < sz + U32.v len
      then res == None
      else
      let input' = Seq.slice input sz (sz + U32.v len) in
      match parse p input' with
      | Some (x, consumed_x) ->
        if consumed_x = U32.v len
        then res == Some (x, sz + U32.v len)
        else res == None
      | _ -> res == None
    end
    else res == None
  ))
= parse_vldata_gen_eq_def sz f p;
  and_then_eq #_ #(parse_filter_refine f) (parse_filter (parse_bounded_integer sz) f) #_ #t (parse_vldata_payload sz f p) input;
  parse_filter_eq #_ #(bounded_integer sz) (parse_bounded_integer sz) f input;
  parser_kind_prop_equiv (parse_bounded_integer_kind sz) (parse_bounded_integer sz);
  ()

let parse_vldata_gen_eq_some_elim
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (requires (Some? (parse (parse_vldata_gen sz f p) input)))
  (ensures (
    let pbi = parse (parse_bounded_integer sz) input in
    Some? pbi /\ (
    let Some (len, consumed_len) = pbi in
    consumed_len == sz /\
    f len /\
    Seq.length input >= sz + U32.v len /\ (
    let input' = Seq.slice input sz (sz + U32.v len) in
    let pp = parse p input' in
    Some? pp /\ (
    let Some (x, consumed_x) = pp in
    consumed_x = U32.v len /\
    parse (parse_vldata_gen sz f p) input == Some (x, sz + U32.v len)
  )))))
= parse_vldata_gen_eq sz f p input

let unconstrained_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
: GTot bool
= true

let parse_vldata
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser _ t)
= parse_vldata_gen sz (unconstrained_bounded_integer sz) p

let parse_vldata_eq
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (input: bytes)
: Lemma
  (parse (parse_vldata sz p) input == (match parse (parse_bounded_integer sz) input with
  | None -> None
  | Some (len, _) ->
    begin
      if Seq.length input < sz + U32.v len
      then None
      else
      let input' = Seq.slice input sz (sz + U32.v len) in
      match parse p input' with
      | Some (x, consumed_x) ->
        if consumed_x = U32.v len
        then Some (x, sz + U32.v len)
        else None
      | _ -> None
    end
  ))
= parse_vldata_gen_eq sz (unconstrained_bounded_integer _) p input

(** Explicit bounds on size *)

#reset-options

inline_for_extraction
let parse_bounded_vldata_strong_kind
  (min: nat)
  (max: nat)
  (l: nat)
  (k: parser_kind)
: Pure parser_kind
  (requires (min <= max /\ max > 0 /\ max < 4294967296 /\ l >= log256' max /\ l <= 4 ))
  (ensures (fun _ -> True))
= [@inline_let]
  let kmin = k.parser_kind_low in
  [@inline_let]
  let min' = if kmin > min then kmin else min in
  [@inline_let]
  let max' = match k.parser_kind_high with
  | None -> max
  | Some kmax -> if kmax < max then kmax else max
  in
  [@inline_let]
  let max' = if max' < min' then min' else max' in
  (* the size of the length prefix must conform to the max bound given by the user, not on the metadata *)
  strong_parser_kind (l + min') (l + max') (
    match k.parser_kind_metadata with
    | Some ParserKindMetadataFail -> Some ParserKindMetadataFail
    | _ -> None
  )

let parse_bounded_vldata_elim'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (xbytes: bytes)
  (x: t)
  (consumed: consumed_length xbytes)
: Lemma
  (requires (parse (parse_vldata_gen l (in_bounds min max) p) xbytes == Some (x, consumed)))
  (ensures (
    let sz : integer_size = l in
    let plen = parse (parse_bounded_integer sz) xbytes in
    Some? plen /\ (
    let (Some (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Some? pp /\ (
    let (Some (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
= parse_vldata_gen_eq l (in_bounds min max) p xbytes;
  parser_kind_prop_equiv (parse_bounded_integer_kind l) (parse_bounded_integer l)

let parse_bounded_vldata_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Lemma
  (parser_kind_prop (parse_bounded_vldata_strong_kind min max l k) (parse_vldata_gen l (in_bounds min max) p))
= parser_kind_prop_equiv (parse_bounded_vldata_strong_kind min max l k) (parse_vldata_gen l (in_bounds min max) p);
  let sz : integer_size = l in
  let p' = parse_vldata_gen sz (in_bounds min max) p in
  parser_kind_prop_equiv (get_parser_kind p') p';
  parser_kind_prop_equiv k p;
  let k' = parse_bounded_vldata_strong_kind min max l k in
  let prf
    (input: bytes)
  : Lemma
    (requires (Some? (parse p' input)))
    (ensures (
      let pi = parse p' input in
      Some? pi /\ (
      let (Some (_, consumed)) = pi in
      k'.parser_kind_low <= (consumed <: nat) /\
      (consumed <: nat) <= Some?.v k'.parser_kind_high
    )))
  = let (Some (data, consumed)) = parse p' input in
    parse_bounded_vldata_elim' min max l p input data consumed
  in
  Classical.forall_intro (Classical.move_requires prf)

let parse_bounded_vldata'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_bounded_vldata_strong_kind min max l k) t)
= parse_bounded_vldata_correct min max l p;
  strengthen (parse_bounded_vldata_strong_kind min max l k) (parse_vldata_gen l (in_bounds min max) p)

let parse_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) k) t)
= parse_bounded_vldata' min max (log256' max) p

let parse_bounded_vldata_elim
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (xbytes: bytes)
  (x: t)
  (consumed: consumed_length xbytes)
: Lemma
  (requires (parse (parse_bounded_vldata' min max l p) xbytes == Some (x, consumed)))
  (ensures (
    let sz : integer_size = l in
    let plen = parse (parse_bounded_integer sz) xbytes in
    Some? plen /\ (
    let (Some (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Some? pp /\ (
    let (Some (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
= parse_bounded_vldata_elim' min max l p xbytes x consumed

let parse_bounded_vldata_elim_forall
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (xbytes: bytes)
: Lemma
  (requires (Some? (parse (parse_bounded_vldata' min max l p) xbytes)))
  (ensures (
    let (Some (x, consumed)) = parse (parse_bounded_vldata' min max l p) xbytes in
    let sz : integer_size = l in
    let plen = parse (parse_bounded_integer sz) xbytes in
    Some? plen /\ (
    let (Some (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Some? pp /\ (
    let (Some (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
= let (Some (x, consumed)) = parse (parse_bounded_vldata' min max l p) xbytes in
  parse_bounded_vldata_elim min max l p xbytes x consumed

(* Serialization *)

let parse_bounded_vldata_strong_pred
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: GTot Type0
= let reslen = Seq.length (s x) in
  min <= reslen /\ reslen <= max

let parse_bounded_vldata_strong_t
  (min: nat)
  (max: nat)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t { parse_bounded_vldata_strong_pred min max s x } )

let parse_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: t)
: Lemma
  (requires (parse (parse_bounded_vldata' min max l p) xbytes == Some (x, consumed)))
  (ensures (parse_bounded_vldata_strong_pred min max s x))
= parse_bounded_vldata_elim min max l p xbytes x consumed;
  let sz : integer_size = l in
  let plen = parse (parse_bounded_integer sz) xbytes in
  let f () : Lemma (Some? plen) =
    parse_bounded_vldata_elim min max l p xbytes x consumed
  in
  f ();
  let (Some (len, _)) = plen in
  let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
  assert (Seq.equal input' (Seq.slice input' 0 (U32.v len)));
  serializer_correct_implies_complete p s;
  assert (s x == input');
  ()

let parse_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (parser (parse_bounded_vldata_strong_kind min max l k) (parse_bounded_vldata_strong_t min max s)) 
= // strengthen (parse_bounded_vldata_strong_kind min max k)
  (
  coerce_parser
  (parse_bounded_vldata_strong_t min max s)
  (parse_strengthen (parse_bounded_vldata' min max l p) (parse_bounded_vldata_strong_pred min max s) (parse_bounded_vldata_strong_correct min max l s))
  )

let parse_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (parser (parse_bounded_vldata_strong_kind min max (log256' max) k) (parse_bounded_vldata_strong_t min max s)) 
= parse_bounded_vldata_strong' min max (log256' max) s

let serialize_bounded_vldata_strong_aux
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (bare_serializer (parse_bounded_vldata_strong_t min max s))
= (fun (x: parse_bounded_vldata_strong_t min max s) ->
  let pl = s x in
  let sz = l in
  let nlen = Seq.length pl in
  assert (min <= nlen /\ nlen <= max);
  let len = U32.uint_to_t nlen in
  let slen = serialize (serialize_bounded_integer sz) len in
  seq_slice_append_l slen pl;
  seq_slice_append_r slen pl;
  Seq.append slen pl
  )

let serialize_vldata_gen_correct_aux
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz) b1 in
    Some? vlen /\ (
    let (Some (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (_, consumed)) = vv in
    consumed == Seq.length b2 /\
    Seq.length b1 <= Seq.length b /\
    Seq.slice b 0 (Seq.length b1) == b1 /\
    Seq.slice b (Seq.length b1) (Seq.length b) == b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (v, consumed)) = vv in
    let vv' = parse (parse_vldata_gen sz f p) b in
    Some? vv' /\ (
    let (Some (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == Seq.length b
  )))) =
  let (Some (len, consumed1)) = parse (parse_bounded_integer sz) b1 in
  parser_kind_prop_equiv (parse_bounded_integer_kind sz) (parse_bounded_integer sz);
  assert (consumed1 == sz);
  assert (no_lookahead_on (parse_bounded_integer sz) b1 b);
  assert (injective_postcond (parse_bounded_integer sz) b1 b);
  assert (parse (parse_bounded_integer sz) b == Some (len, sz));
  assert (sz + U32.v len == Seq.length b);
  assert (b2 == Seq.slice b sz (sz + U32.v len));
  parse_vldata_gen_eq sz f p b

let serialize_vldata_gen_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz) b1 in
    Some? vlen /\ (
    let (Some (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (_, consumed)) = vv in
    consumed == Seq.length b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (v, consumed)) = vv in
    let vv' = parse (parse_vldata_gen sz f p) (Seq.append b1 b2) in
    Some? vv' /\ (
    let (Some (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == sz + Seq.length b2
  )))) =
  seq_slice_append_l b1 b2;
  seq_slice_append_r b1 b2;
  serialize_vldata_gen_correct_aux sz f p (Seq.append b1 b2) b1 b2

let serialize_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (input: parse_bounded_vldata_strong_t min max s)
: Lemma
  (let formatted = serialize_bounded_vldata_strong_aux min max l s input in
    parse (parse_bounded_vldata_strong' min max l s) formatted == Some (input, Seq.length formatted))
= let sz = l in
  let sp = serialize s input in
  let nlen = Seq.length sp in
  assert (min <= nlen /\ nlen <= max);
  let len = U32.uint_to_t nlen in
  M.pow2_le_compat (FStar.Mul.op_Star 8 sz)  (FStar.Mul.op_Star 8 (log256' max));
  assert (U32.v len < pow2 (FStar.Mul.op_Star 8 sz));
  let (len: bounded_integer sz) = len in
  let slen = serialize (serialize_bounded_integer sz) len in
  assert (Seq.length slen == sz);
  let pslen = parse (parse_bounded_integer sz) slen in
  assert (Some? pslen);
  let (Some (len', consumed_len')) = pslen in
  assert (len == len');
  assert (in_bounds min max len' == true);
  assert (Seq.length sp == U32.v len);
  let psp = parse p sp in
  assert (Some? psp);
  let (Some (_, consumed_p)) = psp in
  assert ((consumed_p <: nat) == Seq.length sp);
  serialize_vldata_gen_correct sz (in_bounds min max) p
    slen
    sp
  ;
  ()

let serialize_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (l: nat { l >= log256' max /\ l <= 4 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_bounded_vldata_strong' min max l s))
= Classical.forall_intro (serialize_bounded_vldata_strong_correct min max l s);
  serialize_bounded_vldata_strong_aux min max l s

let serialize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_bounded_vldata_strong min max s))
= serialize_bounded_vldata_strong' min max (log256' max) s

let serialize_bounded_vldata_precond
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (k: parser_kind)
: GTot bool
= match k.parser_kind_high with
  | None -> false
  | Some max' -> min <= k.parser_kind_low && max' <= max

let serialize_bounded_vldata_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { serialize_bounded_vldata_precond min max k } )
  (x: t)
: Lemma
  ( let Some (_, consumed) = parse p (serialize s x) in
    let y = serialize_bounded_vldata_strong_aux min max (log256' max) s (x <: parse_bounded_vldata_strong_t min max s) in
    parse (parse_bounded_vldata min max p) y == Some (x, Seq.length y))
= let Some (_, consumed) = parse p (serialize s x) in
  serialize_bounded_vldata_strong_correct min max (log256' max) s x;
  ()

let serialize_bounded_vldata'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { serialize_bounded_vldata_precond min max k } )
  (x: t)
: GTot (y: bytes { parse (parse_bounded_vldata min max p) y == Some (x, Seq.length y) } )
= let Some (_, consumed) = parse p (serialize s x) in
  serialize_bounded_vldata_correct min max s x;
  serialize_bounded_vldata_strong_aux min max (log256' max) s x

let serialize_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p  { serialize_bounded_vldata_precond min max k } )
: Tot (serializer (parse_bounded_vldata min max p))
= serialize_bounded_vldata' min max s

let serialize_bounded_vldata_strong_upd
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
: Lemma
  (requires (Seq.length (serialize s y) == Seq.length (serialize s x)))
  (ensures (
    let sy = serialize s y in
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length sy == Seq.length sx /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_seq sx lm sy
  ))
=   let y : parse_bounded_vldata_strong_t min max s = y in
    let sx = serialize s x in
    let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
    let sy = serialize s y in
    let sy' = serialize (serialize_bounded_vldata_strong min max s) y in
    let lm = log256' max in
    let sz = serialize (serialize_bounded_integer lm) (U32.uint_to_t (Seq.length sx)) in
    assert (lm + Seq.length sy == Seq.length sx');
    seq_upd_seq_right sx' sy;
    Seq.lemma_split sx' lm;
    Seq.lemma_split sy' lm;
    Seq.lemma_append_inj (Seq.slice sx' 0 lm) (Seq.slice sx' lm (Seq.length sx')) sz sx;
    Seq.lemma_append_inj (Seq.slice sy' 0 lm) (Seq.slice sy' lm (Seq.length sy')) sz sy;
    assert (sy' `Seq.equal` seq_upd_seq sx' lm sy)

let serialize_bounded_vldata_strong_upd_bw
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
: Lemma
  (requires (Seq.length (serialize s y) == Seq.length (serialize s x)))
  (ensures (
    let sy = serialize s y in
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length sy == Seq.length sx /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_bw_seq sx 0 sy
  ))
= serialize_bounded_vldata_strong_upd min max s x y

let serialize_bounded_vldata_strong_upd_chain
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_seq sx i' s'
  ))
  (ensures (
    parse_bounded_vldata_strong_pred min max s y /\ (
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length (serialize s x) == Seq.length sx' /\
    lm + i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_seq sx' (lm + i') s'
  )))
= serialize_bounded_vldata_strong_upd min max s x y;
  let sx = serialize s x in
  let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
  let lm = log256' max in
  let sz = serialize (serialize_bounded_integer lm) (U32.uint_to_t (Seq.length sx)) in
  seq_upd_seq_right_to_left sx' lm sx i' s';
  Seq.lemma_split sx' lm;
  Seq.lemma_append_inj (Seq.slice sx' 0 lm) (Seq.slice sx' lm (Seq.length sx')) sz sx;
  seq_upd_seq_seq_upd_seq_slice sx' lm (Seq.length sx') i' s'

#reset-options "--z3refresh --z3rlimit 32 --z3cliopt smt.arith.nl=false"

let serialize_bounded_vldata_strong_upd_bw_chain
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    parse_bounded_vldata_strong_pred min max s y /\ (
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length (serialize s x) == Seq.length sx' /\
    i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_bw_seq sx' i' s'
  )))
= serialize_bounded_vldata_strong_upd_chain min max s x y (Seq.length (serialize s x) - i' - Seq.length s') s'
