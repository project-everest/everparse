module ASN1.Spec.Set

module LPL = LowParse.Spec.List
module LPC = LowParse.Spec.Combinators

let rec gsorted (f: ('a -> 'a -> GTot bool)) (l: list 'a) : GTot bool =
  match l with
  | []
  | [_] -> true
  | x::y::tl -> f x y && gsorted f (y::tl)

let rec sorted_gsorted // sanity-check
  (#a: Type)
  (f: (a -> a -> Tot bool))
  (l: list a)
: Lemma
  (FStar.List.Tot.sorted f l == gsorted f l)
= match l with
  | [] -> ()
  | [_] -> ()
  | x::y::tl -> sorted_gsorted f (y :: tl)

let repr_order_prop
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPC.parser k t)
  (x1 x2: t)
: Tot prop
=
  (exists b1 . match LPC.parse p b1 with None -> False | Some (x1', _) -> x1' == x1) /\
  (exists b2 . match LPC.parse p b2 with None -> False | Some (x2', _) -> x2' == x2) /\
  (forall b1 b2 .
    match LPC.parse p b1, LPC.parse p b2 with
    | Some (x1', consumed1), Some (x2', consumed2) ->
      (x1' == x1 /\ x2' == x2) ==>
      Seq.slice b1 0 consumed1 `byte_order` Seq.slice b2 0 consumed2
    | _ -> True
  )

let repr_order_spec
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPC.parser k t)
  (x1 x2: t)
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (repr_order_prop byte_order p x1 x2)

let parse_byte_sorted_list_filter
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPC.parser k t)
  (x: list t)
: GTot bool
= gsorted (repr_order_spec byte_order p) x

let synth_byte_sorted_list
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPC.parser k t)
  (x: LPC.parse_filter_refine (parse_byte_sorted_list_filter byte_order p))
: Tot (list t)
= x

let parse_byte_sorted_list
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPC.parser k t)
: Tot (LPC.parser (LPC.parse_filter_kind (LPL.parse_list_kind k.LPC.parser_kind_injective)) (list t))
= LPL.parse_list p `LPC.parse_filter` parse_byte_sorted_list_filter byte_order p `LPC.parse_synth` synth_byte_sorted_list byte_order p

module LPT = LowParse.Tot.Base

let rec tot_parse_byte_sorted_list_aux
  (tot_byte_order: (LPC.bytes -> LPC.bytes -> bool))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPT.parser k t)
  (previous_bytes: LPT.bytes)
  (b: LPT.bytes)
: Tot (option (list t & LPT.consumed_length b))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then Some ([], 0)
  else match p b with
  | None -> None
  | Some (a, consumed1) ->
    if consumed1 = 0
    then None
    else
      let current_bytes = Seq.slice b 0 consumed1 in
      if tot_byte_order previous_bytes current_bytes
      then begin
        let b' = Seq.slice b consumed1 (Seq.length b) in
        match tot_parse_byte_sorted_list_aux tot_byte_order p current_bytes b' with
        | None -> None
        | Some (q, consumed2) -> Some (a::q, consumed1 + consumed2)
      end
      else None

let repr_order_prop_intro
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPC.parser k t)
  (x1 x2: t)
  (b1 b2: LPC.bytes)
: Lemma
  (requires (
    k.LPC.parser_kind_injective == true /\
    begin match p b1, p b2 with
    | Some (x1', consumed1), Some (x2', consumed2) ->
      x1' == x1 /\
      x2' == x2
    | _ -> False
    end
  ))
  (ensures (
    let Some (_, consumed1) = p b1 in
    let Some (_, consumed2) = p b2 in
    byte_order (Seq.slice b1 0 consumed1) (Seq.slice b2 0 consumed2) <==> repr_order_prop byte_order p x1 x2
  ))
= 
  let Some (_, consumed1) = p b1 in
  let Some (_, consumed2) = p b2 in
  let prf
    (b1' b2' : LPC.bytes)
  : Lemma
    (match LPC.parse p b1', LPC.parse p b2' with
    | Some (x1', consumed1'), Some (x2', consumed2') ->
      (x1' == x1 /\ x2' == x2) ==> (
        (Seq.slice b1 0 consumed1 `byte_order` Seq.slice b2 0 consumed2) <==>
        (Seq.slice b1' 0 consumed1' `byte_order` Seq.slice b2' 0 consumed2')
      )
    | _ -> True)
  = match LPC.parse p b1', LPC.parse p b2' with
    | Some (x1', _), Some (x2', _) ->
      if FStar.StrongExcludedMiddle.strong_excluded_middle (x1' == x1 /\ x2' == x2)
      then begin
        LPC.parse_injective p b1 b1';
        LPC.parse_injective p b2 b2'
      end
      else ()
    | _ -> ()
  in
  Classical.forall_intro_2 prf

#push-options "--z3rlimit 16"
#restart-solver

let rec tot_parse_byte_sorted_list_aux_correct
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (tot_byte_order: ((x: LPC.bytes) -> (y: LPC.bytes) -> Pure bool True (fun z -> z == true <==> byte_order x y)))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPT.parser k t)
  (previous_bytes: LPT.bytes)
  (b: LPT.bytes)
: Lemma
  (requires (
    k.LPC.parser_kind_injective == true /\
    k.parser_kind_subkind == Some LPC.ParserStrong /\
    begin match LPC.parse p previous_bytes with
    | None -> False
    | Some (_, consumed_hd) -> consumed_hd <> 0 /\ consumed_hd == Seq.length previous_bytes
    end
  ))
  (ensures (
    match parse_byte_sorted_list byte_order #_ #k p (previous_bytes `Seq.append` b), tot_parse_byte_sorted_list_aux tot_byte_order p previous_bytes b with
    | None, None -> True
    | Some (x, consumed), Some (tot_x, tot_consumed) ->
      x == fst (Some?.v (LPC.parse p previous_bytes)) :: tot_x /\
      consumed == Seq.length previous_bytes + tot_consumed
    | _ -> False
  ))
  (decreases (Seq.length b))
= let Some (hd, consumed_hd) = p previous_bytes in
  let b0 = previous_bytes `Seq.append` b in
  LPC.parse_synth_eq
    (LPC.parse_filter (LPL.parse_list #k p) (parse_byte_sorted_list_filter byte_order #_ #k p))
    (synth_byte_sorted_list byte_order #_ #k p)
    b0;
  LPC.parse_filter_eq
    (LPL.parse_list #k p)
    (parse_byte_sorted_list_filter byte_order #_ #k p)
    b0;
  LPL.parse_list_eq #k p b0;
  LPC.parse_strong_prefix #k p previous_bytes b0;
  assert (b `Seq.equal` Seq.slice b0 consumed_hd (Seq.length b0));
  LPL.parse_list_eq #k p b;
  LPC.parse_filter_eq
    (LPL.parse_list #k p)
    (parse_byte_sorted_list_filter byte_order #_ #k p)
    b;
  LPC.parse_synth_eq
    (LPC.parse_filter (LPL.parse_list #k p) (parse_byte_sorted_list_filter byte_order #_ #k p))
    (synth_byte_sorted_list byte_order #_ #k p)
    b;
  if Seq.length b = 0
  then ()
  else match p b with
  | None -> ()
  | Some (elt, consumed1) ->
    if consumed1 = 0
    then ()
    else begin
      repr_order_prop_intro byte_order #_ #k p hd elt previous_bytes b;
      let current_bytes = Seq.slice b 0 consumed1 in
      LPC.parse_strong_prefix #k p b current_bytes;
      if tot_byte_order previous_bytes current_bytes
      then begin
        let b' = Seq.slice b consumed1 (Seq.length b) in
        assert ((current_bytes `Seq.append` b') `Seq.equal` b);
        tot_parse_byte_sorted_list_aux_correct byte_order tot_byte_order p current_bytes b';
        ()
      end
      else ()
    end

#pop-options

let tot_parse_byte_sorted_list_bare
  (tot_byte_order: (LPC.bytes -> LPC.bytes -> bool))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPT.parser k t)
  (b: LPT.bytes)
: Tot (option (list t & LPT.consumed_length b))
= if Seq.length b = 0
  then Some ([], 0)
  else match p b with
  | None -> None
  | Some (hd, consumed1) ->
    if consumed1 = 0
    then None
    else begin
      let current_bytes = Seq.slice b 0 consumed1 in
      let b' = Seq.slice b consumed1 (Seq.length b) in
      match tot_parse_byte_sorted_list_aux tot_byte_order p current_bytes b' with
      | None -> None
      | Some (tl, consumed2) -> Some (hd::tl, consumed1 + consumed2)
    end

let tot_parse_byte_sorted_list_correct
  (byte_order: (LPC.bytes -> LPC.bytes -> prop))
  (tot_byte_order: ((x: LPC.bytes) -> (y: LPC.bytes) -> Pure bool True (fun z -> z == true <==> byte_order x y)))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPT.parser k t {k.LPC.parser_kind_injective == true /\ k.parser_kind_subkind == Some LPC.ParserStrong})
  (b: LPT.bytes)
: Lemma
  (ensures (
    parse_byte_sorted_list byte_order #_ #k p b == tot_parse_byte_sorted_list_bare tot_byte_order p b
  ))
=
  LPC.parse_synth_eq
    (LPC.parse_filter (LPL.parse_list #k p) (parse_byte_sorted_list_filter byte_order #_ #k p))
    (synth_byte_sorted_list byte_order #_ #k p)
    b;
  LPC.parse_filter_eq
    (LPL.parse_list #k p)
    (parse_byte_sorted_list_filter byte_order #_ #k p)
    b;
  LPL.parse_list_eq #k p b;
  if Seq.length b = 0
  then ()
  else match p b with
  | None -> ()
  | Some (hd, consumed1) ->
    if consumed1 = 0
    then ()
    else begin
      let current_bytes = Seq.slice b 0 consumed1 in
      let b' = Seq.slice b consumed1 (Seq.length b) in
      assert (b `Seq.equal` (current_bytes `Seq.append` b'));
      LPC.parse_strong_prefix #k p b current_bytes;
      tot_parse_byte_sorted_list_aux_correct byte_order tot_byte_order p current_bytes b'
    end

let prop_order_of_bool_order
  (#t: Type)
  (bool_order: (t -> t -> bool))
  (x1 x2: t)
: Tot prop
= bool_order x1 x2 == true

let tot_parse_byte_sorted_list
  (byte_order: ((x: LPC.bytes) -> (y: LPC.bytes) -> bool))
  (#t: Type)
  (#k: LPC.parser_kind)
  (p: LPT.parser k t)
: Pure (LPT.parser (LPC.parse_filter_kind (LPL.parse_list_kind k.LPC.parser_kind_injective)) (list t))
    (requires k.LPC.parser_kind_injective == true /\ k.parser_kind_subkind == Some LPC.ParserStrong)
    (ensures (fun y -> forall x . y x == LPC.parse (parse_byte_sorted_list (prop_order_of_bool_order byte_order) #_ #k p) x))
= Classical.forall_intro (tot_parse_byte_sorted_list_correct (prop_order_of_bool_order byte_order) (fun x1 x2 -> byte_order x1 x2) p);
  let p' = tot_parse_byte_sorted_list_bare (fun x1 x2 -> byte_order x1 x2) p in
  LPC.parser_kind_prop_ext
    (LPC.parse_filter_kind (LPL.parse_list_kind k.LPC.parser_kind_injective))
    (parse_byte_sorted_list (prop_order_of_bool_order byte_order) #_ #k p)
    p';
  p'

module A = ASN1.Base

let rec lex_byte_order'
  (n1: nat)
  (b1: Seq.lseq LPC.byte n1)
  (n2: nat)
  (b2: Seq.lseq LPC.byte n2)
: Tot bool
  (decreases (n1 + n2))
= if n1 = 0
  then true
  else if n2 = 0
  then false
  else
    let x1 = Seq.index b1 0 in
    let x2 = Seq.index b2 0 in
    if x1 `FStar.UInt8.lt` x2
    then true
    else if x2 `FStar.UInt8.lt` x1
    then false
    else lex_byte_order' (n1 - 1) (Seq.slice b1 1 n1) (n2 - 1) (Seq.slice b2 1 n2)

let lex_byte_order
  (b1: Seq.seq LPC.byte)
  (b2: Seq.seq LPC.byte)
: Tot bool
= lex_byte_order' (Seq.length b1) b1 (Seq.length b2) b2

let parse_asn1_set_of
  (#t: Type)
  (p: A.asn1_strong_parser t)
: Tot (A.asn1_weak_parser (list t))
= LPT.weaken _ (tot_parse_byte_sorted_list lex_byte_order p)
