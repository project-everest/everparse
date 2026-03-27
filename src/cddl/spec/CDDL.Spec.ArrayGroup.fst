module CDDL.Spec.ArrayGroup

let array_group_concat_assoc
  (#b: _)
  (a1 a2 a3: array_group b)
: Lemma
  (array_group_concat a1 (array_group_concat a2 a3) `array_group_equiv`
    array_group_concat (array_group_concat a1 a2) a3)
  [SMTPatOr [
    [SMTPat (array_group_concat a1 (array_group_concat a2 a3))];
    [SMTPat (array_group_concat (array_group_concat a1 a2) a3)]
  ]]
= let prf
    (l: list Cbor.cbor { opt_precedes_list l b})
  : Lemma
    (array_group_concat a1 (array_group_concat a2 a3) l ==
      array_group_concat (array_group_concat a1 a2) a3 l)
  = match a1 l with
    | None -> ()
    | Some (l1, lr1) ->
      begin match a2 lr1 with
      | None -> ()
      | Some (l2, lr2) ->
        begin match a3 lr2 with
        | None -> ()
        | Some (l3, lr3) -> List.Tot.append_assoc l1 l2 l3
        end
      end
  in
  Classical.forall_intro prf

let array_group_concat_unique_strong_prop_intro
  #b (a1 a3: array_group b)
  (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  (l3 rem: list Cbor.cbor)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a3 /\
    (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l3, rem))
  ))
  (ensures (
      array_group_concat a1 a3 (l1 `List.Tot.append` l2) == Some (l1 `List.Tot.append` l3, rem)
  ))
= ()


let array_group_concat_unique_strong_prop_elim_gen
  #b (a1 a3: array_group b)
  (l: list Cbor.cbor { opt_precedes_list l b })
  (l' rem: list Cbor.cbor)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a3 /\
    array_group_concat a1 a3 l == Some (l', rem)
  ))
  (ensures (
      (exists (l1 l2 l3: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l3, rem) /\
        l' == l1 `List.Tot.append` l3
  )))
= ()

let array_group_concat_unique_strong_prop_elim
  #b (a1 a3: array_group b)
  (l: list Cbor.cbor { opt_precedes_list l b })
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a3 /\
    array_group_concat a1 a3 l == Some (l, [])
  ))
  (ensures (
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, []))
  ))
= array_group_concat_unique_strong_prop_elim_gen a1 a3 l l [];
  let Some (l1, l2) = a1 l in
  let Some (l3, _) = a3 l2 in
  List.Tot.append_l_nil l3

let array_group_concat_unique_strong_intro
  #b (a1 a3: array_group b)
: Lemma
  (requires (
    forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 l1 == Some (l1, []) <==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
  ))
  (ensures (
    array_group_concat_unique_strong a1 a3
  ))
= ()

let array_group_concat_unique_strong_elim1
  #b (a1 a3: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a3
  ))
  (ensures (
    forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 l1 == Some (l1, []) ==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
  ))
= ()

let indefinite_description_ghost3
  #t1 #t2 #t3
  (p: t1 -> t2 -> t3 -> prop)
: Ghost (t1 & t2 & t3)
    (requires (exists x1 x2 x3 . p x1 x2 x3))
    (ensures (fun (x1, x2, x3) -> p x1 x2 x3))
= let x1 = FStar.IndefiniteDescription.indefinite_description_ghost t1 (fun x1 -> exists x2 x3 . p x1 x2 x3) in
  let x2 = FStar.IndefiniteDescription.indefinite_description_ghost t2 (fun x2 -> exists x3 . p x1 x2 x3) in
  let x3 = FStar.IndefiniteDescription.indefinite_description_ghost t3 (fun x3 -> p x1 x2 x3) in
  (x1, x2, x3)

let array_group_concat_unique_strong_elim2
  #b (a1 a3: array_group b)
: Lemma
  (requires (array_group_concat_unique_strong a1 a3))
  (ensures (
    forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 (l1 `List.Tot.append` l2) == Some (l1, l2) ==> a1 l1 == Some (l1, []))
  ))
= let prf
      (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    ((Some? (a3 l2) /\ a1 (l1 `List.Tot.append` l2) == Some (l1, l2)) ==> a1 l1 == Some (l1, []))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (Some? (a3 l2) /\ a1 (l1 `List.Tot.append` l2) == Some ((l1 <: list _), (l2 <: list _)))
    then begin
      let Some (l3, rem) = a3 l2 in
      let l' = l1 `List.Tot.append` l3 in
      let l = l1 `List.Tot.append` l2 in
      array_group_concat_unique_strong_prop_elim_gen a1 a3 l l' rem
    end
  in
  Classical.forall_intro_2 prf

noextract
let array_group_concat_unique_strong'
  #b (a1 a3: array_group b)
: Tot prop
=
    forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
      Some? (a3 l2) ==> (a1 (l1 `List.Tot.append` l2) == Some (l1, l2) <==> a1 l1 == Some (l1, []))

let array_group_concat_unique_strong'_equiv
  #b (a1 a3: array_group b)
: Lemma
  (array_group_concat_unique_strong a1 a3 <==> array_group_concat_unique_strong' a1 a3)
  [SMTPat (array_group_concat_unique_strong a1 a3)]
= Classical.move_requires (array_group_concat_unique_strong_elim2 a1) a3

let array_group_strong_prefix_empty
  (b: option Cbor.cbor)
: Lemma
  (array_group_strong_prefix #b array_group_empty)
= ()

let array_group_strong_prefix_implies_concat_unique_strong
  #b (a1 a3: array_group b)
: Lemma
  (array_group_strong_prefix a1 ==> array_group_concat_unique_strong a1 a3)
= ()

let array_group_concat_unique_strong'_strong_prefix
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong' a1 a2 /\
    array_group_strong_prefix a2
  ))
  (ensures (
    array_group_strong_prefix (array_group_concat a1 a2)
  ))
= let a = array_group_concat a1 a2 in
  let prf
    (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (a l1 == Some (l1, []) ==> a (l1 `List.Tot.append` l2) == Some (l1, l2))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (a l1 == Some (l1, []))
    then begin
      let Some (l11, l12) = a1 l1 in
      List.Tot.append_assoc l11 l12 l2
    end
    else ()
  in
  Classical.forall_intro_2 prf

let array_group_concat_unique_strong_strong_prefix
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2 /\
    array_group_strong_prefix a2
  ))
  (ensures (
    array_group_strong_prefix (array_group_concat a1 a2)
  ))
= array_group_concat_unique_strong'_strong_prefix a1 a2

let array_group_concat_unique_strong_concat
  #b (a1 a2 a3: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong a1 (array_group_concat a2 a3)
  ))
= ()

let array_group_concat_unique_strong_choice_right #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_concat_unique_strong a1 a2 /\
    array_group_concat_unique_strong a1 a3
  ))
  (ensures (
    array_group_concat_unique_strong a1 (array_group_choice a2 a3)
  ))
= ()

let array_group_concat_unique_strong_choice_left #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_concat_unique_strong a1 a3 /\
    array_group_concat_unique_strong a2 a3 /\
    array_group_disjoint a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_choice a1 a2) a3
  ))
= ()

let array_group_disjoint_sym #b (a1 a2: array_group b) : Lemma
  (array_group_disjoint a1 a2 <==> array_group_disjoint a2 a1)
= ()

let array_group_disjoint_choice #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_disjoint a1 a3
  ))
  (ensures (
    array_group_disjoint a1 (array_group_choice a2 a3)
  ))
= ()

let array_group_disjoint_concat #b (a1 a2 a3: array_group b) : Lemma
  (requires (array_group_disjoint a1 a2))
  (ensures (array_group_disjoint a1 (array_group_concat a2 a3)))
= ()



let rec array_group_zero_or_more_some
  #b
  (a: array_group b)
  (l: list Cbor.cbor { opt_precedes_list l b })
: Lemma
  (ensures (Some? (array_group_zero_or_more a l)))
  (decreases List.Tot.length l)
  [SMTPat (array_group_zero_or_more a l)]
= match a l with
  | None -> ()
  | Some (l1, l2) ->
    List.Tot.append_length l1 l2;
    if Nil? l1
    then ()
    else array_group_zero_or_more_some a l2

let array_group_zero_or_more_equiv #b
 (a1 a2: array_group b)
: Lemma
  (requires array_group_equiv a1 a2)
  (ensures array_group_equiv (array_group_zero_or_more a1) (array_group_zero_or_more a2))
  [SMTPat (array_group_equiv (array_group_zero_or_more a1) (array_group_zero_or_more a2))]
= assert (array_group_equiv a1 a2);
  let rec phi
    (l: list Cbor.cbor { opt_precedes_list l b })
  : Lemma
    (ensures (array_group_zero_or_more a1 l == array_group_zero_or_more a2 l))
    (decreases (List.Tot.length l))
  = assert (a1 l == a2 l);
    match a1 l with
    | None -> ()
    | Some (l1, l2) ->
      List.Tot.append_length l1 l2;
      if Nil? l1
      then ()
      else phi l2
  in
  Classical.forall_intro phi

let array_group_concat_unique_strong_concat_zero_or_more_right
  #b (a1 a2 a3: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2 /\
    array_group_concat_unique_strong a1 a3
  ))
  (ensures (
    array_group_concat_unique_strong a1 (array_group_concat (array_group_zero_or_more a2) a3)
  ))
= ()

let array_group_concat_unique_strong_zero_or_more_right
  #b (a1 a2: array_group b)
: Lemma
  (ensures (
    array_group_concat_unique_strong a1 (array_group_zero_or_more a2) <==> array_group_strong_prefix a1
  ))
= ()

let array_group_concat_unique_strong'_zero_or_more_left
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong' a1 a1 /\
    array_group_concat_unique_strong' a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong' (array_group_zero_or_more a1) a2
  ))
= let _ : squash (array_group_disjoint a1 a2) = () in
  let rec prf
    (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (ensures (
      Some? (a2 l2) ==> (array_group_zero_or_more a1 l1 == Some (l1, []) <==> array_group_zero_or_more a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
    ))
    (decreases (List.Tot.length l1))
  = if Some? (a2 l2)
    then begin
      if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group_zero_or_more a1 l1 == Some (l1, []))
      then
        match a1 l1 with
        | None -> ()
        | Some (l1l, l1r) ->
          if Nil? l1l
          then ()
          else begin
            List.Tot.append_length l1l l1r;
            List.Tot.append_assoc l1l l1r l2;
            let Some (l1rl, l1rr) = array_group_zero_or_more a1 l1r in
            assert (Nil? l1rr);
            List.Tot.append_l_nil l1rl;
            prf l1r l2
          end
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group_zero_or_more a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
      then begin
        match a1 (l1 `List.Tot.append` l2) with
        | None -> ()
        | Some (l12l, l12r) ->
          let Some (l12rl, l12rr) = array_group_zero_or_more a1 l12r in
          assert (l12rr == l2);
          List.Tot.append_assoc l12l l12rl l2;
          List.Tot.append_length l12rl l12rr;
          List.Tot.append_length l12l l12r;
          List.Tot.append_length l1 l2;
          if Nil? l12l
          then ()
          else begin
            prf l12rl l2
          end
      end
    end
  in
  Classical.forall_intro_2 prf

let array_group_concat_unique_strong_zero_or_more_left
  #b (a1 a2: array_group b)
= array_group_concat_unique_strong'_zero_or_more_left a1 a2

let array_group_concat_unique_weak_intro
  #b (a1 a3: array_group b)
  (prf1:
    (l: (l: list Cbor.cbor { opt_precedes_list l b })) ->
    Lemma
    (requires array_group_concat a1 a3 l == Some (l, []))
    (ensures
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))
//    [SMTPat (array_group_concat a1 a3 l)]
  )
  (prf2:
    (l1: (l: list Cbor.cbor { opt_precedes_list l b })) ->
    (l2: (l: list Cbor.cbor { opt_precedes_list l b })) ->
    Lemma
    (requires
        a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])
    )
    (ensures       
      a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
    )
//    [SMTPat (a1 (l1 `List.Tot.append` l2))]
  )
: Lemma
  (array_group_concat_unique_weak a1 a3)
= let prf1'
    (l: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (array_group_concat a1 a3 l == Some (l, []) ==>
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))
  = Classical.move_requires prf1 l
  in
  Classical.forall_intro prf1';
  let prf2'
    (l1: (l: list Cbor.cbor { opt_precedes_list l b }))
    (l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    ((
        a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])
    ) ==>
    (
      a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
    ))
  = Classical.move_requires (prf2 l1) l2
  in
  Classical.forall_intro_2 prf2'

let array_group_concat_unique_strong_implies_weak
  #b (a1 a3: array_group b)
: Lemma
  (array_group_concat_unique_strong a1 a3 ==> array_group_concat_unique_weak a1 a3)
= ()

#push-options "--z3rlimit 128 --fuel 4 --ifuel 4"
#restart-solver

let array_group_concat_unique_weak_concat_zero_or_more_right
  #b (a1 a2 a3: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2 /\
    array_group_concat_unique_weak a1 a3
  ))
  (ensures (
    array_group_concat_unique_weak a1 (array_group_concat (array_group_zero_or_more a2) a3)
  ))
= ()

#pop-options

#push-options "--z3rlimit 32"
#restart-solver

let array_group_concat_unique_weak_zero_or_more_left'
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong' a1 a1 /\
    array_group_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_zero_or_more a1) a2
  ))
= let a10 = a1 in
  let a1 = array_group_zero_or_more a10 in
  let a3 = a2 in
  let rec prf2
    (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (ensures ((a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)))
    (decreases (List.Tot.length l1))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, []))
    then match a10 l1 with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        List.Tot.append_assoc l1l l1r l2;
        prf2 l1r l2
      end
  in
  let rec prf1
    (l: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (ensures (array_group_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))))
    (decreases (List.Tot.length l))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group_concat a1 a3 l == Some (l, []))
    then match a10 l with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        prf1 l1r;
        let Some (l2l, l2r) = a1 l1r in
        List.Tot.append_assoc l1l l2l l2r
      end
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

#pop-options

let array_group_concat_unique_weak_zero_or_more_left
  #b (a1 a2: array_group b)
= array_group_concat_unique_weak_zero_or_more_left' a1 (close_array_group a2)

let array_group_concat_unique_weak_zero_or_more_right
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak a1 (array_group_zero_or_more a2)
  ))
= ()

#push-options "--z3rlimit 32"
#restart-solver

let array_group_concat_unique_weak_zero_or_more'
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong' a1 a1 /\
    array_group_concat_unique_strong' a1 a2 /\
    array_group_disjoint a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_zero_or_more a1) (array_group_zero_or_more a2)
  ))
= let a10 = a1 in
  let a1 = array_group_zero_or_more a10 in
  let a3 = array_group_zero_or_more a2 in
  let rec prf2
    (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (ensures ((a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)))
    (decreases (List.Tot.length l1))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, []))
    then match a10 l1 with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        List.Tot.append_assoc l1l l1r l2;
        prf2 l1r l2
      end
  in
  let rec prf1
    (l: (l: list Cbor.cbor { opt_precedes_list l b }))
  : Lemma
    (ensures (array_group_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))))
    (decreases (List.Tot.length l))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (array_group_concat a1 a3 l == Some (l, []))
    then match a10 l with
    | None -> ()
    | Some (l1l, l1r) ->
      if Nil? l1l
      then ()
      else begin
        List.Tot.append_length l1l l1r;
        prf1 l1r;
        let Some (l2l, l2r) = a1 l1r in
        List.Tot.append_assoc l1l l2l l2r
      end
  in
  Classical.forall_intro prf1;
  Classical.forall_intro_2 prf2

#pop-options

let array_group_concat_unique_weak_zero_or_more
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_strong a1 a2 /\
    array_group_disjoint a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_zero_or_more a1) (array_group_zero_or_more a2)
  ))
= array_group_concat_unique_weak_zero_or_more' a1 a2

let array_group_concat_unique_weak_choice_right #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_concat_unique_weak a1 a2 /\
    array_group_concat_unique_weak a1 a3
  ))
  (ensures (
    array_group_concat_unique_weak a1 (array_group_choice a2 a3)
  ))
= ()

#push-options "--z3rlimit 16"

let array_group_concat_unique_strong'_concat_left
  (#b: _)
  (g1 g2 g3: array_group b)
: Lemma
  (requires
    array_group_concat_unique_strong' g1 (array_group_concat g2 g3) /\
    array_group_concat_unique_strong' g2 g3 /\
    array_group_concat_unique_weak g1 g2
  )
  (ensures
    array_group_concat_unique_strong' (array_group_concat g1 g2) g3
  )
= let a1 = array_group_concat g1 g2 in
  let a3 = g3 in
  let prf
    (l1 l2:
      (l: list Cbor.cbor { opt_precedes_list l b })
    )
  : Lemma
    (Some? (a3 l2) ==> (a1 (l1 `List.Tot.append` l2) == Some (l1, l2) <==> a1 l1 == Some (l1, [])))
  = if Some? (a3 l2)
    then begin
      if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
      then assert (a1 l1 == Some (l1, []))
      else if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 l1 == Some (l1, []))
      then begin
        let Some (lg1, lg2) = g1 l1 in
        assert (g1 lg1 == Some (lg1, []));
        assert (g2 lg2 == Some (lg2, []));
        List.Tot.append_assoc lg1 lg2 l2
      end
    end
  in
  Classical.forall_intro_2 prf

let array_group_concat_unique_strong_concat_left
  (#b: _)
  (g1 g2 g3: array_group b)
: Lemma
  (requires
    array_group_concat_unique_strong g1 (array_group_concat g2 g3) /\
    array_group_concat_unique_strong g2 g3 /\
    array_group_concat_unique_weak g1 g2
  )
  (ensures
    array_group_concat_unique_strong (array_group_concat g1 g2) g3
  )
= array_group_concat_unique_strong'_concat_left g1 g2 g3

#restart-solver
let array_group_concat_unique_strong_zero_or_one_left
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_zero_or_one a1) a2
  ))
= ()

let array_group_concat_unique_strong_one_or_more_left
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_one_or_more a1) a2
  ))
= array_group_concat_unique_weak_zero_or_more_right a1 a1;
  array_group_concat_unique_strong_zero_or_more_left a1 a2;
  array_group_concat_unique_strong_concat_left a1 (array_group_zero_or_more a1) a2

#pop-options

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver
let array_group_concat_unique_weak_one_or_more_left'
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_one_or_more a1) a2
  ))
= array_group_concat_unique_weak_concat_zero_or_more_right a1 a1 a2;
  array_group_concat_unique_weak_zero_or_more_left a1 a2;
  array_group_concat_unique_weak_intro (array_group_one_or_more a1) a2
      (fun l ->
        let Some (l1, lr) = a1 l in
        assert (array_group_concat (array_group_zero_or_more a1) a2 lr == Some (lr, []));
        let Some (l1s, l2) = array_group_zero_or_more a1 lr in
        assert (array_group_zero_or_more a1 l1s == Some (l1s, []));
        assert (a2 l2 == Some (l2, []));
        ()
      )
      (fun l1 l2 ->
        assert (Some? (a1 l1));
        assert (array_group_zero_or_more a1 l1 == Some (l1, []));
        let l = l1 `List.Tot.append` l2 in
        assert (array_group_concat (array_group_zero_or_more a1) a2 l == Some (l, []));
        assert (Some? (a1 l));
        ()
      )

let array_group_concat_unique_weak_one_or_more_left
  #b (a1 a2: array_group b)
= array_group_concat_unique_weak_one_or_more_left' a1 (close_array_group a2)

let array_group_concat_close
  (#b: _)
  (a1 a2: array_group b)
: Lemma
  (array_group_equiv
    (close_array_group (array_group_concat a1 a2))
    (array_group_concat a1 (close_array_group a2))
  )
= ()

#pop-options

let array_group_serializer_spec_item
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> bool)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_item p target_size))
= fun x -> [s x]

let array_group_serializer_spec_item_eq
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> bool)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
  (x: target { target_prop x })
: Lemma
  (ensures (array_group_serializer_spec_item s target_size x == [s x]))
= ()

#push-options "--z3rlimit 16"
#restart-solver
let array_group_parser_spec_concat
  #source1
  p1
  (#source2: array_group None)
  p2
  target_size
  target_prop
= fun x ->
  array_group_concat_unique_weak_elim1 source1 source2 x;
  let Some (x1, x2) = source1 x in
  assert (source1 x1 == Some (x1, []));
  List.Tot.append_length x1 x2;
  (p1 x1, p2 x2)

#pop-options

let array_group_parser_spec_concat_eq
  #source1 p1 #source2 p2 target_size target_prop x
= array_group_concat_unique_weak_elim1 source1 source2 x
