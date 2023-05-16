module LowParse.SteelST.Recursive
include LowParse.Spec.Recursive
include LowParse.SteelST.Validate
include LowParse.SteelST.Access
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.GenElim


open LowParse.Spec.VCList

module U32 = FStar.UInt32

unfold
let validate_recursive_prop_invariant0
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (consumed: SZ.t) 
  (err: U32.t)
  (n: SZ.t)
  (vl: AP.v byte)
  (vr: AP.v byte)
  (cont: bool)
: GTot prop
= AP.merge_into (AP.array_of vl) (AP.array_of vr) (AP.array_of v0) /\
  (AP.contents_of vl `Seq.append` AP.contents_of vr) `Seq.equal` AP.contents_of v0 /\
  SZ.v consumed == AP.length (AP.array_of vl) /\
  begin if cont
  then
    U32.v err == 0 /\
    begin match parse (parse_nlist n0 (parse_recursive p)) (AP.contents_of v0), parse (parse_nlist (SZ.v n) (parse_recursive p)) (AP.contents_of vr) with
    | None, None -> True
    | Some (_, consumed1), Some (_, consumed2) -> SZ.v consumed + consumed2 == consumed1
    | _ -> False
    end
  else
    validator_prop (parse_nlist n0 (parse_recursive p)) v0 err consumed
  end

let validate_recursive_prop_invariant
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (consumed: SZ.t) 
  (err: U32.t)
  (n: SZ.t)
  (vl: AP.v byte)
  (vr: AP.v byte)
  (cont: bool)
: GTot prop
= validate_recursive_prop_invariant0 p n0 v0 consumed err n vl vr cont

module R = Steel.ST.Reference

[@@__reduce__]
let validate_recursive_invariant0
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (perr: R.ref U32.t)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (cont: bool)
: Tot vprop
= exists_ (fun vl -> exists_ (fun a -> exists_ (fun vr -> exists_ (fun err -> exists_ (fun consumed -> exists_ (fun n ->
    AP.arrayptr a0 vl `star`
    AP.arrayptr a vr `star`
    R.pts_to perr full_perm err `star`
    R.pts_to pconsumed full_perm consumed `star`
    R.pts_to pn full_perm n `star`
    R.pts_to pcont full_perm cont `star`
    pure (validate_recursive_prop_invariant p n0 v0 consumed err n vl vr cont)
  ))))))

let validate_recursive_invariant
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (perr: R.ref U32.t)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (cont: bool)
: Tot vprop
= validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont cont

let intro_validate_recursive_invariant
  (#opened: _)
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (perr: R.ref U32.t)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (cont: bool)
  (#vl: AP.v byte)
  (#a: byte_array)
  (#vr: AP.v byte)
  (#err: U32.t)
  (#consumed: SZ.t)
  (#n: SZ.t)
  (_: squash (validate_recursive_prop_invariant0 p n0 v0 consumed err n vl vr cont))
: STGhostT unit opened
    (AP.arrayptr a0 vl `star`
    AP.arrayptr a vr `star`
    R.pts_to perr full_perm err `star`
    R.pts_to pconsumed full_perm consumed `star`
    R.pts_to pn full_perm n `star`
    R.pts_to pcont full_perm cont)
    (fun _ -> validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont cont)
= noop ();
  rewrite
    (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont cont)
    (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont cont)

inline_for_extraction
let read_replace
  (#t: Type)
  (#p: perm)
  (#v: Ghost.erased t)
  (r: R.ref t)
: ST t
    (R.pts_to r p v)
    (fun v' ->  R.pts_to r p v')
    True
    (fun v' ->  Ghost.reveal v == v')
= let v' = R.read r in
  vpattern_rewrite (R.pts_to r _) v';
  return v'

let mul_pos_gt
  (n1: nat)
  (n2: pos)
: Lemma
  (n1 `mul` n2 >= n1)
= ()

let validate_recursive_error_not_enough_data : U32.t = 1ul

inline_for_extraction
let r_flip
          (r:R.ref bool)
  : STT unit
      (R.pts_to r full_perm true)
      (fun _ -> R.pts_to r full_perm false)
= R.write r false

let vpattern_rewrite_with_squash
  (#opened: _)
  (#a: Type)
  (#x1: a)
  (p: a -> vprop)
  (x2: a)
  (_: squash (x1 == x2))
: STGhostT unit opened
    (p x1)
    (fun _ -> p x2)
= vpattern_rewrite p x2

let validate_recursive_step_count_post
  (p: parse_recursive_param)
  (va: v p.parse_header_kind p.header)
  (bound: SZ.t)
  (res: SZ.t)
  (err: U32.t)
: GTot prop
= if err = 0ul
  then SZ.v res == p.count va.contents
  else (p.count va.contents > SZ.v bound) == true

inline_for_extraction
let validate_recursive_step_count
  (p: parse_recursive_param)
: Tot Type
=
    (#va: v p.parse_header_kind p.header) ->
    (a: byte_array) ->
    (bound: SZ.t) ->
    (perr: R.ref U32.t) ->
    STT SZ.t
      (aparse p.parse_header a va `star` R.pts_to perr full_perm 0ul)
      (fun res -> aparse p.parse_header a va `star`
        exists_ (fun err ->
          R.pts_to perr full_perm err `star`
          pure (validate_recursive_step_count_post p va bound res err)
      ))

#push-options "--z3rlimit 128 --fuel 3 --ifuel 6 --query_stats"
#restart-solver

inline_for_extraction
let validate_recursive_step
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (w: validator p.parse_header)
  (count: validate_recursive_step_count p)
  (v0: AP.v byte)
  (a0: byte_array)
  (len0: SZ.t { SZ.v len0 == AP.length (AP.array_of v0) })
  (perr: R.ref U32.t)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  ()
: STT unit
    (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont true)
    (fun _ -> exists_ (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont))
= rewrite
    (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont true)
    (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont true);
  let _ = gen_elim () in
  let n = read_replace pn in
  let vr = vpattern_replace (fun vr -> AP.arrayptr a0 _ `star` AP.arrayptr _ vr) in
  parse_nlist_eq (SZ.v n) (parse_recursive p) (AP.contents_of vr);
  if (n = 0sz)
  then (
      r_flip pcont;
      rewrite
        (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont false)
        (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont false);
      noop ();
      return ()
    )
  else (    
     let consumed = read_replace pconsumed in
      let len = len0 `SZ.sub` consumed in
      parser_kind_prop_equiv (parse_nlist_kind (SZ.v n) (parse_recursive_kind p.parse_header_kind)) (parse_nlist (SZ.v n) (parse_recursive p));
      mul_pos_gt (SZ.v n) p.parse_header_kind.parser_kind_low;
      if (n `SZ.gt` len)
      then (
          // this test has 2 purposes: 1/ a shortcut to avoid useless header validation; 2/ avoiding integer overflow
          R.write perr validate_recursive_error_not_enough_data; 
          r_flip pcont;
          rewrite
            (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont false)
            (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont false);
          noop ();
          return ()      
        )
      else (
          let a = AP.split' a0 consumed _ in
          parse_recursive_eq' p (AP.contents_of vr);
          let consumed1 = w a len perr in
          let _ = gen_elim () in
          let err = read_replace perr in
          if (err <> 0ul)
          then (
              r_flip pcont;
              noop ();
              rewrite
                (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont false)
                (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont false);
              return ()
            )
          else (
              let a' = ghost_peek_strong p.parse_header a in
//            let _ = gen_elim () in // FIXME: WHY WHY WHY does this fail?
              let _ = elim_exists () in
              let _ = elim_exists () in
              let _ = elim_pure _ in
              let vl = vpattern_replace (aparse _ a) in
              let vr' = vpattern_replace (AP.arrayptr a') in
              parse_nlist_sum (parse_recursive p) (p.count vl.contents) (SZ.v n - 1) (AP.contents_of vr');
              parser_kind_prop_equiv (parse_nlist_kind (p.count vl.contents + (SZ.v n - 1)) (parse_recursive_kind p.parse_header_kind)) (parse_nlist (p.count vl.contents + (SZ.v n - 1)) (parse_recursive p));
              mul_pos_gt (p.count vl.contents + (SZ.v n - 1)) p.parse_header_kind.parser_kind_low;
              Seq.lemma_split (AP.contents_of vr) (SZ.v consumed1);
              let rem = len `SZ.sub` n in  // no overflow in this subtraction by virtue of the test above
              let n' = count a rem perr in
              let _ = gen_elim () in
              let err = read_replace perr in
              let vr2 = elim_aparse _ a in
              parse_injective p.parse_header (Seq.slice (AP.contents_of vr) 0 (SZ.v consumed1)) (AP.contents_of vr2);
              let overflow =
                if err = 0ul
                then (n' `SZ.gt` rem)
                else true
              in
              if overflow
              then (
                  noop ();
                  parser_kind_prop_equiv p.parse_header_kind p.parse_header;
                  let _ : squash ((p.count vl.contents + (SZ.v n - 1) > AP.length (AP.array_of vr')) == true) = () in
                  let _ : squash (parse (parse_nlist (SZ.v n) (parse_recursive p)) (AP.contents_of vr) == None) = () in
                  noop ();
                  let vr3 = AP.join a a' in
                  vpattern_rewrite_with_squash (AP.arrayptr a) vr ();
                  if err = 0ul returns STT unit (R.pts_to perr full_perm err) (fun _ -> exists_ (fun err' -> R.pts_to perr full_perm err' `star` pure (~ (err' == 0ul))))
                  then begin
                    R.write perr validate_recursive_error_not_enough_data;
                    return ()
                  end else begin
                    noop ();
                    return ()
                  end;
                  let _ = elim_exists () in
                  elim_pure _;
                  r_flip pcont;
                  intro_validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont false #_ #a #vr #_ #consumed #n ();
                  return ()
                )
              else (
                  noop ();
                  R.write pn (n' `SZ.add` (n `SZ.sub` 1sz));
                  R.write pconsumed (consumed `SZ.add` consumed1);
                  let _ = AP.join a0 a in
                  intro_validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont true #_ #a' ();
                  return ()
                )
            )
        )
    )

#pop-options

inline_for_extraction
let validate_recursive_test
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (perr: R.ref U32.t)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  ()
: STT bool
    (exists_ (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont))
    (fun cont -> validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont cont)
= 
  let gcont = elim_exists () in
  rewrite
    (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont gcont)
    (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont gcont);
  let _ = gen_elim () in
  let cont = R.read pcont in
  rewrite
    (validate_recursive_invariant0 p n0 v0 a0 perr pconsumed pn pcont gcont)
    (validate_recursive_invariant p n0 v0 a0 perr pconsumed pn pcont cont);
  return cont

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let validate_nlist_recursive
  (p: parse_recursive_param)
  (n: SZ.t)
  (w: validator p.parse_header)
  (count: validate_recursive_step_count p)
: Tot (validator (parse_nlist (SZ.v n) (parse_recursive p)))
= fun #va0 a0 len perr ->
  let n0 = Ghost.hide (SZ.v n) in
  let _ = AP.gsplit a0 0sz in
  let _ = gen_elim () in
  R.with_local 0sz (fun pconsumed ->
  R.with_local n (fun pn ->
  R.with_local true (fun pcont ->
    noop ();
    rewrite
      (validate_recursive_invariant0 p n0 va0 a0 perr pconsumed pn pcont true)
      (validate_recursive_invariant p n0 va0 a0 perr pconsumed pn pcont true);
    Steel.ST.Loops.while_loop
      (validate_recursive_invariant p n0 va0 a0 perr pconsumed pn pcont)
      (validate_recursive_test p n0 va0 a0 perr pconsumed pn pcont)
      (validate_recursive_step p n0 w count va0 a0 len perr pconsumed pn pcont)
      ;
    rewrite
      (validate_recursive_invariant p n0 va0 a0 perr pconsumed pn pcont false)
      (validate_recursive_invariant0 p n0 va0 a0 perr pconsumed pn pcont false);
    let _ = gen_elim () in
    let _ = AP.join a0 _ in
    vpattern_rewrite (AP.arrayptr a0) va0;
    let res = R.read pconsumed in
    let err = vpattern_replace_erased (R.pts_to perr _) in
    noop ();
    return res
  )))

#pop-options

inline_for_extraction
let validate_recursive
  (p: parse_recursive_param)
  (w: validator p.parse_header)
  (count: validate_recursive_step_count p)
: Tot (validator (parse_recursive p))
= fun #va0 a0 len perr ->
  parse_nlist_one (parse_recursive p) (AP.contents_of va0);
  let res = validate_nlist_recursive p 1sz w count #va0 a0 len perr in
  let _ = gen_elim () in
  noop ();
  return res

unfold
let jump_recursive_prop_invariant0
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (consumed: SZ.t) 
  (n: SZ.t)
  (vl: AP.v byte)
  (vr: AP.v byte)
  (cont: bool)
: GTot prop
= AP.merge_into (AP.array_of vl) (AP.array_of vr) (AP.array_of v0) /\
  (AP.contents_of vl `Seq.append` AP.contents_of vr) `Seq.equal` AP.contents_of v0 /\
  SZ.v consumed == AP.length (AP.array_of vl) /\
  cont == (n <> 0sz) /\
  begin match parse (parse_nlist n0 (parse_recursive p)) (AP.contents_of v0), parse (parse_nlist (SZ.v n) (parse_recursive p)) (AP.contents_of vr) with
  | Some (_, consumed1), Some (_, consumed2) -> SZ.v consumed + consumed2 == consumed1
  | _ -> False
  end

let jump_recursive_prop_invariant
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (consumed: SZ.t) 
  (n: SZ.t)
  (vl: AP.v byte)
  (vr: AP.v byte)
  (cont: bool)
: GTot prop
= jump_recursive_prop_invariant0 p n0 v0 consumed n vl vr cont

[@@__reduce__]
let jump_recursive_invariant0
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= exists_ (fun vl -> exists_ (fun a -> exists_ (fun vr -> exists_ (fun consumed -> exists_ (fun n ->
    AP.arrayptr a0 vl `star`
    AP.arrayptr a vr `star`
    R.pts_to pconsumed full_perm consumed `star`
    R.pts_to pn full_perm n `star`
    pure (jump_recursive_prop_invariant p n0 v0 consumed n vl vr cont)
  )))))

let jump_recursive_invariant
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= jump_recursive_invariant0 p n0 v0 a0 pconsumed pn cont

let intro_jump_recursive_invariant
  (#opened: _)
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (cont: bool)
  (#vl: AP.v byte)
  (#a: byte_array)
  (#vr: AP.v byte)
  (#consumed: SZ.t)
  (#n: SZ.t)
  (_: squash (jump_recursive_prop_invariant0 p n0 v0 consumed n vl vr cont))
: STGhostT unit opened
    (AP.arrayptr a0 vl `star`
    AP.arrayptr a vr `star`
    R.pts_to pconsumed full_perm consumed `star`
    R.pts_to pn full_perm n)
    (fun _ -> jump_recursive_invariant p n0 v0 a0 pconsumed pn cont)
= noop ();
  rewrite
    (jump_recursive_invariant0 p n0 v0 a0 pconsumed pn cont)
    (jump_recursive_invariant p n0 v0 a0 pconsumed pn cont)

inline_for_extraction
let jump_recursive_step_count
  (p: parse_recursive_param)
: Tot Type
=
    (#va: v p.parse_header_kind p.header) ->
    (a: byte_array) ->
    (bound: Ghost.erased SZ.t) ->
    ST SZ.t
      (aparse p.parse_header a va)
      (fun res -> aparse p.parse_header a va)
      (p.count va.contents <= SZ.v bound)
      (fun res ->
        SZ.v res == p.count va.contents
      )

#push-options "--z3rlimit 128 --fuel 3 --ifuel 6 --query_stats"
#restart-solver

inline_for_extraction
let jump_recursive_step
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
  (v0: AP.v byte)
  (a0: byte_array)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  ()
: STT unit
    (jump_recursive_invariant p n0 v0 a0 pconsumed pn true)
    (fun _ -> exists_ (jump_recursive_invariant p n0 v0 a0 pconsumed pn))
= let len0 = Ghost.hide (AP.len (AP.array_of v0)) in
  rewrite
    (jump_recursive_invariant p n0 v0 a0 pconsumed pn true)
    (jump_recursive_invariant0 p n0 v0 a0 pconsumed pn true);
  let _ = gen_elim () in
  let n = read_replace pn in
  let vr = vpattern_replace (fun vr -> AP.arrayptr a0 _ `star` AP.arrayptr _ vr) in
  parse_nlist_eq (SZ.v n) (parse_recursive p) (AP.contents_of vr);
      let consumed = read_replace pconsumed in
      let len = Ghost.hide (len0 `SZ.sub` consumed) in
      parser_kind_prop_equiv (parse_nlist_kind (SZ.v n) (parse_recursive_kind p.parse_header_kind)) (parse_nlist (SZ.v n) (parse_recursive p));
      mul_pos_gt (SZ.v n) p.parse_header_kind.parser_kind_low;
      let a = AP.split' a0 consumed _ in
      parse_recursive_eq' p (AP.contents_of vr);
      let consumed1 = w a in
      let _ = gen_elim () in
      let a' = ghost_peek_strong p.parse_header a in
//            let _ = gen_elim () in // FIXME: WHY WHY WHY does this fail?
      let _ = elim_exists () in
      let _ = elim_exists () in
      let _ = elim_pure _ in
      let vl = vpattern_replace (aparse _ a) in
      let vr' = vpattern_replace (AP.arrayptr a') in
      parse_nlist_sum (parse_recursive p) (p.count vl.contents) (SZ.v n - 1) (AP.contents_of vr');
      parser_kind_prop_equiv (parse_nlist_kind (p.count vl.contents + (SZ.v n - 1)) (parse_recursive_kind p.parse_header_kind)) (parse_nlist (p.count vl.contents + (SZ.v n - 1)) (parse_recursive p));
      mul_pos_gt (p.count vl.contents + (SZ.v n - 1)) p.parse_header_kind.parser_kind_low;
      Seq.lemma_split (AP.contents_of vr) (SZ.v consumed1);
      let rem = Ghost.hide (len `SZ.sub` n) in  // no overflow in this subtraction by virtue of the test above
      let n' = count a rem in
      let vr2 = elim_aparse _ a in
      parse_injective p.parse_header (Seq.slice (AP.contents_of vr) 0 (SZ.v consumed1)) (AP.contents_of vr2);
      let new_count = n' `SZ.add` (n `SZ.sub` 1sz) in
      R.write pn new_count;
      R.write pconsumed (consumed `SZ.add` consumed1);
      let _ = AP.join a0 a in
      intro_jump_recursive_invariant p n0 v0 a0 pconsumed pn (new_count <> 0sz) #_ #a' ();
      return ()

#pop-options

inline_for_extraction
let jump_recursive_test
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  ()
: STT bool
    (exists_ (jump_recursive_invariant p n0 v0 a0 pconsumed pn))
    (fun cont -> jump_recursive_invariant p n0 v0 a0 pconsumed pn cont)
= 
  let gcont = elim_exists () in
  rewrite
    (jump_recursive_invariant p n0 v0 a0 pconsumed pn gcont)
    (jump_recursive_invariant0 p n0 v0 a0 pconsumed pn gcont);
  let _ = gen_elim () in
  let n = R.read pn in
  [@@inline_let]
  let cont = n <> 0sz in
  rewrite
    (jump_recursive_invariant0 p n0 v0 a0 pconsumed pn gcont)
    (jump_recursive_invariant p n0 v0 a0 pconsumed pn cont);
  return cont

let intro_jump_recursive_invariant1
  (#opened: _)
  (p: parse_recursive_param)
  (n0: Ghost.erased nat)
  (v0: AP.v byte)
  (a0: byte_array)
  (pconsumed: R.ref SZ.t)
  (pn: R.ref SZ.t)
  (cont: bool)
  (#vl: AP.v byte)
  (#a: byte_array)
  (#vr: AP.v byte)
  (#consumed: SZ.t)
  (#n: SZ.t)
  (_: squash (jump_recursive_prop_invariant p n0 v0 consumed n vl vr cont))
: STGhostT unit opened
    (AP.arrayptr a0 vl `star`
    AP.arrayptr a vr `star`
    R.pts_to pconsumed full_perm consumed `star`
    R.pts_to pn full_perm n)
    (fun _ -> jump_recursive_invariant p n0 v0 a0 pconsumed pn cont)
= noop ();
  rewrite
    (jump_recursive_invariant0 p n0 v0 a0 pconsumed pn cont)
    (jump_recursive_invariant p n0 v0 a0 pconsumed pn cont)

#push-options "--z3rlimit 64 --fuel 3 --ifuel 6 --query_stats"

#restart-solver
inline_for_extraction
let jump_nlist_recursive
  (p: parse_recursive_param)
  (n: SZ.t)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
: Tot (jumper (parse_nlist (SZ.v n) (parse_recursive p)))
= fun #va0 a0 ->
  Seq.slice_length (AP.contents_of va0);
  let n0 = Ghost.hide (SZ.v n) in
  let a' = AP.gsplit a0 0sz in
  let _ = gen_elim () in
  let res =
    R.with_local 0sz (fun pconsumed ->
    R.with_local n (fun pn ->
      intro_jump_recursive_invariant p n0 va0 a0 pconsumed pn (n <> 0sz) #_ #a' ();
      Steel.ST.Loops.while_loop
        (jump_recursive_invariant p n0 va0 a0 pconsumed pn)
        (jump_recursive_test p n0 va0 a0 pconsumed pn)
        (jump_recursive_step p n0 w count va0 a0 pconsumed pn)
        ;
      rewrite
        (jump_recursive_invariant p n0 va0 a0 pconsumed pn false)
        (jump_recursive_invariant0 p n0 va0 a0 pconsumed pn false);
      let _ = gen_elim () in
      let vr = vpattern_replace (fun vr -> AP.arrayptr a0 _ `star` AP.arrayptr _ vr) in
      parse_nlist_zero (parse_recursive p) (AP.contents_of vr);
      let _ = AP.join a0 _ in
      vpattern_rewrite (AP.arrayptr a0) va0;
      let res = R.read pconsumed in
      noop ();
      return res
    ))
  in
  elim_pure (jumper_post (parse_nlist (SZ.v n) (parse_recursive p)) va0 res);
  return res

#pop-options

inline_for_extraction
let jump_recursive
  (p: parse_recursive_param)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
: Tot (jumper (parse_recursive p))
= fun #va0 a0 ->
  parse_nlist_one (parse_recursive p) (AP.contents_of va0);
  let res = jump_nlist_recursive p 1sz w count #va0 a0 in
  let _ = gen_elim () in
  noop ();
  return res

module LPC = LowParse.SteelST.Combinators
module NL = LowParse.SteelST.VCList

let intro_recursive_as_nlist
  (#opened: _)
  (p: parse_recursive_param)
  (#vl: v p.parse_header_kind p.header)
  (n: nat)
  (al: byte_array)
  (#vr: v (parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)) (nlist n p.t))
  (ar: byte_array)
: STGhost (v (parse_recursive_kind p.parse_header_kind) p.t) opened
    (aparse p.parse_header al vl `star`
      aparse (parse_nlist n (parse_recursive p)) ar vr
    )
    (fun va -> aparse (parse_recursive p) al va)
    (AP.adjacent (array_of vl) (array_of vr) /\
      n == p.count vl.contents
    )
    (fun va ->
      AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
      n == p.count vl.contents /\
      va.contents == p.synth_ (| vl.contents, vr.contents |)
    )
= let _ = LPC.intro_dtuple2 p.parse_header (parse_recursive_payload p (parse_recursive p)) al ar in
  let _ = LPC.intro_synth _ p.synth_ al () in
  Classical.forall_intro (parse_recursive_eq p);
  rewrite_aparse al (parse_recursive p)

let intro_recursive_as_list
  (#opened: _)
  (p: parse_recursive_param)
  (#vl: v p.parse_header_kind p.header)
  (al: byte_array)
  (#vr: v parse_list_kind (list p.t))
  (ar: byte_array)
: STGhost (v (parse_recursive_kind p.parse_header_kind) p.t) opened
    (aparse p.parse_header al vl `star`
      aparse (parse_list (parse_recursive p)) ar vr
    )
    (fun va -> aparse (parse_recursive p) al va)
    (AP.adjacent (array_of vl) (array_of vr) /\
      List.Tot.length vr.contents == p.count vl.contents
    )
    (fun va ->
      AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
      List.Tot.length vr.contents == p.count vl.contents /\
      va.contents == p.synth_ (| vl.contents, vr.contents |)
    )
= let _ = NL.aparse_list_aparse_nlist (parse_recursive p) (p.count vl.contents) ar in
  intro_recursive_as_nlist p (p.count vl.contents) al ar

let elim_recursive_as_list_post
  (p: parse_recursive_param)
  (va: v (parse_recursive_kind p.parse_header_kind) p.t)
  (vl: v p.parse_header_kind p.header)
  (vr: v parse_list_kind (list p.t))
: GTot prop
= 
        AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
        List.Tot.length vr.contents == p.count vl.contents /\
        va.contents == p.synth_ (| vl.contents, vr.contents |)

let elim_recursive_as_list
  (#opened: _)
  (p: parse_recursive_param)
  (#va: v (parse_recursive_kind p.parse_header_kind) p.t)
  (a: byte_array)
: STGhostT (Ghost.erased byte_array) opened
    (aparse (parse_recursive p) a va)
    (fun ar -> exists_ (fun (vl: v p.parse_header_kind p.header) -> exists_ (fun (vr: v parse_list_kind (list p.t)) ->
      aparse p.parse_header a vl `star`
      aparse (parse_list (parse_recursive p)) ar vr `star`
      pure (elim_recursive_as_list_post p va vl vr)
   )))
= Classical.forall_intro (parse_recursive_eq p);
  let _ = rewrite_aparse a (parse_recursive_alt p (parse_recursive p) `parse_synth` p.synth_) in
  let _ = LPC.elim_synth _ _ a () in
  let ar = LPC.ghost_split_dtuple2 _ _ a in
  let _ = gen_elim () in
  let tag = LPC.ghost_dtuple2_tag _ _ a ar in
  let _ = gen_elim () in
  let _ = rewrite_aparse ar (parse_nlist (p.count tag) (parse_recursive p)) in
  let _ = NL.aparse_nlist_aparse_list (parse_recursive p) (p.count tag) ar in
  noop ();
  ar

let elim_recursive_as_nlist_post
  (p: parse_recursive_param)
  (va: v (parse_recursive_kind p.parse_header_kind) p.t)
  (vl: v p.parse_header_kind p.header)
  (vr: v (parse_nlist_kind (p.count vl.contents) (parse_recursive_kind p.parse_header_kind)) (nlist (p.count vl.contents) p.t))
: GTot prop
= 
        AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
        va.contents == p.synth_ (| vl.contents, vr.contents |)

#set-options "--ide_id_info_off"

#push-options "--z3rlimit 16"

#restart-solver
let elim_recursive_as_nlist
  (#opened: _)
  (p: parse_recursive_param)
  (#va: v (parse_recursive_kind p.parse_header_kind) p.t)
  (a: byte_array)
: STGhostT (Ghost.erased byte_array) opened
    (aparse (parse_recursive p) a va)
    (fun ar -> exists_ (fun vl -> exists_ (fun vr ->
      aparse p.parse_header a vl `star`
      aparse (parse_nlist (p.count vl.contents) (parse_recursive p)) ar vr `star`
      pure (elim_recursive_as_nlist_post p va vl vr)
    )))
= let ar = elim_recursive_as_list p a in
  let _ = gen_elim () in
  let vl = vpattern_replace (aparse _ a) in
  let vr = NL.aparse_list_aparse_nlist (parse_recursive p) (p.count vl.contents) ar in
  intro_pure (elim_recursive_as_nlist_post p va vl vr);
  noop ();
  ar

#pop-options

[@@__reduce__]
let recursive_iterator0
  (p: parse_recursive_param)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (n: nat)
  (va: v (parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)) (nlist n p.t))
: Tot vprop
= (exists_ (fun (a: byte_array) -> aparse (parse_nlist n (parse_recursive p)) a va)) @==> aparse (parse_nlist n0 (parse_recursive p)) a0 va0

let recursive_iterator
  (p: parse_recursive_param)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (n: nat)
  (va: v (parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)) (nlist n p.t))
: Tot vprop
= recursive_iterator0 p a0 n0 va0 n va

let recursive_iterator_stop
  (#opened: _)
  (p: parse_recursive_param)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (a: byte_array)
  (n: nat)
  (va: v (parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)) (nlist n p.t))
: STGhostT unit opened
   (recursive_iterator p a0 n0 va0 n va `star` aparse (parse_nlist n (parse_recursive p)) a va)
   (fun _ -> aparse (parse_nlist n0 (parse_recursive p)) a0 va0)
= noop ();
  elim_implies (exists_ (fun (a: byte_array) -> aparse (parse_nlist n (parse_recursive p)) a va)) (aparse (parse_nlist n0 (parse_recursive p)) a0 va0)

#push-options "--z3rlimit 32"

#restart-solver
let recursive_iterator_start
  (#opened: _)
  (p: parse_recursive_param)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
: STGhost (v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t)) opened
    (aparse (parse_nlist n0 (parse_recursive p)) a0 va0)
    (fun va -> aparse (parse_nlist n0 (parse_recursive p)) a0 va `star` recursive_iterator p a0 n0 va0 n0 va)
    True
    (fun va -> va.contents == va0.contents)
= let vb = elim_aparse _ a0 in
  Seq.slice_length (AP.contents_of' vb);
  let a = AP.gsplit a0 0sz in
  let _ = gen_elim () in
  let va = intro_aparse (parse_nlist n0 (parse_recursive p)) a in
  vpattern_rewrite (fun a -> aparse _ a _) a0;
  intro_implies (exists_ (fun (a: byte_array) -> aparse (parse_nlist n0 (parse_recursive p)) a va)) (aparse (parse_nlist n0 (parse_recursive p)) a0 va0) (AP.arrayptr a0 _) (fun _ ->
    let a = elim_exists () in
    let vr = elim_aparse _ a in
    let vb = AP.join a0 a in
    assert (AP.contents_of' vb `Seq.equal` AP.contents_of' vr);
    noop ();
    let _ = intro_aparse (parse_nlist n0 (parse_recursive p)) a0 in
    vpattern_rewrite (aparse _ a0) va0
  );
  va

#restart-solver
let recursive_iterator_next
  (#opened: _)
  (p: parse_recursive_param)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (n: nat)
  (va: v (parse_nlist_kind n (parse_recursive_kind p.parse_header_kind)) (nlist n p.t))
  (a1: byte_array)
  (va1: v p.parse_header_kind p.header)
  (a2: byte_array)
  (n2: nat)
  (va2: v (parse_nlist_kind n2 (parse_recursive_kind p.parse_header_kind)) (nlist n2 p.t))
  (a3: byte_array)
  (n3: nat)
  (va3: v (parse_nlist_kind n3 (parse_recursive_kind p.parse_header_kind)) (nlist n3 p.t))
: STGhost (v (parse_nlist_kind (n2 + n3) (parse_recursive_kind p.parse_header_kind)) (nlist (n2 + n3) p.t)) opened
    (recursive_iterator p a0 n0 va0 n va `star`
      aparse p.parse_header a1 va1 `star`
      aparse (parse_nlist n2 (parse_recursive p)) a2 va2 `star`
      aparse (parse_nlist n3 (parse_recursive p)) a3 va3
    )
    (fun va' -> recursive_iterator p a0 n0 va0 (n2 + n3) va' `star`
      aparse (parse_nlist (n2 + n3) (parse_recursive p)) a2 va'
    )
    (
      AP.adjacent (array_of' va1) (array_of' va2) /\
      AP.merge_into (AP.merge (array_of' va1) (array_of' va2)) (array_of' va3) (array_of' va) /\
      n2 == p.count va1.contents /\
      va.contents == p.synth_ (| va1.contents, va2.contents |) :: va3.contents
    )
    (fun va' ->
      va'.contents == va2.contents `List.Tot.append` va3.contents
    )
= let va' = NL.intro_nlist_sum (n2 + n3) (parse_recursive p) n2 a2 n3 a3 in
  intro_implies (exists_ (fun (a: byte_array) -> aparse (parse_nlist (n2 + n3) (parse_recursive p)) a va')) (aparse (parse_nlist n0 (parse_recursive p)) a0 va0) (aparse p.parse_header a1 va1 `star` recursive_iterator p a0 n0 va0 n va) (fun _ ->
    let a2' = elim_exists () in
    let a3' = NL.elim_nlist_sum (n2 + n3) (parse_recursive p) a2' n2 n3 in
    let _ = gen_elim () in
    let va2_ : v _ (nlist n2 p.t) = vpattern_replace (aparse _ a2') in
    let va3_ : v _ (nlist n3 p.t) = vpattern_replace (aparse _ a3') in
    List.Tot.append_injective va2.contents va2_.contents va3.contents va3_.contents;
    noop ();
    let _ = intro_recursive_as_nlist p n2 a1 a2' in
    let _ = NL.intro_nlist_cons n (parse_recursive p) n3 a1 a3' in
    vpattern_rewrite (aparse _ a1) va;
    rewrite
      (recursive_iterator p a0 n0 va0 n va)
      (recursive_iterator0 p a0 n0 va0 n va);
    elim_implies (exists_ (fun (a: byte_array) -> aparse (parse_nlist n (parse_recursive p)) a va)) (aparse (parse_nlist n0 (parse_recursive p)) a0 va0)
  );
  rewrite
    (recursive_iterator0 p a0 n0 va0 (n2 + n3) va')
    (recursive_iterator p a0 n0 va0 (n2 + n3) va');
  va'

#pop-options

unfold
let fold_recursive_invariant_prop0
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (#t: Type)
  (fold: fold_recursive_t s t)
  (init: t)
  (cont: bool)
  (n: _)
  (va: v (parse_nlist_kind (SZ.v n) (parse_recursive_kind p.parse_header_kind)) (nlist (SZ.v n) p.t))
  (x: _)
: GTot prop
=
      begin if cont
      then
        List.Tot.fold_left fold.fold init va0.contents == List.Tot.fold_left fold.fold x va.contents /\
        n <> 0sz
      else
        List.Tot.fold_left fold.fold init va0.contents == x
      end

let fold_recursive_invariant_prop
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (#t: Type)
  (fold: fold_recursive_t s t)
  (init: t)
  (cont: bool)
  (n: _)
  (va: v (parse_nlist_kind (SZ.v n) (parse_recursive_kind p.parse_header_kind)) (nlist (SZ.v n) p.t))
  (x: _)
: GTot prop
= fold_recursive_invariant_prop0 s n0 va0 fold init cont n va x

[@@__reduce__]
let fold_recursive_invariant0
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (#t: Type)
  (fold: fold_recursive_t s t)
  (init: t)
  (q: t -> vprop)
  (cont: bool)
: Tot vprop
= exists_ (fun a -> exists_ (fun n -> exists_ (fun va -> exists_ (fun x ->
    R.pts_to pa full_perm a `star`
    R.pts_to pn full_perm n `star`
    q x `star`
    aparse (parse_nlist (SZ.v n) (parse_recursive p)) a va `star`
    recursive_iterator p a0 n0 va0 (SZ.v n) va `star`
    R.pts_to pcont full_perm cont `star`
    pure (fold_recursive_invariant_prop s n0 va0 fold init cont n va x)
  ))))

let fold_recursive_invariant
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (#t: Type)
  (fold: fold_recursive_t s t)
  (init: t)
  (q: t -> vprop)
  (cont: bool)
: Tot vprop
= fold_recursive_invariant0 s a0 n0 va0 pa pn pcont fold init q cont

let intro_fold_recursive_invariant
  (#opened: _)
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (a0: byte_array)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (#t: Type)
  (fold: fold_recursive_t s t)
  (init: t)
  (q: t -> vprop)
  (cont: bool)
  (a: _)
  (n: _)
  (va: _)
  (x: _)
: STGhost unit opened
    (R.pts_to pa full_perm a `star`
      R.pts_to pn full_perm n `star`
      q x `star`
      aparse (parse_nlist (SZ.v n) (parse_recursive p)) a va `star`
      recursive_iterator p a0 n0 va0 (SZ.v n) va `star`
      R.pts_to pcont full_perm cont
    )
    (fun _ -> fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init q cont)
    (fold_recursive_invariant_prop0 s n0 va0 fold init cont n va x)
    (fun _ -> True)
= noop ();
  rewrite
    (fold_recursive_invariant0 s a0 n0 va0 pa pn pcont fold init q cont)
    (fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init q cont)

inline_for_extraction
let size_add_fits
  (n1 n2: SZ.t)
  (bound: Ghost.erased SZ.t)
  (sq: squash (SZ.v n1 + SZ.v n2 <= SZ.v bound))
: Pure SZ.t
    (requires True)
    (ensures (fun y -> SZ.v y == SZ.v n1 + SZ.v n2))
= n1 `SZ.add` n2

let aparse_nlist_count_le_size
  (k: parser_kind)
  (t: Type)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
  (sq: squash (k.parser_kind_low > 0))
: Tot (squash (n <= AP.length (array_of' va)))
= ()

let get_children_synth
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (x: parse_recursive_alt_t p.t p.header p.count)
: Lemma
  (get_children s (p.synth_ x) == dsnd x)
= let y = s.synth_recip (p.synth_ x) in
  assert (p.synth_ x == p.synth_ y)

inline_for_extraction
let fold_recursive_step_t
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (state: t -> vprop)
: Tot Type
=
  (x: Ghost.erased t) ->
  (a: byte_array) ->
  (va: v (parse_recursive_kind p.parse_header_kind) p.t) ->
  STT unit
    (aparse (parse_recursive p) a va `star` state x)
    (fun _ -> aparse (parse_recursive p) a va `star` state (fold.step x va.contents))

// #push-options "--z3rlimit 128 --fuel 3 --ifuel 6 --query_stats --split_queries always --z3cliopt smt.arith.nl=false"

#restart-solver
inline_for_extraction
let fold_recursive_step
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
  (a0: byte_array)
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (init: Ghost.erased t)
  (state: t -> vprop)
  (step: fold_recursive_step_t s fold state)
  (_: unit)
: STT unit
    (fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state true)
    (fun _ -> exists_ (fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state))
= rewrite_with_tactic
    (fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state true)
    (fold_recursive_invariant0 s a0 n0 va0 pa pn pcont fold init state true);
  let _ = gen_elim () in
  let n = read_replace pn in
  let n_pred = n `SZ.sub` 1sz in
  let a = read_replace pa in
  vpattern_rewrite (fun a -> aparse _ a _) a;
  let _ = rewrite_aparse a (parse_nlist (SZ.v n) (parse_recursive p)) in
  let ga3 = NL.elim_nlist_cons (parse_recursive p) (SZ.v n) (SZ.v n_pred) a in
  let _ = gen_elim () in
  let va1 = vpattern_replace (aparse _ a) in
  let x = vpattern_replace_erased state in
  let va3 : v _ (nlist (SZ.v n_pred) p.t) = vpattern_replace (aparse (parse_nlist (SZ.v n_pred) (parse_recursive p)) ga3) in
  step _ a _;
  let ga2 = elim_recursive_as_nlist p a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let a2 = hop_aparse_aparse w _ a ga2 in
  R.write pa a2;
  let va2 = rewrite_aparse a2 (parse_nlist (p.count vh.contents) (parse_recursive p)) in
  get_children_synth s (| vh.contents, va2.contents |);
  noop ();
  let _ = aparse_nlist_count_le_size _ _ _ va2 () in
  noop ();
  let nl = count a (AP.len (array_of' va2)) in
  let vr = recursive_iterator_next p a0 n0 va0 _ _ a _ a2 _ _ ga3 _ _ in
  fold_recursive_cons_eq s fold x va1.contents va3.contents vr.contents;
  let _ = aparse_nlist_count_le_size _ _ _ vr () in
  let n' = size_add_fits nl n_pred (AP.len (array_of' vr)) () in
  noop ();
  R.write pn n';
  let vr : v _ (nlist (SZ.v n') p.t) = rewrite_aparse a2 (parse_nlist (SZ.v n') (parse_recursive p)) in
  rewrite
    (recursive_iterator p a0 n0 va0 _ _)
    (recursive_iterator p a0 n0 va0 (SZ.v n') vr);
  R.write pcont (n' <> 0sz);
  intro_fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state _ a2 n' vr _;
  noop ()

// #pop-options

let fold_recursive_continue_post
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (x: t)
  (n: SZ.t)
  (va: v (parse_nlist_kind (SZ.v n) (parse_recursive_kind p.parse_header_kind)) (nlist (SZ.v n) p.t))
  (x' : t)
  (res: bool)
: GTot prop
= x' == (if res then x else List.Tot.fold_left fold.fold (Ghost.reveal x) va.contents)

inline_for_extraction
let fold_recursive_continue_t
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (state: t -> vprop)
: Tot Type
= (x: Ghost.erased t) ->
  (n: SZ.t) ->
  (va: v (parse_nlist_kind (SZ.v n) (parse_recursive_kind p.parse_header_kind)) (nlist (SZ.v n) p.t)) ->
  (a: byte_array) ->
  STT bool
    (aparse (parse_nlist (SZ.v n) (parse_recursive p)) a va `star` state x)
    (fun res ->
       aparse (parse_nlist (SZ.v n) (parse_recursive p)) a va `star`
       exists_ (fun x' -> state x' `star` pure (fold_recursive_continue_post s fold x n va x' res))
    )

#push-options "--z3rlimit 16"

#restart-solver
inline_for_extraction
let fold_recursive_test
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (a0: byte_array)
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 (parse_recursive_kind p.parse_header_kind)) (nlist n0 p.t))
  (pa: R.ref byte_array)
  (pn: R.ref SZ.t)
  (pcont: R.ref bool)
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (init: Ghost.erased t)
  (state: t -> vprop)
  (f_continue: fold_recursive_continue_t s fold state)
  (_: unit)
: STT bool
    (exists_ (fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state))
    (fun res -> fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state res)
= let gres = elim_exists () in
  rewrite
    (fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state _)
    (fold_recursive_invariant0 s a0 n0 va0 pa pn pcont fold init state gres);
  let _ = gen_elim () in
  let cont = read_replace pcont in
  if cont
  then begin
    let n = read_replace pn in
    let a = read_replace pa in
    vpattern_rewrite (fun a -> aparse _ a _) a;
    let va = rewrite_aparse a (parse_nlist (SZ.v n) (parse_recursive p)) in
    rewrite
      (recursive_iterator p a0 n0 va0 _ _)
      (recursive_iterator p a0 n0 va0 (SZ.v n) va);
    let cont' = f_continue _ n _ a in
    let _ = gen_elim () in
    if cont'
    then begin
      noop ();
      intro_fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state cont _ _ _ _;
      return cont
    end else begin
      R.write pcont false;
      noop ();
      intro_fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state false _ _ _ _;
      return false
    end
  end else begin
    noop ();
    intro_fold_recursive_invariant s a0 n0 va0 pa pn pcont fold init state cont _ _ _ _;
    return cont
  end

#pop-options

// #push-options "--z3rlimit 16  --fuel 3 --ifuel 6 --query_stats --split_queries always --z3cliopt smt.arith.nl=false"

#restart-solver
inline_for_extraction
let fold_recursive_nlist
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
  (a0: byte_array)
  (n0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v n0) (parse_recursive_kind p.parse_header_kind)) (nlist (SZ.v n0) p.t))
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (init: Ghost.erased t)
  (state: t -> vprop)
  (step: fold_recursive_step_t s fold state)
  (f_continue: fold_recursive_continue_t s fold state)
: STT unit
    (aparse (parse_nlist (SZ.v n0) (parse_recursive p)) a0 va0 `star` state init)
    (fun res ->
      aparse (parse_nlist (SZ.v n0) (parse_recursive p)) a0 va0 `star`
      state (List.Tot.fold_left fold.fold (Ghost.reveal init) va0.contents)
    )
= let va = recursive_iterator_start p a0 (SZ.v n0) _ in
  R.with_local a0 (fun pa ->
  R.with_local n0 (fun pn ->
  R.with_local (n0 <> 0sz) (fun pcont ->
    intro_fold_recursive_invariant s a0 (SZ.v n0) va0 pa pn pcont fold init state (n0 <> 0sz) _ _ _ _;
    Steel.ST.Loops.while_loop
      (fold_recursive_invariant s a0 (SZ.v n0) va0 pa pn pcont fold init state)
      (fold_recursive_test s a0 (SZ.v n0) va0 pa pn pcont fold init state f_continue)
      (fold_recursive_step s w count a0 (SZ.v n0) va0 pa pn pcont fold init state step)
      ;
    rewrite
      (fold_recursive_invariant s a0 (SZ.v n0) va0 pa pn pcont fold init state false)
      (fold_recursive_invariant0 s a0 (SZ.v n0) va0 pa pn pcont fold init state false);
    let _ = gen_elim () in
    recursive_iterator_stop p a0 (SZ.v n0) va0 _ _ _;
    vpattern_rewrite state _;
    noop ()
  )))

// #pop-options

inline_for_extraction
let fold_recursive
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
  (a0: byte_array)
  (#va0: v (parse_recursive_kind p.parse_header_kind) p.t)
  (#t: Type0) // gen_elim universe issue
  (fold: fold_recursive_t s t)
  (init: Ghost.erased t)
  (state: t -> vprop)
  (step: fold_recursive_step_t s fold state)
  (f_continue: fold_recursive_continue_t s fold state)
: STT unit
    (aparse (parse_recursive p) a0 va0 `star` state init)
    (fun res ->
      aparse (parse_recursive p) a0 va0 `star`
      state (fold.fold (Ghost.reveal init) va0.contents)
    )
= [@@inline_let]
  let n0 = 1sz in
  let _ = NL.intro_nlist_one (parse_recursive p) a0 (SZ.v n0) in
  fold_recursive_nlist s w count a0 n0 fold init state step f_continue;
  let _ = NL.elim_nlist_one (parse_recursive p) (SZ.v n0) a0 in
  vpattern_rewrite (aparse _ a0) _;
  vpattern_rewrite state _

inline_for_extraction
let pred_recursive_base_t
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (base: Ghost.erased (p.t -> bool))
: Tot Type
=
  (a: byte_array) ->
  (va: v (parse_recursive_kind p.parse_header_kind) p.t) ->
  ST bool
    (aparse (parse_recursive p) a va)
    (fun _ -> aparse (parse_recursive p) a va)
    True
    (fun res -> res == Ghost.reveal base va.contents)

inline_for_extraction
let pred_recursive_step
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (pred: pred_recursive_t s)
  (base: pred_recursive_base_t s pred.base)
  (pv: R.ref bool)
: Tot (fold_recursive_step_t s (fold_of_pred_recursive s pred) (R.pts_to pv full_perm))
= fun x a va ->
    let res = R.read pv in
    if res
    then begin
      let res = base a va in
      R.write pv res;
      vpattern_rewrite (R.pts_to pv full_perm) _
    end else begin
      noop ();
      vpattern_rewrite (R.pts_to pv full_perm) _
    end

inline_for_extraction
let pred_recursive_continue
  (#p: parse_recursive_param)
  (s: serialize_recursive_param p)
  (pred: pred_recursive_t s)
  (pv: R.ref bool)
: Tot (fold_recursive_continue_t s (fold_of_pred_recursive s pred) (R.pts_to pv full_perm))
= fun x n va a ->
    let cont = read_replace pv in
    LowParse.WellFounded.for_all_fold_left_aux pred.pred cont va.contents;
    noop ();
    return cont

inline_for_extraction
let intro_refinement
  (#t: Type)
  (p: (t ->  prop))
  (x: t)
: Pure (x: t { p x })
    (requires (p x))
    (ensures (fun _ -> True))
= x

inline_for_extraction
let pred_recursive_nlist
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
  (a0: byte_array)
  (n0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v n0) (parse_recursive_kind p.parse_header_kind)) (nlist (SZ.v n0) p.t))
  (pred: pred_recursive_t s)
  (base: pred_recursive_base_t s pred.base)
: ST bool
    (aparse (parse_nlist (SZ.v n0) (parse_recursive p)) a0 va0)
    (fun _ -> aparse (parse_nlist (SZ.v n0) (parse_recursive p)) a0 va0)
    True
    (fun res -> res == List.Tot.for_all pred.pred va0.contents)
= LowParse.WellFounded.for_all_fold_left pred.pred va0.contents;
  let res : (res: bool { res == List.Tot.for_all pred.pred va0.contents }) = R.with_local true (fun pres ->
    fold_recursive_nlist
      s w count
      a0 n0
      (fold_of_pred_recursive s pred)
      true
      (R.pts_to pres full_perm)
      (pred_recursive_step s pred base pres)
      (pred_recursive_continue s pred pres)
      ;
    let res = read_replace pres in
    noop ();
    return (intro_refinement (fun res -> res == List.Tot.for_all pred.pred va0.contents) res)
  )
  in
  return res

inline_for_extraction
let pred_recursive
  (#p: parse_recursive_param u#0 u#0) // gen_elim universe issue
  (s: serialize_recursive_param p)
  (w: jumper p.parse_header)
  (count: jump_recursive_step_count p)
  (a0: byte_array)
  (#va0: v (parse_recursive_kind p.parse_header_kind) p.t)
  (pred: pred_recursive_t s)
  (base: pred_recursive_base_t s pred.base)
: ST bool
    (aparse (parse_recursive p) a0 va0)
    (fun _ -> aparse (parse_recursive p) a0 va0)
    True
    (fun res -> res == pred.pred va0.contents)
= [@@inline_let]
  let n0 = 1sz in
  let _ = NL.intro_nlist_one (parse_recursive p) a0 (SZ.v n0) in
  let res = pred_recursive_nlist s w count a0 n0 pred base in
  let _ = NL.elim_nlist_one (parse_recursive p) (SZ.v n0) a0 in
  vpattern_rewrite (aparse _ a0) _;
  return res
