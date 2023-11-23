module LowParse.SteelST.Recursive.Validate
include LowParse.SteelST.Recursive.Base
include LowParse.SteelST.Validate
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Steel.ST.Reference
open Steel.ST.GenElim
open LowParse.Spec.VCList

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
