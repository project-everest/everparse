module LowParse.SteelST.Recursive.Jump
include LowParse.SteelST.Recursive.Base
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Steel.ST.Reference
open Steel.ST.GenElim
open LowParse.Spec.VCList

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
