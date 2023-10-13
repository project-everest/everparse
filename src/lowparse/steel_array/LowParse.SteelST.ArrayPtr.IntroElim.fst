module LowParse.SteelST.ArrayPtr.IntroElim
friend LowParse.SteelST.ArrayPtr

let steel_array_of_array
  a
= a.array_ptr

let mk_array
  a p
= Mkarray a p

inline_for_extraction
let intro_arrayptr_with_implies
  #elt #p #va a
= SA.pts_to_length _ _;
  [@@inline_let]
  let a' = SA.ptr_of a in
  let va' = {
    v_array = mk_array a p;
    v_contents = Ghost.reveal va;
  }
  in
  rewrite_with_implies
    (SA.pts_to _ _ _)
    (arrayptr1 va');
  rewrite_with_implies
    (arrayptr0 a' va')
    (arrayptr a' va');
  intro_implies
    (arrayptr0 a' va')
    (arrayptr1 va')
    emp
    (fun _ -> let _ = gen_elim () in noop ());
  implies_trans
    (arrayptr a' va')
    (arrayptr0 a' va')
    (arrayptr1 va');
  implies_trans
    (arrayptr a' va')
    (arrayptr1 va')
    (SA.pts_to _ _ _);
  return a'

inline_for_extraction
let elim_arrayptr_with_implies
  #elt #va a
= rewrite_with_implies
    (arrayptr a va)
    (arrayptr0 a va);
  let _ = gen_elim () in
  [@@inline_let]
  let a' : SA.array elt = (| a, Ghost.hide (Seq.length va.v_contents) |) in
  rewrite_with_implies
    (arrayptr1 va)
    (SA.pts_to a' (array_perm (array_of va)) (contents_of' va));
  intro_implies
    (arrayptr1 va)
    (arrayptr0 a va)
    emp
    (fun _ -> noop (); noop ());
  implies_trans
    (SA.pts_to _ _ _)
    (arrayptr1 va)
    (arrayptr0 a va);
  implies_trans
    (SA.pts_to _ _ _)
    (arrayptr0 a va)
    (arrayptr a va);
  return a'
