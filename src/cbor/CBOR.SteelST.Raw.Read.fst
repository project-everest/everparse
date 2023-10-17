module CBOR.SteelST.Raw.Read
open CBOR.SteelST.Raw.Validate

inline_for_extraction
noextract
let jump_long_argument_as_simple_value
  (b: parse_filter_refine get_header_argument_as_simple_value_initial_byte_precond)
: Tot (read_and_jump (parse_long_argument b))
= match b with
  | (major_type, (additional_info, _)) ->
    ifthenelse_read_and_jump
      (additional_info = additional_info_long_argument_8_bits)
      (fun _ ->
         rewrite_read_and_jump
           (read_and_jump_weaken
             (strong_parser_kind 0 8 None)
             (read_and_jump_synth'
               (read_and_jump_filter
                 (mk_read_and_jump (cps_reader_of_leaf_reader read_u8) I.jump_u8)
                 simple_value_long_argument_wf
               )
               (LongArgumentSimpleValue #b ())
               ()
             )
             ()
           )
           (parse_long_argument b)
      )
      (fun _ ->
         rewrite_read_and_jump
           (read_and_jump_weaken
             (strong_parser_kind 0 8 None)
             (read_and_jump_synth'
               (mk_read_and_jump (cps_reader_of_leaf_reader read_empty) jump_empty)
               (LongArgumentOther #b additional_info ())
               ()
             )
             ()
           )
           (parse_long_argument b)
      )

let get_header_argument_as_simple_value_precond
  (h: header)
: GTot bool
=
      let (| b, x |) = h in
      get_header_argument_as_simple_value_initial_byte_precond b

let get_header_argument_as_simple_value
  (h: header)
: Ghost simple_value
  (requires (get_header_argument_as_simple_value_precond h))
  (ensures (fun _ -> True))
= let (| b, x |) = h in
  argument_as_simple_value b x

inline_for_extraction
noextract
let read_header_argument_as_simple_value
  (#va: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST simple_value
    (aparse parse_header a va)
    (fun _ -> aparse parse_header a va)
    (get_header_argument_as_simple_value_precond va.contents)
    (fun res -> 
      let (| b, x |) = va.contents in
      let (major_type, (additional_info, _)) = b in
      major_type = major_type_simple_value /\ additional_info `U8.lte` additional_info_long_argument_8_bits /\
      res == argument_as_simple_value b x
    )
= rewrite (aparse parse_header a va) (aparse (parse_dtuple2 parse_initial_byte parse_long_argument) a va);
  let _ = intro_dtuple2_filter_tag parse_initial_byte get_header_argument_as_simple_value_initial_byte_precond parse_long_argument a in
  let res = read_and_jump_dtuple2
    (read_and_jump_filter read_and_jump_initial_byte get_header_argument_as_simple_value_initial_byte_precond)
    parse_long_argument
    jump_long_argument_as_simple_value
    a
    emp
    simple_value
    (fun res -> aparse parse_header a va `star` pure (
      get_header_argument_as_simple_value_precond va.contents == true /\
      res == get_header_argument_as_simple_value va.contents
    ))
    (fun _ (| b, x |) ->
      let _ = elim_dtuple2_filter_tag parse_initial_byte get_header_argument_as_simple_value_initial_byte_precond parse_long_argument a in
      rewrite (aparse (parse_dtuple2 parse_initial_byte parse_long_argument) a _) (aparse parse_header a va);
      return (argument_as_simple_value b x)
    )
  in
  let _ = elim_pure _ in
  return res

#push-options "--z3rlimit 16"
#restart-solver

let read_simple_value
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST simple_value
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (Simple? va.contents)
    (fun res -> va.contents == Simple res)
= Classical.forall_intro parse_raw_data_item_eq;
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va1 = elim_synth _ _ a () in
  let a_content = ghost_split_dtuple2_full _ _ a in // parse_header (parse_content parse_raw_data_item) a in
  let _ = gen_elim () in
  let res = read_header_argument_as_simple_value a in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a_content in
  let _ = intro_synth (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item a () in
  let _ = rewrite_aparse a parse_raw_data_item in
  vpattern_rewrite (aparse parse_raw_data_item a) va;
  return res

#pop-options

let read_int64
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST U64.t
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (Int64? va.contents)
    (fun res -> 
      match va.contents with
      | Int64 _ res' -> res == res'
      | _ -> False
    )
= read_argument_as_uint64 a

#push-options "--z3rlimit 16"
#restart-solver

let focus_tagged
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun va' ->
      aparse parse_raw_data_item a' va' `star`
      (aparse parse_raw_data_item a' va' `implies_`
        aparse parse_raw_data_item a va) `star`
      pure (focus_tagged_postcond va va')
    ))
    (Tagged? va.contents)
    (fun _ -> True)
= 
  Classical.forall_intro parse_raw_data_item_eq;
  noop ();
  let va1 = rewrite_aparse_with_implies a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let va2 = elim_synth_with_implies _ _ a () in
  implies_trans
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a va2)
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) a va1)
    (aparse parse_raw_data_item a va);
  let ga' = ghost_split_dtuple2_full _ _ a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let vc = rewrite_aparse ga' (parse_content parse_raw_data_item vh.contents) in
  let a' = hop_aparse_aparse jump_header (parse_content parse_raw_data_item vh.contents) a ga' in
  intro_implies
    (aparse (parse_content parse_raw_data_item vh.contents) a' vc)
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a va2)
    (aparse parse_header a vh)
    (fun _ ->
      let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a' in
      vpattern_rewrite (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a) va2
    );
  implies_trans
    (aparse (parse_content parse_raw_data_item vh.contents) a' vc)
    (aparse (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) a va2)
    (aparse parse_raw_data_item a va);
  let _ = rewrite_aparse_with_implies a' parse_raw_data_item in
  implies_trans
    (aparse parse_raw_data_item a' _)
    (aparse (parse_content parse_raw_data_item vh.contents) a' vc)
    (aparse parse_raw_data_item a va);
  return a'

let intro_raw_data_item_string
  (#opened: _)
  (m: major_type_byte_string_or_text_string)
  (#vh: v (get_parser_kind parse_header) header)
  (ah: byte_array)
  (#vp: _)
  (ap: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header ah vh `star` AP.arrayptr ap vp)
    (fun v' -> aparse parse_raw_data_item ah v')
    (intro_raw_data_item_string_pre m vh vp)
    (fun v' ->
      let (| b, arg |) = vh.contents in
      AP.merge_into (array_of vh) (AP.array_of vp) (array_of v') /\
      U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp) /\
      v'.contents == String m (AP.contents_of vp)
    )
=
  let (| b, arg |) = vh.contents in
  let _ = intro_lseq_bytes (U64.v (argument_as_uint64 b arg)) ap in
  let _ = rewrite_aparse ap (parse_content parse_raw_data_item vh.contents) in
  let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) ah ap in
  let _ = intro_synth _ synth_raw_data_item ah () in
  Classical.forall_intro parse_raw_data_item_eq;
  noop ();
  rewrite_aparse ah parse_raw_data_item

let elim_raw_data_item_string_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vh: v (get_parser_kind parse_header) header)
  (vp: AP.v byte)
: GTot prop
= 
      let (| b, arg |) = vh.contents in
      let (major_type, _) = b in
      AP.merge_into (array_of vh) (AP.array_of vp) (array_of va) /\
      U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp) /\
      begin match va.contents with
      | String m contents ->
        m == major_type /\
        contents == (AP.contents_of vp)
      | _ -> False
      end

let elim_raw_data_item_string
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun (vh: v (get_parser_kind parse_header) header) -> exists_ (fun vp ->
      aparse parse_header a vh `star`
      AP.arrayptr a' vp `star`
      pure (elim_raw_data_item_string_post va vh vp)
    )))
    (String? va.contents)
    (fun _ -> True)
= 
  Classical.forall_intro parse_raw_data_item_eq;
  noop ();
  let _ = rewrite_aparse a (parse_dtuple2 parse_header (parse_content parse_raw_data_item) `parse_synth` synth_raw_data_item) in
  let _ = elim_synth _ _ a () in
  let a' = ghost_split_dtuple2_full _ _ a in
  let _ = gen_elim () in
  let vh = vpattern_replace (aparse _ a) in
  let (| b, arg |) = vh.contents in
  let _ = rewrite_aparse a' (parse_lseq_bytes (U64.v (argument_as_uint64 b arg))) in
  let _ = elim_lseq_bytes _ a' in
  noop ();
  a'

(*
let ghost_focus_string_strong
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (ghost_focus_byte_string_post va vp) `star`
      (forall_ (fun vp' ->
        (AP.arrayptr a' vp' `star` pure (AP.array_of vp' == AP.array_of vp))
        `implies_`
        (exists_ (fun va' -> aparse parse_raw_data_item a va' `star` pure (
          AP.length (AP.array_of vp') < 4294967296 /\
          array_of va' == array_of va /\
          va'.contents == String _ (AP.contents_of vp')
      )))))
    ))
    (String? va.contents)
    (fun _ -> True)
= ...
*)

#pop-options

#push-options "--z3rlimit 32 --query_stats --ifuel 8"

#restart-solver
let ghost_focus_string
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (
        ghost_focus_string_post va vp
      ) `star`
      (AP.arrayptr a' vp `implies_` aparse parse_raw_data_item a va)
    ))
    (String? va.contents)
    (fun _ -> True)
= let a' = elim_raw_data_item_string a in
  let _ = gen_elim () in
  intro_implies (AP.arrayptr a' _) (aparse parse_raw_data_item a va) (aparse _ a _) (fun _ ->
    let m = String?.typ va.contents in
    let _ = intro_raw_data_item_string m a a' in
    vpattern_rewrite (aparse _ a) va
  );
  noop ();
  a'

#restart-solver
let focus_string
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (
        ghost_focus_string_post va vp
      ) `star`
      (AP.arrayptr a' vp `implies_` aparse parse_raw_data_item a va)
    ))
    (String? va.contents)
    (fun _ -> True)
= let _ = elim_raw_data_item_string a in
  let _ = gen_elim () in
  let a' = hop_aparse_arrayptr jump_header _ _ in
  intro_implies (AP.arrayptr a' _) (aparse parse_raw_data_item a va) (aparse _ a _) (fun _ ->
    let m = String?.typ va.contents in
    let _ = intro_raw_data_item_string m a a' in
    vpattern_rewrite (aparse _ a) va
  );
  noop ();
  return a'

#pop-options
