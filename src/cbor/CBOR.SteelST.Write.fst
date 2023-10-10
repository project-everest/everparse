module CBOR.SteelST.Write
include CBOR.SteelST.Base
open CBOR.SteelST.Read
open LowParse.SteelST.Combinators
open LowParse.SteelST.Assoc
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open LowParse.SteelST.SeqBytes
open Steel.ST.GenElim

module R = Steel.ST.Reference
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module I16 = FStar.Int16
module U64 = FStar.UInt64

#set-options "--print_universes"

#set-options "--ide_id_info_off"

(* Writers *)

let write_initial_byte
  (t: major_type_t)
  (x: additional_info_t)
  (sq: squash (
    initial_byte_wf (t, (x, ()))
  ))
  (#va: AP.v byte)
  (a: byte_array)
: ST (v (get_parser_kind parse_initial_byte) initial_byte)
    (AP.arrayptr a va)
    (fun va' ->
      aparse parse_initial_byte a va'
    )
    (AP.length (AP.array_of va) == 1 /\
      AP.array_perm (AP.array_of va) == full_perm
    )
    (fun va' -> 
       array_of' va' == AP.array_of va /\
       va'.contents == mk_initial_byte t x
    )
= let _ = exact_write (write_bitsum' mk_synth_initial_byte (write_constant_size write_u8 1sz)) (mk_initial_byte t x) a in
  let _ = intro_filter _ initial_byte_wf a in
  rewrite_aparse a parse_initial_byte

inline_for_extraction
noextract
let write_initial_byte'
: exact_writer serialize_initial_byte
= fun x a ->
  match x with
  | (major_type, (additional_info, _)) ->
    write_initial_byte major_type additional_info () a

#push-options "--z3rlimit 64 --ifuel 8"

(* In fact, I can follow the structure of the type instead. Indeed, the
   data constructors for long_argument do follow the structure of the ifthenelse
   in the parser or the serializer: each branch of the match corresponds to exactly 
   one branch of the ifthenelse.
*)
#restart-solver
inline_for_extraction
noextract
let write_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (maybe_r2l_writer_for (serialize_long_argument b) a)
= match a with
  | LongArgumentSimpleValue _ _ ->
    rewrite_maybe_r2l_writer
      #_ #(long_argument b)
      (maybe_r2l_write_weaken parse_long_argument_kind
        (maybe_r2l_write_synth'
          (maybe_r2l_write_filter
            (maybe_r2l_write_constant_size write_u8 1sz)
            simple_value_long_argument_wf
          )
          (LongArgumentSimpleValue ())
          LongArgumentSimpleValue?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU8 _ _ ->
    rewrite_maybe_r2l_writer
      #_ #(long_argument b)
      (maybe_r2l_write_weaken parse_long_argument_kind
        (maybe_r2l_write_synth'
          (maybe_r2l_write_filter
            (maybe_r2l_write_constant_size write_u8 1sz)
            uint8_wf
          )
          (LongArgumentU8 ())
          LongArgumentU8?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU16 _ _ ->
    rewrite_maybe_r2l_writer
      #_ #(long_argument b)
      (maybe_r2l_write_weaken parse_long_argument_kind
        (maybe_r2l_write_synth'
          (maybe_r2l_write_filter
            (maybe_r2l_write_constant_size write_u16 2sz)
            uint16_wf
          )
          (LongArgumentU16 ())
          LongArgumentU16?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU32 _ _ ->
    rewrite_maybe_r2l_writer
      #_ #(long_argument b)
      (maybe_r2l_write_weaken parse_long_argument_kind
        (maybe_r2l_write_synth'
          (maybe_r2l_write_filter
            (maybe_r2l_write_constant_size write_u32 4sz)
            uint32_wf
          )
          (LongArgumentU32 ())
          LongArgumentU32?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU64 _ _ ->
    rewrite_maybe_r2l_writer
      #_ #(long_argument b)
      (maybe_r2l_write_weaken parse_long_argument_kind
        (maybe_r2l_write_synth'
          (maybe_r2l_write_filter
            (maybe_r2l_write_constant_size write_u64 8sz)
            uint64_wf
          )
          (LongArgumentU64 ())
          LongArgumentU64?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentOther additional_info _ _ ->
    rewrite_maybe_r2l_writer
      #_ #(long_argument b)
      (maybe_r2l_write_weaken parse_long_argument_kind
        (maybe_r2l_write_synth'
          (maybe_r2l_write_constant_size exact_write_empty 0sz)
          (LongArgumentOther additional_info ())
          LongArgumentOther?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a

inline_for_extraction
noextract
let size_comp_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (size_comp_for (serialize_long_argument b) a)
= match a with
  | LongArgumentSimpleValue _ _ ->
    rewrite_size_comp
      #_ #(long_argument b)
      (size_comp_weaken parse_long_argument_kind
        (size_comp_synth'
          (size_comp_filter
            (size_comp_constant_size serialize_u8 1sz)
            simple_value_long_argument_wf
          )
          (LongArgumentSimpleValue ())
          LongArgumentSimpleValue?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU8 _ _ ->
    rewrite_size_comp
      #_ #(long_argument b)
      (size_comp_weaken parse_long_argument_kind
        (size_comp_synth'
          (size_comp_filter
            (size_comp_constant_size serialize_u8 1sz)
            uint8_wf
          )
          (LongArgumentU8 ())
          LongArgumentU8?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU16 _ _ ->
    rewrite_size_comp
      #_ #(long_argument b)
      (size_comp_weaken parse_long_argument_kind
        (size_comp_synth'
          (size_comp_filter
            (size_comp_constant_size serialize_u16 2sz)
            uint16_wf
          )
          (LongArgumentU16 ())
          LongArgumentU16?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU32 _ _ ->
    rewrite_size_comp
      #_ #(long_argument b)
      (size_comp_weaken parse_long_argument_kind
        (size_comp_synth'
          (size_comp_filter
            (size_comp_constant_size serialize_u32 4sz)
            uint32_wf
          )
          (LongArgumentU32 ())
          LongArgumentU32?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU64 _ _ ->
    rewrite_size_comp
      #_ #(long_argument b)
      (size_comp_weaken parse_long_argument_kind
        (size_comp_synth'
          (size_comp_filter
            (size_comp_constant_size serialize_u64 8sz)
            uint64_wf
          )
          (LongArgumentU64 ())
          LongArgumentU64?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentOther additional_info _ _ ->
    rewrite_size_comp
      #_ #(long_argument b)
      (size_comp_weaken parse_long_argument_kind
        (size_comp_synth'
          (size_comp_constant_size serialize_empty 0sz)
          (LongArgumentOther additional_info ())
          LongArgumentOther?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a

inline_for_extraction
noextract
let l2r_write_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (l2r_writer_for (serialize_long_argument b) a)
= match a with
  | LongArgumentSimpleValue _ _ ->
    rewrite_l2r_writer
      #_ #(long_argument b)
      (l2r_write_weaken parse_long_argument_kind
        (l2r_write_synth'
          (l2r_write_filter
            (l2r_write_constant_size write_u8 1sz)
            simple_value_long_argument_wf
          )
          (LongArgumentSimpleValue ())
          LongArgumentSimpleValue?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU8 _ _ ->
    rewrite_l2r_writer
      #_ #(long_argument b)
      (l2r_write_weaken parse_long_argument_kind
        (l2r_write_synth'
          (l2r_write_filter
            (l2r_write_constant_size write_u8 1sz)
            uint8_wf
          )
          (LongArgumentU8 ())
          LongArgumentU8?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU16 _ _ ->
    rewrite_l2r_writer
      #_ #(long_argument b)
      (l2r_write_weaken parse_long_argument_kind
        (l2r_write_synth'
          (l2r_write_filter
            (l2r_write_constant_size write_u16 2sz)
            uint16_wf
          )
          (LongArgumentU16 ())
          LongArgumentU16?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU32 _ _ ->
    rewrite_l2r_writer
      #_ #(long_argument b)
      (l2r_write_weaken parse_long_argument_kind
        (l2r_write_synth'
          (l2r_write_filter
            (l2r_write_constant_size write_u32 4sz)
            uint32_wf
          )
          (LongArgumentU32 ())
          LongArgumentU32?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentU64 _ _ ->
    rewrite_l2r_writer
      #_ #(long_argument b)
      (l2r_write_weaken parse_long_argument_kind
        (l2r_write_synth'
          (l2r_write_filter
            (l2r_write_constant_size write_u64 8sz)
            uint64_wf
          )
          (LongArgumentU64 ())
          LongArgumentU64?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a
  | LongArgumentOther additional_info _ _ ->
    rewrite_l2r_writer
      #_ #(long_argument b)
      (l2r_write_weaken parse_long_argument_kind
        (l2r_write_synth'
          (l2r_write_constant_size exact_write_empty 0sz)
          (LongArgumentOther additional_info ())
          LongArgumentOther?.v
          ()
        )
        ()
      )
      (serialize_long_argument b)
      a

#pop-options

inline_for_extraction
noextract
let write_header : maybe_r2l_writer serialize_header
=
  maybe_r2l_write_dtuple2
    (maybe_r2l_write_constant_size write_initial_byte' 1sz)
    write_long_argument

inline_for_extraction
noextract
let size_comp_header : size_comp serialize_header
=
  size_comp_dtuple2
    (size_comp_constant_size serialize_initial_byte 1sz)
    size_comp_long_argument

inline_for_extraction
noextract
let l2r_write_header : l2r_writer serialize_header
=
  l2r_write_dtuple2
    (l2r_write_constant_size write_initial_byte' 1sz)
    l2r_write_long_argument

inline_for_extraction
noextract
let write_simple_value_as_argument
  (x: simple_value)
: Tot (maybe_r2l_writer_for serialize_header (simple_value_as_argument x))
= cps_simple_value_as_argument
    (maybe_r2l_writer_for serialize_header (simple_value_as_argument x))
    (ifthenelse_maybe_r2l_writer_for serialize_header (simple_value_as_argument x))
    x
    (fun h out ->
      let res = write_header h out in
      vpattern_rewrite
        (fun v -> maybe_r2l_write serialize_header out _ v _)
        (simple_value_as_argument x);
      return res
    )

inline_for_extraction
noextract
let size_comp_simple_value_as_argument
  (x: simple_value)
: Tot (size_comp_for serialize_header (simple_value_as_argument x))
= cps_simple_value_as_argument
    (size_comp_for serialize_header (simple_value_as_argument x))
    (ifthenelse_size_comp_for serialize_header (simple_value_as_argument x))
    x
    (fun h sz perr ->
      let res = size_comp_header h sz perr in
      let _ = gen_elim () in
      return res
    )

inline_for_extraction
noextract
let l2r_write_simple_value_as_argument
  (x: simple_value)
: Tot (l2r_writer_for serialize_header (simple_value_as_argument x))
= cps_simple_value_as_argument
    (l2r_writer_for serialize_header (simple_value_as_argument x))
    (ifthenelse_l2r_writer_for serialize_header (simple_value_as_argument x))
    x
    (fun h out ->
      let res = l2r_write_header h out in
      let _ = gen_elim () in
      return res
    )

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

module W = LowParse.SteelST.R2LOutput

let maybe_r2l_write_simple_value
  (#opened: _)
  (x: simple_value)
  (#vout: _)
  (out: W.t)
  (success: bool)
: STGhostT unit opened
   (maybe_r2l_write serialize_header out vout (simple_value_as_argument x) success)
   (fun _ -> maybe_r2l_write serialize_raw_data_item out vout (Simple x) success)
= if success
  then begin
    let a = ghost_elim_maybe_r2l_write_success serialize_header out in
    let _ = gen_elim () in
    let a' = aparse_split_zero_r parse_header a in
    let _ = gen_elim () in
    let _ = intro_aparse parse_empty a' in
    let _ = rewrite_aparse a' (parse_content parse_raw_data_item (simple_value_as_argument x)) in
    let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a' in
    Classical.forall_intro parse_raw_data_item_eq;
    let _ = intro_synth _ synth_raw_data_item a () in
    let _ = rewrite_aparse a parse_raw_data_item in
    intro_maybe_r2l_write_success serialize_raw_data_item out vout (Simple x) _ _ _;
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (Simple x)) success
  end else begin
    elim_maybe_r2l_write_failure serialize_header out;
    serialize_raw_data_item_aux_correct (Simple x);
    serialize_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip () (Simple x);
    serialize_dtuple2_eq serialize_header serialize_content (| simple_value_as_argument x, () |);
    noop ();
    intro_maybe_r2l_write_failure serialize_raw_data_item out vout (Simple x);
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (Simple x)) success
  end

#pop-options

inline_for_extraction // necessary for the reexport into CBOR.SteelST
let write_simple_value
  (x: simple_value)
: Tot (maybe_r2l_writer_for serialize_raw_data_item (Simple x))
= fun out ->
    let res = write_simple_value_as_argument x out in
    maybe_r2l_write_simple_value x out res;
    return res

let write_uint64_as_argument
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
: Tot (maybe_r2l_writer_for serialize_header (uint64_as_argument ty x))
= cps_uint64_as_argument
    (maybe_r2l_writer_for serialize_header (uint64_as_argument ty x))
    (ifthenelse_maybe_r2l_writer_for serialize_header (uint64_as_argument ty x))
    ty
    x
    (fun h out ->
      let res = write_header h out in
      vpattern_rewrite
        (fun v -> maybe_r2l_write serialize_header out _ v _)
        (uint64_as_argument ty x);
      return res
    )

inline_for_extraction
noextract
let size_comp_simple_value_header
  (x: simple_value)
: Tot (size_comp_for serialize_header (simple_value_as_argument x))
= cps_simple_value_as_argument
    (size_comp_for serialize_header (simple_value_as_argument x))
    (ifthenelse_size_comp_for serialize_header (simple_value_as_argument x))
    x
    (fun k -> coerce _ (size_comp_header k))

inline_for_extraction
let size_comp_simple_value
  (x: simple_value)
: Tot (size_comp_for serialize_raw_data_item (Simple x))
= Classical.forall_intro parse_raw_data_item_eq;
  rewrite_size_comp_for
    serialize_raw_data_item_aux
    (Simple x)
    (coerce _ (size_comp_synth_for
      (serialize_dtuple2 serialize_header serialize_content)
      synth_raw_data_item
      synth_raw_data_item_recip
      (Simple x)
      (| simple_value_as_argument x, () |)
      (size_comp_dtuple2_for
        serialize_header
        serialize_content
        (| simple_value_as_argument x, () |)
        (simple_value_as_argument x)
        ()
        (size_comp_simple_value_header x)
        (coerce _ (size_comp_weaken
          parse_content_kind
          (size_comp_constant_size serialize_empty 0sz)
          ()
          ()
        ))
      )
      ()
    ))
    _

inline_for_extraction
noextract
let l2r_write_simple_value_header
  (x: simple_value)
: Tot (l2r_writer_for serialize_header (simple_value_as_argument x))
= cps_simple_value_as_argument
    (l2r_writer_for serialize_header (simple_value_as_argument x))
    (ifthenelse_l2r_writer_for serialize_header (simple_value_as_argument x))
    x
    (fun k -> coerce _ (l2r_write_header k))

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

inline_for_extraction
let l2r_write_simple_value
  (x: simple_value)
: Tot (l2r_writer_for serialize_raw_data_item (Simple x))
= Classical.forall_intro parse_raw_data_item_eq;
  rewrite_l2r_writer_for
    serialize_raw_data_item_aux
    (Simple x)
    (coerce _ (l2r_write_synth_for
      (serialize_dtuple2 serialize_header serialize_content)
      synth_raw_data_item
      synth_raw_data_item_recip
      (Simple x)
      (| simple_value_as_argument x, () |)
      (l2r_write_dtuple2_for
        serialize_header
        serialize_content
        (| simple_value_as_argument x, () |)
        (simple_value_as_argument x)
        ()
        (l2r_write_simple_value_header x)
        (coerce _ (l2r_write_weaken
          parse_content_kind
          (l2r_write_constant_size exact_write_empty 0sz)
          ()
          ()
        ))
      )
      ()
    ))
    serialize_raw_data_item

#pop-options

inline_for_extraction
noextract
let size_comp_uint64_header
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
: Tot (size_comp_for serialize_header (uint64_as_argument ty x))
= cps_uint64_as_argument
    (size_comp_for serialize_header (uint64_as_argument ty x))
    (ifthenelse_size_comp_for serialize_header (uint64_as_argument ty x))
    ty
    x
    (fun k -> coerce _ (size_comp_header k))

inline_for_extraction
let size_comp_int64
  (ty: major_type_uint64_or_neg_int64)
  (x: U64.t)
: Tot (size_comp_for serialize_raw_data_item (Int64 ty x))
= Classical.forall_intro parse_raw_data_item_eq;
  rewrite_size_comp_for
    serialize_raw_data_item_aux
    (Int64 ty x)
    (coerce _ (size_comp_synth_for
      (serialize_dtuple2 serialize_header serialize_content)
      synth_raw_data_item
      synth_raw_data_item_recip
      (Int64 ty x)
      (| uint64_as_argument ty x, () |)
      (size_comp_dtuple2_for
        serialize_header
        serialize_content
        (| uint64_as_argument ty x, () |)
        (uint64_as_argument ty x)
        ()
        (size_comp_uint64_header ty x)
        (coerce _ (size_comp_weaken
          parse_content_kind
          (size_comp_constant_size serialize_empty 0sz)
          ()
          ()
        ))
      )
      ()
    ))
    _

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

inline_for_extraction
let size_comp_string
  (ty: major_type_byte_string_or_text_string)
  (x: U64.t)
  (v: Ghost.erased (Seq.seq byte) { Seq.length v == U64.v x /\ SZ.fits_u64 })
: Tot (size_comp_for serialize_raw_data_item (String ty (Ghost.reveal v)))
= Classical.forall_intro parse_raw_data_item_eq;
  rewrite_size_comp_for
    serialize_raw_data_item_aux
    (Ghost.hide (String ty (Ghost.reveal v)))
    (coerce _ 
      (size_comp_synth_for
        (serialize_dtuple2 serialize_header serialize_content)
        synth_raw_data_item
        synth_raw_data_item_recip
        (Ghost.hide (String ty (Ghost.reveal v)))
        (Ghost.hide (| uint64_as_argument ty x, Ghost.reveal v |))
        (size_comp_dtuple2_for
          serialize_header
          serialize_content
          (Ghost.hide (| uint64_as_argument ty x, Ghost.reveal v |))
          (Ghost.hide (uint64_as_argument ty x))
          (Ghost.hide (Ghost.reveal v))
          (size_comp_uint64_header ty x)
          (coerce _ (rewrite_size_comp_for
            (serialize_weaken parse_content_kind (serialize_lseq_bytes (U64.v x)))
            (Ghost.hide (Ghost.reveal v))
            (size_comp_weaken_for
              parse_content_kind
              (serialize_lseq_bytes (U64.v x))
              (Ghost.hide (Ghost.reveal v))
              (size_comp_constant_size_for
                (serialize_lseq_bytes (U64.v x))
                (SZ.uint64_to_sizet x)
                (Ghost.hide (Ghost.reveal v))
              )
              ()
            )
            (serialize_content (uint64_as_argument ty x))
          ))
        )
        ()
      )
    )
    _

#pop-options

inline_for_extraction
noextract
let l2r_write_uint64_header
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
: Tot (l2r_writer_for serialize_header (uint64_as_argument ty x))
= cps_uint64_as_argument
    (l2r_writer_for serialize_header (uint64_as_argument ty x))
    (ifthenelse_l2r_writer_for serialize_header (uint64_as_argument ty x))
    ty
    x
    (fun k -> coerce _ (l2r_write_header k))

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

inline_for_extraction
let l2r_write_int64
  (ty: major_type_uint64_or_neg_int64)
  (x: U64.t)
: Tot (l2r_writer_for serialize_raw_data_item (Int64 ty x))
= Classical.forall_intro parse_raw_data_item_eq;
  rewrite_l2r_writer_for
    serialize_raw_data_item_aux
    (Int64 ty x)
    (coerce _ (l2r_write_synth_for
      (serialize_dtuple2 serialize_header serialize_content)
      synth_raw_data_item
      synth_raw_data_item_recip
      (Int64 ty x)
      (| uint64_as_argument ty x, () |)
      (l2r_write_dtuple2_for
        serialize_header
        serialize_content
        (| uint64_as_argument ty x, () |)
        (uint64_as_argument ty x)
        ()
        (l2r_write_uint64_header ty x)
        (coerce _ (l2r_write_weaken
          parse_content_kind
          (l2r_write_constant_size exact_write_empty 0sz)
          ()
          ()
        ))
      )
      ()
    ))
    serialize_raw_data_item

#pop-options

#push-options "--z3rlimit 32 --split_queries always"
#restart-solver

let maybe_r2l_write_int64
  (#opened: _)
  (m: major_type_uint64_or_neg_int64)
  (x: U64.t)
  (#vout: _)
  (out: W.t)
  (success: bool)
: STGhostT unit opened
   (maybe_r2l_write serialize_header out vout (uint64_as_argument m x) success)
   (fun _ -> maybe_r2l_write serialize_raw_data_item out vout (Int64 m x) success)
= if success
  then begin
    let a = ghost_elim_maybe_r2l_write_success serialize_header out in
    let _ = gen_elim () in
    let a' = aparse_split_zero_r parse_header a in
    let _ = gen_elim () in
    let _ = intro_aparse parse_empty a' in
    let _ = rewrite_aparse a' (parse_content parse_raw_data_item (uint64_as_argument m x)) in
    let _ = intro_dtuple2 parse_header (parse_content parse_raw_data_item) a a' in
    Classical.forall_intro parse_raw_data_item_eq;
    let _ = intro_synth _ synth_raw_data_item a () in
    let _ = rewrite_aparse a parse_raw_data_item in
    intro_maybe_r2l_write_success serialize_raw_data_item out vout (Int64 m x) _ _ _;
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (Int64 m x)) success
  end else begin
    elim_maybe_r2l_write_failure serialize_header out;
    serialize_raw_data_item_aux_correct (Int64 m x);
    serialize_synth_eq (parse_dtuple2 parse_header (parse_content parse_raw_data_item)) synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip () (Int64 m x);
    serialize_dtuple2_eq serialize_header serialize_content (| uint64_as_argument m x, () |);
    noop ();
    intro_maybe_r2l_write_failure serialize_raw_data_item out vout (Int64 m x);
    vpattern_rewrite (maybe_r2l_write serialize_raw_data_item out vout (Int64 m x)) success
  end

#pop-options

inline_for_extraction // necessary for the reexport into CBOR.SteelST
let write_int64
  (m: major_type_uint64_or_neg_int64)
  (x: U64.t)
: Tot (maybe_r2l_writer_for serialize_raw_data_item (Int64 m x))
= fun out ->
    let res = write_uint64_as_argument m x out in
    maybe_r2l_write_int64 m x out res;
    return res

let finalize_raw_data_item_string_post_prop
  (m: major_type_byte_string_or_text_string)
  (va: v parse_raw_data_item_kind raw_data_item)
  (vp: AP.v byte)
: GTot prop
=
        FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
        va.contents == String m (AP.contents_of vp)

let finalize_raw_data_item_string_failure
  (m: major_type_byte_string_or_text_string)
  (vout: AP.array byte)
  (vp: AP.v byte)
: GTot prop
= 
  FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
  Seq.length (serialize serialize_raw_data_item (String m (AP.contents_of vp))) > AP.length vout + AP.length (AP.array_of vp)

[@@__reduce__]
let finalize_raw_data_item_string_post
  (m: major_type_byte_string_or_text_string)
  (vout: AP.array byte)
  (out: W.t)
  (vp: AP.v byte)
  (ap: byte_array)
  (res: bool)
: Tot vprop
=
      ifthenelse_vprop
        res
        (fun _ -> exists_ (fun vout' -> exists_ (fun a -> exists_ (fun va ->
          aparse parse_raw_data_item a va `star`
          W.vp out vout' `star`
          pure (
            AP.adjacent vout (AP.array_of vp) /\
            AP.merge_into vout' (array_of va) (AP.merge vout (AP.array_of vp)) /\
            finalize_raw_data_item_string_post_prop m va vp
        )))))
        (fun _ ->
          pure (finalize_raw_data_item_string_failure m vout vp) `star`
          W.vp out vout `star` AP.arrayptr ap vp
        )

#push-options "--z3rlimit 32"
#restart-solver

let maybe_finalize_raw_data_item_string
  (#opened: _)
  (m: major_type_byte_string_or_text_string)
  (#vout: _)
  (out: W.t)
  (#vp: _)
  (ap: byte_array)
  (len: U64.t)
  (res: bool)
: STGhost unit opened
    (maybe_r2l_write serialize_header out vout (uint64_as_argument m len) res `star`
      AP.arrayptr ap vp
    )
    (fun _ ->
      finalize_raw_data_item_string_post m vout out vp ap res
    )
    (U64.v len == AP.length (AP.array_of vp) /\
      AP.adjacent vout (AP.array_of vp)
    )
    (fun _ -> True)
=
  if res
  then begin
      let ah = ghost_elim_maybe_r2l_write_success serialize_header out in
      let _ = gen_elim () in
      let _ = intro_raw_data_item_string m ah ap in
      noop ();
      intro_ifthenelse_vprop_true res _ _ ()
    end else begin
      elim_maybe_r2l_write_failure serialize_header out;
      serialize_raw_data_item_aux_correct (String m (AP.contents_of vp));
      serialize_synth_eq _ synth_raw_data_item (serialize_dtuple2 serialize_header serialize_content) synth_raw_data_item_recip () (String m (AP.contents_of vp));
      serialize_dtuple2_eq serialize_header serialize_content (| uint64_as_argument m len, AP.contents_of vp |);
      noop ();
      intro_ifthenelse_vprop_false res _ _ ()
    end

#pop-options

inline_for_extraction // necessary for the reexport into CBOR.SteelST
let finalize_raw_data_item_string
  (m: major_type_byte_string_or_text_string)
  (#vout: _)
  (out: W.t)
  (#vp: _)
  (ap: Ghost.erased byte_array)
  (len: U64.t)
: ST bool
    (W.vp out vout `star` AP.arrayptr ap vp)
    (fun res -> finalize_raw_data_item_string_post m vout out vp ap res)
    (U64.v len == AP.length (AP.array_of vp) /\
      AP.adjacent vout (AP.array_of vp)
    )
    (fun _ -> True)
= let res = write_uint64_as_argument m len out in
  maybe_finalize_raw_data_item_string m out ap len res;
  return res
