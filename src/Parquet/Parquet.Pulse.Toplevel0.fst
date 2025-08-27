module Parquet.Pulse.Toplevel0
#lang-pulse
open Pulse.Lib.Pervasives
open LowParse.Pulse.Combinators
open Parquet.Pulse.Jump
open LowParse.Pulse.SeqBytes
open LowParse.Pulse.Int
open LowParse.Pulse.FLData
include Parquet.Spec.Toplevel

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module Rel = CDDL.Pulse.Types.Base
module PV = Parquet.Pulse.Vec
module U64 = FStar.UInt64
module U32 = FStar.UInt32

module U32 = FStar.UInt32
module U8 = FStar.UInt8

include Parquet.Pulse.Rel

fn validate_is_PAR1 ()
: validate_filter_test_t
  #_ #_ #_
  (serialize_seq_flbytes 4)
  is_PAR1

=
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased Seq.lseq byte 4)
{

  unfold (pts_to_serialized (serialize_seq_flbytes 4) input #pm v);
  S.pts_to_len input #pm #v;
  let v0 = S.op_Array_Access input 0sz;
  let v1 = S.op_Array_Access input 1sz;
  let v2 = S.op_Array_Access input 2sz;
  let v3 = S.op_Array_Access input 3sz;
  let res = (
    (80uy = v0) && // 'P'
    (65uy = v1) && // 'A'
    (82uy = v2) && // 'R'
    (49uy = v3)    // '1'
  );
  fold (pts_to_serialized (serialize_seq_flbytes 4) input #pm v);
  res
}

assume val validate_footer : validator parse_footer

assume val read_footer : zero_copy_parse rel_file_meta_data serialize_footer

[@@pulse_unfold] noextract
let pts_to_bytes (pm: perm) (x: S.slice byte) (y: bytes) : Tot slprop =
  pts_to x #pm y

noextract [@@noextract_to "krml"]
let list_for_all_option_map_pred
  (#t1 #t2: Type)
  (f: (t1 -> option t2))
  (p: (t2 -> bool))
  (x: t1)
: Tot bool
= match f x with
  | None -> true
  | Some y -> p y

let rec list_for_all_option_map
  (#t1 #t2: Type)
  (f: (t1 -> option t2))
  (p: (t2 -> bool))
  (l: list t1)
: Lemma
  (List.Tot.for_all p (list_option_map f l) == List.Tot.for_all (list_for_all_option_map_pred f p) l)
= match l with
  | [] -> ()
  | a :: q -> list_for_all_option_map f p q

module I64 = FStar.Int64

noextract [@@noextract_to "krml"]
let compute_cols_size_postcond
  (vcc: list Parquet.Spec.Toplevel.Types.column_chunk)
  (bound: I64.t)
  (overflow: bool)
  (res: option I64.t)
: Tot prop
= match cols_size vcc, res with
  | None, None -> True
  | Some md, Some md' ->
    if overflow then md > I64.v bound else md == I64.v md'
  | _ -> False

noextract [@@noextract_to "krml"]
let column_size_nonnegative
  (cc: column_chunk)
: Tot bool
= match cc.meta_data with
  | None -> true
  | Some md -> I64.v md.total_compressed_size >= 0

let rec cols_size_nonnegative
  (cc: list column_chunk)
: Lemma
  (ensures (List.Tot.for_all column_size_nonnegative cc ==> begin match cols_size cc with
  | None -> True
  | Some sz -> sz >= 0
  end
  ))
  [SMTPat (cols_size cc)]
= match cc with
  | [] -> ()
  | c :: q -> cols_size_nonnegative q

noextract [@@noextract_to "krml"]
let compute_cols_size_invariant
  (bound: I64.t)
  (vcc: list Parquet.Spec.Toplevel.Types.column_chunk)
  (vccr: list Parquet.Spec.Toplevel.Types.column_chunk)
  (overflow: bool)
  (accu: option I64.t)
: Tot prop
= List.Tot.for_all column_size_nonnegative vccr /\
  begin match accu with
  | Some accu' -> 0 <= I64.v accu' /\ ((~ overflow) ==> I64.v accu' <= I64.v bound)
  | None -> True
  end /\
  begin match accu, cols_size vcc, cols_size vccr with
  | _, None, None -> True
  | Some accu', Some md, Some md' -> if overflow then md > I64.v bound else md == I64.v accu' + md'
  | _ -> False
  end

module Vec = Pulse.Lib.Vec
module SM = Pulse.Lib.SeqMatch.Util

fn compute_cols_size
  (poverflow: ref bool)
  (#overflow0: Ghost.erased bool)
  (cc: PV.vec Parquet.Pulse.Toplevel.column_chunk)
  (#vcc: Ghost.erased (list Parquet.Spec.Toplevel.Types.column_chunk))
  (bound: I64.t)
requires
  PV.rel_vec_of_list rel_column_chunk cc vcc **
  pts_to poverflow overflow0 **
  pure (List.Tot.for_all column_size_nonnegative vcc)
returns res: option I64.t
ensures exists* overflow .
  PV.rel_vec_of_list rel_column_chunk cc vcc **
  pts_to poverflow overflow **
  pure (compute_cols_size_postcond vcc bound overflow res)
{
  poverflow := (I64.lt bound 0L);
  unfold (PV.rel_vec_of_list rel_column_chunk cc vcc);
  with s . assert (Vec.pts_to cc.data s);
  Vec.pts_to_len cc.data;
  SM.seq_list_match_length rel_column_chunk _ _;
  Trade.refl (SM.seq_list_match s vcc rel_column_chunk);
  let mut paccu = Some 0L;
  let mut pi = 0sz;
  while (
    let accu = !paccu;
    if (Some? accu) {
      let i = !pi;
      SZ.lt i cc.len
    } else {
      false
    }
  ) invariant b . exists* sr vcr accu i overflow .
    Vec.pts_to cc.data s **
    SM.seq_list_match sr vcr rel_column_chunk **
    pts_to paccu accu **
    pts_to pi i **
    pts_to poverflow overflow **
    Trade.trade (SM.seq_list_match sr vcr rel_column_chunk) (SM.seq_list_match s vcc rel_column_chunk) **
    pure (
      compute_cols_size_invariant bound vcc vcr overflow accu /\
      SZ.v i <= Seq.length s /\
      sr == Seq.slice s (SZ.v i) (Seq.length s) /\
      b == (Some? accu && SZ.v i < Seq.length s)
    )
  {
    SM.seq_list_match_length rel_column_chunk _ _;
    SM.seq_list_match_cons_elim_trade _ _ rel_column_chunk;
    with gimpl gspec . assert (rel_column_chunk gimpl gspec);
    let i = !pi;
    let impl = Vec.op_Array_Access cc.data i;
    rewrite each gimpl as impl;
    unfold (rel_column_chunk impl gspec);
    Rel.rel_option_cases rel_column_meta_data impl.meta_data gspec.meta_data;
    match impl.meta_data {
      None -> {
        fold (rel_column_chunk impl gspec);
        Trade.elim (rel_column_chunk _ _ ** _) _;
        paccu := None;
      }
      Some md -> {
        Rel.rel_option_eq_some rel_column_meta_data md (Some?.v gspec.meta_data);
        Trade.rewrite_with_trade
          (rel_opt rel_column_meta_data impl.meta_data gspec.meta_data)
          (rel_column_meta_data md (Some?.v gspec.meta_data));
        unfold (rel_column_meta_data md (Some?.v gspec.meta_data));
        Rel.rel_pure_peek md.total_compressed_size _;
        fold (rel_column_meta_data md (Some?.v gspec.meta_data));
        Trade.elim (rel_column_meta_data _ _) _;
        fold (rel_column_chunk impl gspec);
        Trade.elim_hyp_l (rel_column_chunk _ _) _ _;
        Trade.trans _ _ (SM.seq_list_match s vcc rel_column_chunk);
        let overflow = !poverflow;
        pi := SZ.add i 1sz;
        if (not overflow) {
          let accu = Some?.v !paccu;
          if (I64.lt (I64.sub bound accu) md.total_compressed_size) {
            poverflow := true;
          } else {
            paccu := Some (I64.add accu md.total_compressed_size);
          }
        }
      }
    }
  };
  SM.seq_list_match_length rel_column_chunk _ _;
  Trade.elim _ _;
  fold (PV.rel_vec_of_list rel_column_chunk cc vcc);
  !paccu
}

fn impl_validate_file_meta_data (footer_start: SZ.t) : PV.impl_pred #_ #_ emp rel_file_meta_data (validate_file_meta_data (SZ.v footer_start)) =
  (md: _)
  (vmd: _)
{
  admit ()
}

fn impl_validate_offset_index_all (pm: perm) : PV.impl_pred3 #_ #_ #_ #_ #_ #_ emp rel_column_chunk (pts_to_bytes pm) rel_offset_index validate_offset_index_all
=
  (cc: _)
  (vcc: _)
  (data: _)
  (vdata: _)
  (oi: _)
  (voi: _)
{
  admit ()
}

module I32 = FStar.Int32

assume val validate_offset_index : validator (parser_of_tot_parser parse_offset_index)

assume val read_offset_index : zero_copy_parse rel_offset_index (serializer_of_tot_serializer serialize_offset_index)

fn impl_validate_offset_index_all0
  (pm: perm)
  (data: Pulse.Lib.Slice.slice byte)
  (vdata: erased bytes)
  (cc: Toplevel.column_chunk)
  (vcc: erased column_chunk)
:
validate_filter_test_gen_t (pts_to_bytes pm data vdata ** rel_column_chunk cc vcc) #_ #_ #_
  (serializer_of_tot_serializer serialize_offset_index)
  (validate_offset_index_all vcc vdata)
=
  (x: _)
  (#pm': _)
  (#v' : _)
{
  let oi = read_offset_index x;
  let res = impl_validate_offset_index_all _ cc _ data _ oi _;
  Trade.elim _ _;
  res
}

let validate_jump_offset_index (offset_sz: SZ.t) (length_sz: SZ.t) (pm: perm) (data: S.slice byte) (vdata: Ghost.erased bytes) (cc: Parquet.Pulse.Toplevel.column_chunk) (vcc: Ghost.erased column_chunk) =
  validate_jump_with_offset_and_size_then_parse
    (pts_to_bytes pm data vdata ** rel_column_chunk cc vcc) offset_sz length_sz 
    (validate_gen_ext 
      (validate_filter_gen' (validator_gen_of_validator _ validate_offset_index) (serializer_of_tot_serializer serialize_offset_index) (validate_offset_index_all vcc vdata) (impl_validate_offset_index_all0 pm data vdata cc vcc))
      (parser_of_tot_parser (tot_parse_filter parse_offset_index (validate_offset_index_all vcc vdata)))
    )

fn impl_validate_all_validate_column_chunk (pm: perm) : PV.impl_pred2 #_ #_ #_ #_ emp (pts_to_bytes pm) rel_column_chunk validate_all_validate_column_chunk
=
  (data: _)
  (vdata: _)
  (cc: _)
  (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_pure_peek cc.offset_index_offset _;
  Rel.rel_pure_peek cc.offset_index_length _;
  fold (rel_column_chunk cc vcc);
  if (Some? cc.offset_index_offset && Some? cc.offset_index_length) {
    let Some offset = cc.offset_index_offset;
    let Some length = cc.offset_index_length;
    assume (pure (SZ.fits_u64));
    assume (pure (SZ.fits_u32));
    let offset_sz = SZ.uint64_to_sizet (FStar.Int.Cast.int64_to_uint64 offset);
    let length_sz = SZ.uint32_to_sizet (FStar.Int.Cast.int32_to_uint32 length);
    if (I64.lte 0L offset && I32.lte 0l length) {
      S.share data;
      tot_parse_filter_equiv parse_offset_index (validate_offset_index_all vcc vdata) (parser_of_tot_parser parse_offset_index);
      let res = validate_jump_offset_index offset_sz length_sz _ data vdata cc vcc data _;
      S.gather data;
      res
    } else {
      false
    }
  } else {
    true
  }
}

fn impl_validate_all_validate_row_group (pm: perm) : PV.impl_pred2 #_ #_ #_ #_ emp (pts_to_bytes pm) rel_row_group validate_all_validate_row_group
=
  (data: _)
  (vdata: _)
  (rg: _)
  (vrg: _)
{
  unfold (rel_row_group rg vrg);
  let res = PV.impl_for_all _ _ _ (impl_validate_all_validate_column_chunk pm data vdata) rg.columns _;
  fold (rel_row_group rg vrg);
  res
}

let validate_header_magic_number =
  let _ = tot_parse_filter_equiv (tot_parse_seq_flbytes 4) is_PAR1 (parse_seq_flbytes 4) in
  validate_jump_with_offset_and_size_then_parse emp 0sz 4sz (validator_gen_of_validator emp (validate_ext (validate_filter_gen (validate_total_constant_size (parse_seq_flbytes 4) 4sz) (serialize_seq_flbytes 4) is_PAR1 (validate_is_PAR1 ())) (parser_of_tot_parser (tot_parse_filter (tot_parse_seq_flbytes 4) is_PAR1))))

fn impl_validate_all0 (pm: perm) : PV.impl_pred2 #_ #_ #_ #_ emp rel_file_meta_data (pts_to_bytes pm) validate_all
=
  (fmd: _)
  (vfmd: _)
  (data: _)
  (vdata: _)
{
  S.pts_to_len data;
  let footer_start = S.len data;
  let res1 = impl_validate_file_meta_data footer_start fmd _;
  if (res1) {
    tot_parse_filter_equiv (tot_parse_seq_flbytes 4) is_PAR1 (parse_seq_flbytes 4);
    let res2 = validate_header_magic_number data vdata;
    if (res2) {
      unfold (rel_file_meta_data fmd vfmd);
      let res = PV.impl_for_all _ _ _ (impl_validate_all_validate_row_group pm data vdata) fmd.row_groups vfmd.row_groups;
      fold (rel_file_meta_data fmd vfmd);
      res
    } else {
      false
    }
  } else {
    false
  }
}

fn impl_validate_all
  (len: U32.t)
  (footer: Ghost.erased (parse_fldata_strong_t serialize_footer (U32.v len)))
  (y: Pulse.Lib.Slice.slice LowParse.Bytes.byte)
  (pm: perm)
:
validate_filter_test_gen_t (pts_to_serialized (serialize_fldata_strong serialize_footer (U32.v len))
      y  #pm
      footer)
  #_ #_ #_
  serialize_seq_all_bytes
  (validate_all footer)
=
  (x: _)
  (#pm': _)
  (#v: _)
{
  pts_to_serialized_fldata_strong_elim_trade serialize_footer (U32.v len) y;
  let f = read_footer y;
  Trade.trans (rel_file_meta_data _ _) _ _;
  pts_to_serialized_elim_trade serialize_seq_all_bytes x;
  let res = impl_validate_all0 _ f _ x _;
  Trade.elim (pts_to_bytes _ x _) _;
  Trade.elim (rel_file_meta_data _ _) _;
  res
}

let validate_parquet (sq: squash SZ.fits_u32) : validator parse_parquet =
  validate_nondep_then_rtol
    4sz
    (validate_dtuple2_rtol
      4sz
      (leaf_reader_of_reader read_u32_le)
      (fun len -> validate_weaken (dtuple2_rtol_kind parse_seq_all_bytes_kind 0)
        (validate_dtuple2_rtol_gen
          (SZ.uint32_to_sizet len)
          (serialize_fldata_strong serialize_footer (U32.v len))
          (fun footer y pm ->
            (validate_filter_gen'
              (validator_gen_of_validator _ (validate_seq_all_bytes ()))
              serialize_seq_all_bytes
              (validate_all footer)
              (impl_validate_all len footer y pm)
              )
          )
          (validate_fldata_strong
            serialize_footer
            validate_footer
            (SZ.uint32_to_sizet len)
          )
        )
      )
      (validate_total_constant_size parse_u32_le 4sz)
    )
    (validate_filter_gen
      (validate_total_constant_size (parse_seq_flbytes 4) 4sz)
      (serialize_seq_flbytes 4)
      is_PAR1
      (validate_is_PAR1 ())
    )
