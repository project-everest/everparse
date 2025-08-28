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
    (overflow == (md > I64.v bound)) /\
    ((~ overflow) ==> md == I64.v md')
  | _ -> False

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

noextract [@@noextract_to "krml"]
let validate_file_meta_data_aux (data_size: I64.t) (rg: list row_group) : Tot bool =
  List.Tot.for_all (validate_row_group_size data_size) rg &&
  ranges_disjoint (list_option_map rg_range rg)

fn impl_column_size_nonnegative () : PV.impl_pred #_ #_  emp rel_column_chunk column_size_nonnegative
= (cc: _)
  (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  match cc.meta_data {
    norewrite
    None -> {
      fold (rel_column_chunk cc vcc);
      true
    }
    norewrite
    Some md -> {
      Trade.rewrite_with_trade
        (Rel.rel_option rel_column_meta_data _ _)
        (rel_column_meta_data md (Some?.v vcc.meta_data));
      unfold (rel_column_meta_data md (Some?.v vcc.meta_data));
      Rel.rel_pure_peek md.total_compressed_size _;
      fold (rel_column_meta_data md (Some?.v vcc.meta_data));
      Trade.elim _ _;
      fold (rel_column_chunk cc vcc);
      (I64.lte 0L md.total_compressed_size);
    }
  }
}

let rec validate_file_meta_data_aux_append (data_size: I64.t) (ll lr: list row_group) : Lemma
  (ensures validate_file_meta_data_aux data_size (List.Tot.append ll lr) ==> validate_file_meta_data_aux data_size lr)
  (decreases ll)
= match ll with
  | [] -> ()
  | a :: q -> validate_file_meta_data_aux_append data_size q lr

noextract [@@noextract_to "krml"]
let option_i64_v (x: option I64.t) : Tot (option int) =
  match x with
  | None -> None
  | Some x' -> Some (I64.v x')

noextract [@@noextract_to "krml"]
let option_i64_v_pair (x: option (I64.t & I64.t)) : Tot (option range) =
  match x with
  | None -> None
  | Some (x', y') -> Some ({ start = I64.v x'; len = I64.v y' })

module GR = Pulse.Lib.GhostReference

fn impl_offset_of_column_chunk (_: unit) : PV.impl_f_t #_ #_ #_ offset_of_column_chunk rel_column_meta_data
= (cc: _) (vcc: _) {
  unfold (rel_column_meta_data cc vcc);
  Rel.rel_pure_peek cc.dictionary_page_offset _;
  Rel.rel_pure_peek cc.index_page_offset _;
  Rel.rel_pure_peek cc.data_page_offset _;
  fold (rel_column_meta_data cc vcc);
  (match cc.dictionary_page_offset with
  | Some off -> off
  | None ->
    match cc.index_page_offset with
    | Some off -> if I64.lt off cc.data_page_offset then off else cc.data_page_offset
    | None -> cc.data_page_offset
  )
}

fn impl_validate_column_chunk_offsets_ok () : PV.impl_pred #_ #_ emp rel_column_chunk validate_column_chunk_offsets_ok =
  (cc: _)
  (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  match cc.meta_data {
    norewrite
    None -> {
      fold (rel_column_chunk cc vcc);
      true
    }
    norewrite
    Some cmd -> {
      Trade.rewrite_with_trade
        (Rel.rel_option rel_column_meta_data _ _)
        (rel_column_meta_data cmd (Some?.v vcc.meta_data));
      unfold (rel_column_meta_data cmd (Some?.v vcc.meta_data));
      Rel.rel_pure_peek cmd.data_page_offset _;
      Rel.rel_pure_peek cmd.dictionary_page_offset _;
      Rel.rel_pure_peek cmd.index_page_offset _;
      let res = (
        let data_off = cmd.data_page_offset in
        begin match cmd.dictionary_page_offset with
        | None -> true
        | Some dict_off ->
          I64.lt dict_off data_off &&
          begin match cmd.index_page_offset with
          | None -> true
          | Some idx_off -> I64.lt dict_off idx_off
          end
        end
      );
      fold (rel_column_meta_data cmd (Some?.v vcc.meta_data));
      Trade.elim _ _;
      fold (rel_column_chunk cc vcc);
      res
    }
  }
}

fn impl_validate_column_chunk_idx_ok () : PV.impl_pred #_ #_ emp rel_column_chunk validate_column_chunk_idx_ok =
  (cc: _)
  (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_pure_peek cc.offset_index_offset _;
  Rel.rel_pure_peek cc.offset_index_length _;
  Rel.rel_pure_peek cc.column_index_offset _;
  Rel.rel_pure_peek cc.column_index_length _;
  let res = (
    (Some? cc.offset_index_offset = Some? cc.offset_index_length) &&
    (Some? cc.column_index_offset = Some? cc.column_index_length) &&
    (if Some? cc.column_index_offset then Some? cc.offset_index_offset else true)
  );
  fold (rel_column_chunk cc vcc);
  res
}

fn impl_validate_column_chunk () : PV.impl_pred #_ #_ emp rel_column_chunk validate_column_chunk =
  (cc: _)
  (vcc: _)
{
  if impl_validate_column_chunk_idx_ok () cc _ {
    impl_validate_column_chunk_offsets_ok () cc _
  } else {
    false
  }
}

fn impl_column_chunk_offset () : impl_fst_f #_ #_ column_chunk_offset_and_size rel_column_chunk
= (cc: _) (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  if (Some? cc.meta_data) {
    let md = Some?.v cc.meta_data;
    Trade.rewrite_with_trade
      (Rel.rel_option rel_column_meta_data cc.meta_data _)
      (rel_column_meta_data md (Some?.v vcc.meta_data));
    let res = impl_offset_of_column_chunk () md _;
    Trade.elim _ _;
    fold (rel_column_chunk cc vcc);
    res
  } else {
    fold (rel_column_chunk cc vcc);
    0L
  }
}

fn impl_column_chunk_size () : impl_snd_f #_ #_ column_chunk_offset_and_size rel_column_chunk
= (cc: _) (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  if (Some? cc.meta_data) {
    let md = Some?.v cc.meta_data;
    Trade.rewrite_with_trade
      (Rel.rel_option rel_column_meta_data cc.meta_data _)
      (rel_column_meta_data md (Some?.v vcc.meta_data));
    unfold (rel_column_meta_data md (Some?.v vcc.meta_data));
    Rel.rel_pure_peek md.total_compressed_size _;
    fold (rel_column_meta_data md (Some?.v vcc.meta_data));
    Trade.elim _ _;
    fold (rel_column_chunk cc vcc);
    md.total_compressed_size
  } else {
    fold (rel_column_chunk cc vcc);
    0L
  }
}

fn impl_column_chunk_some_meta_data () : PV.impl_pred #_ #_ emp rel_column_chunk (fun cc -> Some? cc.meta_data)
= (cc: _) (vcc: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  let res = Some? cc.meta_data;
  fold (rel_column_chunk cc vcc);
  res
}

fn impl_validate_row_group_sorted_ok () : PV.impl_pred #_ #_ emp rel_row_group validate_row_group_sorted_ok =
  (rg: _)
  (vrg: _)
{
  unfold (rel_row_group rg vrg);
  if (PV.impl_for_all _ _ (fun cc -> Some? cc.meta_data) (impl_column_chunk_some_meta_data ()) rg.columns _) {
    let res = impl_offsets_and_sizes_are_sorted _ _ (impl_column_chunk_offset ()) (impl_column_chunk_size ()) rg.columns;
    fold (rel_row_group rg vrg);
    res
  } else {
    fold (rel_row_group rg vrg);
    true
  };
}

fn impl_validate_row_group_aux () : PV.impl_pred #_ #_ emp rel_row_group validate_row_group_aux =
  (rg: _)
  (vrg: _)
{
  if (impl_validate_row_group_sorted_ok () rg _) {
    unfold (rel_row_group rg vrg);
    let res = PV.impl_for_all _ _ _ (impl_validate_column_chunk ()) rg.columns _;
    fold (rel_row_group rg vrg);
    res
  } else {
    false
  }
}

fn impl_first_column_offset (_: unit) : PV.impl_f_t #_ #_ #_ first_column_offset rel_row_group
= (rg: _) (vrg: _) {
  unfold (rel_row_group rg vrg);
  let first_column = PV.impl_hd rel_column_chunk rg.columns;
  Rel.rel_option_cases rel_column_chunk first_column _;
  match first_column {
    None -> {
      Trade.elim _ _;
      fold (rel_row_group rg vrg);
      None
    }
    Some first -> {
      let gfirst = Ghost.hide (List.Tot.hd vrg.columns);
      Trade.rewrite_with_trade
        (Rel.rel_option rel_column_chunk _ _)
        (rel_column_chunk first gfirst);
      Trade.trans (rel_column_chunk first gfirst) _ _;
      unfold (rel_column_chunk first gfirst);
      Rel.rel_option_cases rel_column_meta_data first.meta_data _;
      match first.meta_data {
        norewrite
        Some cmd -> {
          Trade.rewrite_with_trade
            (Rel.rel_option rel_column_meta_data _ _)
            (rel_column_meta_data cmd (Some?.v gfirst.meta_data));
          let res = impl_offset_of_column_chunk () cmd _;
          Trade.elim (rel_column_meta_data _ _) _;
          fold (rel_column_chunk first gfirst);
          Trade.elim _ _;
          fold (rel_row_group rg vrg);
          Some res
        }
        norewrite
        None -> {
          fold (rel_column_chunk first gfirst);
          Trade.elim _ _;
          fold (rel_row_group rg vrg);
          None
        }
      }
    }
  }
}

fn impl_rg_range
  (rg: Parquet.Pulse.Toplevel.row_group)
  (vrg: Ghost.erased row_group)
  (csz: option I64.t)
requires
  rel_row_group rg vrg ** pure (option_i64_v csz == cols_size vrg.columns)
returns res: option (I64.t & I64.t)
ensures
  rel_row_group rg vrg ** pure (option_i64_v_pair res == rg_range vrg)
{
  let fco = impl_first_column_offset () rg _;
  unfold (rel_row_group rg vrg);
  Rel.rel_pure_peek rg.total_compressed_size _;
  if (Some? fco && Some? rg.total_compressed_size) {
    fold (rel_row_group rg vrg);
    Some (Some?.v fco, Some?.v rg.total_compressed_size)
  } else {
    match csz {
      None -> {
        fold (rel_row_group rg vrg);
        None
      }
      Some total_sz -> {
        let o = PV.impl_hd _ rg.columns;
        Rel.rel_option_cases rel_column_chunk o _;
        match o {
          None -> {
            Trade.elim _ _;
            fold (rel_row_group rg vrg);
            None
          }
          Some first -> {
            Trade.rewrite_with_trade
              (Rel.rel_option rel_column_chunk _ _)
              (rel_column_chunk first (List.Tot.hd vrg.columns));
            Trade.trans (rel_column_chunk _ _) _ _;
            unfold (rel_column_chunk first (List.Tot.hd vrg.columns));
            Rel.rel_option_cases rel_column_meta_data first.meta_data _;
            match first.meta_data {
              norewrite
              None -> {
                fold (rel_column_chunk first (List.Tot.hd vrg.columns));
                Trade.elim _ _;
                fold (rel_row_group rg vrg);
                None
              }
              norewrite
              Some cmd -> {
                Trade.rewrite_with_trade
                  (Rel.rel_option rel_column_meta_data _ _)
                  (rel_column_meta_data cmd (Some?.v (List.Tot.hd vrg.columns).meta_data));
                let off = impl_offset_of_column_chunk () cmd _;
                Trade.elim (rel_column_meta_data cmd (Some?.v (List.Tot.hd vrg.columns).meta_data)) _;
                fold (rel_column_chunk first (List.Tot.hd vrg.columns));
                Trade.elim _ _;
                fold (rel_row_group rg vrg);
                Some (off, total_sz)
              }
            }
          }
        }
      }
    }
  }
}

let impl_disjoint
  (rg: option (I64.t & I64.t))
  (rg1: option (I64.t & I64.t))
: Pure bool
  (requires Some? rg /\ Some? rg1)
  (ensures (fun res ->  res == disjoint (Some?.v (option_i64_v_pair rg)) (Some?.v (option_i64_v_pair rg1))))
=
  let Some (st, len) = rg in
  let Some (st1, len1) = rg1 in
  if I64.lte 0L st && I64.lte 0L len && I64.lte 0L st1 && I64.lte 0L len1
  then
    (if I64.lte st st1 then I64.gte (I64.sub st1 st) len else false) ||
    (if I64.lte st1 st then I64.gte (I64.sub st st1) len1 else false)
  else false

fn impl_rg_disjoint
  (rg: option (I64.t & I64.t))
  (n: SZ.t)
  (crg: Vec.vec (option (I64.t & I64.t)))
  (srg: Ghost.erased (Seq.seq (option (I64.t & I64.t))))
  (i: SZ.t)
requires
  Vec.pts_to crg srg ** pure (SZ.v i <= SZ.v n /\ SZ.v n == Seq.length srg)
returns res: bool
ensures
  Vec.pts_to crg srg ** pure (SZ.v i <= SZ.v n /\ SZ.v n == Seq.length srg /\
    res == (if Some? rg then List.Tot.for_all (disjoint (Some?.v (option_i64_v_pair rg))) (list_option_map option_i64_v_pair (Seq.seq_to_list (Seq.slice srg (SZ.v i) (Seq.length srg)))) else true)
  )
{
  if (None? rg) {
      true
  } else {
      let mut pj = i;
      let mut pres = true;
      Vec.pts_to_len crg;
      while (
        if (!pres) {
          SZ.lt !pj n;
        } else {
          false
        }
      ) invariant b . exists* j res . (
        Vec.pts_to crg srg **
        pts_to pj j **
        pts_to pres res **
        pure (
          SZ.v j <= SZ.v n /\
          b == (SZ.v j < SZ.v n && res) /\
          List.Tot.for_all (disjoint (Some?.v (option_i64_v_pair rg))) (list_option_map option_i64_v_pair (Seq.seq_to_list (Seq.slice srg (SZ.v i) (Seq.length srg)))) == (res && List.Tot.for_all (disjoint (Some?.v (option_i64_v_pair rg))) (list_option_map option_i64_v_pair (Seq.seq_to_list (Seq.slice srg (SZ.v j) (Seq.length srg)))))
        )
      ) {
        let j = !pj;
        Seq.cons_head_tail (Seq.slice srg (SZ.v j) (Seq.length srg));
        let rg1 = Vec.op_Array_Access crg j;
        if (None? rg1) {
            pj := (SZ.add j 1sz);
        } else {
            pres := impl_disjoint rg rg1;
            pj := (SZ.add j 1sz);
        }
      };
      !pres
  }
}

fn impl_validate_file_meta_data_aux (data_size: I64.t) : PV.impl_pred #_ #_ emp (PV.rel_vec_of_list rel_row_group) (validate_file_meta_data_aux data_size) =
  (l: _)
  (vl: _)
{
  unfold (PV.rel_vec_of_list rel_row_group l vl);
  Vec.pts_to_len l.data;
  SM.seq_list_match_length rel_row_group _ _;
  with s . assert (Vec.pts_to l.data s);
  if (0sz = l.len) {
    fold (PV.rel_vec_of_list rel_row_group l vl);
    true
  } else {
    let rg_ranges = Vec.alloc (None #(I64.t & I64.t)) l.len;
    let mut pres = true;
    let mut pi = (l.len <: SZ.t);
    let pll = GR.alloc (Ghost.reveal vl);
    let plr = GR.alloc (Nil #row_group);
    SM.seq_list_match_nil_intro Seq.empty [] rel_row_group;
    List.Tot.append_l_nil vl;
    while (
      let res = !pres;
      if (res) {
        (!pi <> 0sz)
      } else {
        false
      }
    ) invariant b . exists* res sl sr vll vlr i cl . (
      Vec.pts_to l.data s **
      GR.pts_to pll vll **
      GR.pts_to plr vlr **
      SM.seq_list_match sl vll rel_row_group **
      SM.seq_list_match sr vlr rel_row_group **
      pts_to pres res **
      pts_to pi i **
      Vec.pts_to rg_ranges cl **
      pure (
        Ghost.reveal vl == List.Tot.append vll vlr /\
        SZ.v i <= Seq.length s /\
        SZ.v i == List.Tot.length vll /\
        sl == Seq.slice s 0 (SZ.v i) /\
        Seq.equal sr (Seq.slice s (SZ.v i) (Seq.length s)) /\
        b == (res && Cons? vll) /\
        Seq.length cl == Seq.length s /\
        (res ==> (
          validate_file_meta_data_aux data_size vlr /\
          list_option_map option_i64_v_pair (Seq.seq_to_list (Seq.slice cl (SZ.v i) (Seq.length cl))) == list_option_map rg_range vlr
        )) /\
        ((~ res) ==> (~ (validate_file_meta_data_aux data_size vl)))
      )
    ) {
      with sl sr vll vlr . assert (
        GR.pts_to pll vll ** SM.seq_list_match sl vll rel_row_group **
        GR.pts_to plr vlr ** SM.seq_list_match sr vlr rel_row_group
      );
      SM.seq_list_match_length rel_row_group sl vll;
      let i' = !pi;
      let i = SZ.sub i' 1sz;
      let rg = Vec.op_Array_Access l.data i;
      Seq.lemma_split sl (SZ.v i);
      let sl1 = Ghost.hide (Seq.slice sl 0 (SZ.v i));
      let sl2 = Ghost.hide (Seq.slice sl (SZ.v i) (Seq.length sl));
      List.Tot.lemma_unsnoc_snoc vll;
      List.Tot.lemma_unsnoc_length vll;
      let vll' = Ghost.hide (fst (List.Tot.unsnoc vll));
      let vrg = Ghost.hide (snd (List.Tot.unsnoc vll));
      rewrite (SM.seq_list_match sl vll rel_row_group)
        as (SM.seq_list_match (Seq.append sl1 sl2) (List.Tot.append vll' [Ghost.reveal vrg]) rel_row_group);
      SM.seq_list_match_append_elim rel_row_group _ _ _ _;
      SM.seq_list_match_cons_elim sl2 [Ghost.reveal vrg] rel_row_group;
      SM.seq_list_match_nil_elim _ [] rel_row_group;
      with grg . assert (rel_row_group grg vrg);
      rewrite (rel_row_group grg vrg) as (rel_row_group rg vrg);
      pi := i;
      GR.op_Colon_Equals pll (Ghost.reveal vll');
      GR.op_Colon_Equals plr (Ghost.reveal vrg :: vlr);
      List.Tot.append_assoc vll' [Ghost.reveal vrg] vlr;
      validate_file_meta_data_aux_append data_size vll' (Ghost.reveal vrg :: vlr);
      unfold (rel_row_group rg vrg);
      if not (PV.impl_for_all _ _ _ (impl_column_size_nonnegative ()) rg.columns _) {
        fold (rel_row_group rg vrg);
        SM.seq_list_match_cons_intro rg (Ghost.reveal vrg) sr vlr rel_row_group;
        pres := false;
      } else {
        let mut poverflow = false;
        Rel.rel_pure_peek rg.total_compressed_size _;
        let bound = (match rg.total_compressed_size with None -> data_size | Some sz -> sz);
        if (I64.lt data_size bound) {
          fold (rel_row_group rg vrg);
          SM.seq_list_match_cons_intro rg (Ghost.reveal vrg) sr vlr rel_row_group;
          pres := false;
        } else {
          let csz = compute_cols_size poverflow rg.columns bound;
          let overflow = !poverflow;
          if (match csz with Some sz -> overflow || I64.gt sz bound | _ -> false) {
            fold (rel_row_group rg vrg);
            SM.seq_list_match_cons_intro rg (Ghost.reveal vrg) sr vlr rel_row_group;
            pres := false;
          } else {
            with cl . assert (Vec.pts_to rg_ranges cl);
            Vec.pts_to_len rg_ranges;
            fold (rel_row_group rg vrg);
            let rrg = impl_rg_range rg _ csz;
            Vec.op_Array_Assignment rg_ranges i rrg;
            with cl' . assert (Vec.pts_to rg_ranges cl');
            Vec.pts_to_len rg_ranges;
            assert (pure (validate_row_group_size data_size vrg));
            Seq.cons_head_tail (Seq.slice cl' (SZ.v i) (Seq.length cl'));
            Seq.lemma_seq_to_list_cons rrg (Seq.slice cl (SZ.v i + 1) (Seq.length cl));
            assert (pure (list_option_map option_i64_v_pair (Seq.seq_to_list (Seq.slice cl' (SZ.v i) (Seq.length cl'))) == list_option_map rg_range (Ghost.reveal vrg :: vlr)));
            SM.seq_list_match_cons_intro rg (Ghost.reveal vrg) sr vlr rel_row_group;
            pres := impl_rg_disjoint rrg l.len rg_ranges _ i';
          }
        }
      }
    };
    with sl sr vll vlr . assert (
      GR.pts_to pll vll ** SM.seq_list_match sl vll rel_row_group **
      GR.pts_to plr vlr ** SM.seq_list_match sr vlr rel_row_group
    );
    SM.seq_list_match_append_intro rel_row_group sl vll sr vlr;
    with gi . assert (pts_to pi gi);
    Seq.lemma_split s (SZ.v gi);
    rewrite (SM.seq_list_match (Seq.append sl sr) (List.Tot.append vll vlr) rel_row_group)
      as (SM.seq_list_match s vl rel_row_group);
    fold (PV.rel_vec_of_list rel_row_group l vl);
    GR.free pll;
    GR.free plr;
    Vec.free rg_ranges;
    !pres
  }
}

module U = CBOR.Spec.Util

let _ : squash (pow2 63 == 9223372036854775808) = _ by (FStar.Tactics.trefl ())

let list_for_all_validate_row_group_eq
  (footer_start64: I64.t)
  (l: list row_group)
: Lemma
  (List.Tot.for_all (validate_row_group footer_start64) l == (
    List.Tot.for_all (validate_row_group_size footer_start64) l &&
    List.Tot.for_all validate_row_group_aux l
  ))
=
  U.list_for_all_ext (validate_row_group footer_start64) (U.andp (validate_row_group_size footer_start64) validate_row_group_aux) l (fun _ -> ());
  U.list_for_all_andp (validate_row_group_size footer_start64) validate_row_group_aux l

fn impl_validate_file_meta_data (footer_start: SZ.t) : PV.impl_pred #_ #_ emp rel_file_meta_data (validate_file_meta_data (SZ.v footer_start)) =
  (md: _)
  (vmd: _)
{
  assume (pure (SZ.fits_u64));
  let footer_start_u64 = SZ.sizet_to_uint64 footer_start;
  if (SZ.uint64_to_sizet footer_start_u64 <> footer_start) {
    false
  } else if (U64.gte footer_start_u64 9223372036854775808uL) {
    false
  } else {
    let footer_start64 = FStar.Int.Cast.uint64_to_int64 footer_start_u64;
    assert (pure (I64.v footer_start64 == SZ.v footer_start));
    list_for_all_validate_row_group_eq footer_start64 vmd.row_groups;
    unfold (rel_file_meta_data md vmd);
    if (impl_validate_file_meta_data_aux footer_start64 md.row_groups _) {
      let res = PV.impl_for_all _ _ _ (impl_validate_row_group_aux ()) md.row_groups _;
      fold (rel_file_meta_data md vmd);
      res
    } else {
      fold (rel_file_meta_data md vmd);
      false
    }
  }
}

module I32 = FStar.Int32

assume val validate_page_header : validator (parser_of_tot_parser parse_page_header)

assume val read_page_header : zero_copy_parse rel_page_header (serializer_of_tot_serializer serialize_page_header)

fn impl_validate_page_data (vph: Ghost.erased page_header) (ph: _) (pm: perm) : validate_filter_test_gen_t (pts_to_serialized (serializer_of_tot_serializer serialize_page_header) ph #pm vph) #_ #_ #_ serialize_seq_all_bytes (validate_page_data vph) =
  (data: _)
  (#pm: _)
  (#vdata: _)
{
  let ph' = read_page_header ph;
  pts_to_serialized_elim_trade serialize_seq_all_bytes data;
  S.pts_to_len data;
  Trade.elim _ (pts_to_serialized serialize_seq_all_bytes data #pm vdata);
  assume (pure SZ.fits_u32);
  unfold (rel_page_header ph' vph);
  Rel.rel_pure_peek ph'.compressed_page_size _;
  fold (rel_page_header ph' vph);
  Trade.elim _ _;
  if (I32.lt ph'.compressed_page_size 0l) {
    false
  } else {
    (SZ.uint32_to_sizet (FStar.Int.Cast.int32_to_uint32 ph'.compressed_page_size) = S.len data)
  }
}

let validate_page : validator (parser_of_tot_parser tot_parse_page) =
  validate_ext #_ #_ #parse_page
    (validate_dtuple2_gen
      validate_page_header
      serialize_page_header
      (fun vph ph pm ->
        validate_filter_gen'
          (validator_gen_of_validator _ (validate_seq_all_bytes ()))
          serialize_seq_all_bytes
          (validate_page_data vph)
          (impl_validate_page_data vph ph pm)
      )
    )
    _

let validate_jump_page (offset_sz: SZ.t) (size_sz: SZ.t) (pm: perm) (data: S.slice byte) (vdata: Ghost.erased bytes) (pl: Parquet.Pulse.Toplevel.page_location) (vpl: Ghost.erased page_location)
=
  validate_jump_with_offset_and_size_then_parse 
  emp
  // (pts_to_bytes pm data vdata ** rel_page_location pl vpl)
  offset_sz size_sz validate_page

fn impl_validate_page_location_all (pm: perm) : PV.impl_pred2 #_ #_ #_ #_ emp (pts_to_bytes pm) rel_page_location validate_page_location_all
=
  (data: _)
  (vdata: _)
  (pl: _)
  (vpl: _)
{
  unfold rel_page_location pl vpl;
  Rel.rel_pure_peek pl _;
  assume (pure (SZ.fits_u64));
  assume (pure (SZ.fits_u32));
  let offset_sz = SZ.uint64_to_sizet (FStar.Int.Cast.int64_to_uint64 pl.offset);
  let length_sz = SZ.uint32_to_sizet (FStar.Int.Cast.int32_to_uint32 pl.compressed_page_size);
  let res = 
  (
    (I64.gte pl.offset 0L) &&
    (I32.gte pl.compressed_page_size 0l) &&
    (validate_jump_page offset_sz length_sz pm data vdata pl vpl data vdata)
    // validate_jump_with_offset_and_size_then_parse 
    //   emp offset_sz length_sz validate_page data vdata
  );
  fold rel_page_location pl vpl;
  res
}

fn impl_validate_offset_index_all_aux (pm: perm) : PV.impl_pred2 #_ #_ #_ #_ emp (pts_to_bytes pm) rel_offset_index validate_offset_index_all_aux
= 
  (data: _)
  (vdata: _)
  (oi: _)
  (voi: _)
{
  unfold rel_offset_index oi voi;
  let res = PV.impl_for_all _ _ _ (impl_validate_page_location_all pm data vdata) oi.page_locations voi.page_locations;
  fold rel_offset_index oi voi;
  res
}

fn impl_validate_offset_index_first_loc () : PV.impl_pred2 #_ #_ #_ #_ emp rel_column_chunk rel_offset_index validate_offset_index_first_loc
=
  (cc: _)
  (vcc: _)
  (oi: _)
  (voi: _)
{
  unfold (rel_offset_index oi voi);
  let first_loc = PV.impl_hd _ oi.page_locations;
  Rel.rel_option_cases rel_page_location _ _;
  match first_loc {
    norewrite
    None -> {
      Trade.elim _ _;
      fold (rel_offset_index oi voi);
      true
    }
    norewrite
    Some loc -> {
      Trade.rewrite_with_trade
        (Rel.rel_option rel_page_location _ _)
        (rel_page_location loc (List.Tot.hd voi.page_locations));
      Trade.trans (rel_page_location loc (List.Tot.hd voi.page_locations)) _ _;
      unfold (rel_page_location loc (List.Tot.hd voi.page_locations));
      Rel.rel_pure_peek loc _;
      fold (rel_page_location loc (List.Tot.hd voi.page_locations));
      Trade.elim _ _;
      fold (rel_offset_index oi voi);
      unfold (rel_column_chunk cc vcc);
      Rel.rel_option_cases rel_column_meta_data _ _;
      match cc.meta_data {
        norewrite
        None -> {
          fold (rel_column_chunk cc vcc);
          true
        }
        norewrite
        Some cmd -> {
          Trade.rewrite_with_trade
            (Rel.rel_option rel_column_meta_data _ _)
            (rel_column_meta_data cmd (Some?.v vcc.meta_data));
          let off = impl_offset_of_column_chunk () cmd _;
          Trade.elim _ _;
          fold (rel_column_chunk cc vcc);
          (loc.offset = off)
        }
      }
    }
  }
}

fn page_location_access_offset (): PV.impl_f_t #_ #_ #_ (fun (pl: page_location) -> pl.offset) rel_page_location
= (pl: _) (vpl: _)
{
  unfold (rel_page_location pl vpl);
  Rel.rel_pure_peek _ _;
  fold (rel_page_location pl vpl);
  pl.offset
}

noextract [@@noextract_to "krml"]
let list_mem_option_map (#t: Type0) (#t' : eqtype) (f: t -> t') (x: option t') (l: list t) : Tot bool =
  match x with
  | None -> true
  | Some x' -> List.Tot.mem x' (List.Tot.map f l)

fn option_offset_in_page_locations (o: option I64.t) : PV.impl_pred #_ #_ emp (rel_vec_of_list rel_page_location) (list_mem_option_map (fun pl -> pl.offset) o)
= (pl: _)
  (vpl: _)
{
  match o {
    None -> {
      true
    }
    Some off -> {
      PV.impl_mem_map _ (fun pl -> pl.offset) (page_location_access_offset ()) off pl _ // FIXME: Pulse cannot infer lambdas
    }
  }
}

fn impl_validate_offset_index_cc_page_offsets () : PV.impl_pred2 #_ #_ #_ #_ emp rel_column_chunk rel_offset_index validate_offset_index_cc_page_offsets
=
  (cc: _)
  (vcc: _)
  (oi: _)
  (voi: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  match cc.meta_data {
    norewrite
    None -> {
      fold (rel_column_chunk cc vcc);
      true
    }
    norewrite
    Some cmd -> {
      Trade.rewrite_with_trade
        (Rel.rel_option rel_column_meta_data _ _)
        (rel_column_meta_data cmd (Some?.v vcc.meta_data));
      unfold (rel_column_meta_data cmd (Some?.v vcc.meta_data));
      Rel.rel_pure_peek cmd.dictionary_page_offset _;
      Rel.rel_pure_peek cmd.index_page_offset _;
      Rel.rel_pure_peek cmd.data_page_offset _;
      fold (rel_column_meta_data cmd (Some?.v vcc.meta_data));
      Trade.elim _ _;
      fold (rel_column_chunk cc vcc);
      unfold (rel_offset_index oi voi);
      let res = (
        option_offset_in_page_locations cmd.dictionary_page_offset oi.page_locations _ &&
        option_offset_in_page_locations cmd.index_page_offset oi.page_locations _ &&
        PV.impl_mem_map _ (fun pl -> pl.offset) (page_location_access_offset ()) cmd.data_page_offset oi.page_locations _
      );
      fold (rel_offset_index oi voi);
      res
    }
  }
}

let rec list_fold_validate_offset_index_col_size_add_nonnegative
  (acc: int)
  (l: list page_location)
: Lemma
  (ensures acc >= 0 ==> List.Tot.fold_left validate_offset_index_col_size_add acc l >= acc)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    list_fold_validate_offset_index_col_size_add_nonnegative (validate_offset_index_col_size_add acc a) q

fn impl_validate_offset_index_col_size () : PV.impl_pred2 #_ #_ #_ #_ emp rel_column_chunk rel_offset_index validate_offset_index_col_size
=
  (cc: _)
  (vcc: _)
  (oi: _)
  (voi: _)
{
  unfold (rel_column_chunk cc vcc);
  Rel.rel_option_cases rel_column_meta_data _ _;
  match cc.meta_data {
    norewrite
    None -> {
      fold (rel_column_chunk cc vcc);
      true
    }
    norewrite
    Some md -> {
      Trade.rewrite_with_trade
        (Rel.rel_option rel_column_meta_data _ _)
        (rel_column_meta_data md (Some?.v vcc.meta_data));
      unfold (rel_column_meta_data md (Some?.v vcc.meta_data));
      Rel.rel_pure_peek md.total_compressed_size _;
      fold (rel_column_meta_data md (Some?.v vcc.meta_data));
      Trade.elim _ _;
      fold (rel_column_chunk cc vcc);
      unfold (rel_offset_index oi voi);
      let mut pres = (I64.lte 0L md.total_compressed_size);
      let mut paccu = 0L;
      let mut pi = 0sz;
      unfold (PV.rel_vec_of_list rel_page_location oi.page_locations voi.page_locations);
      Vec.pts_to_len oi.page_locations.data;
      SM.seq_list_match_length rel_page_location _ _;
      with s . assert (Vec.pts_to oi.page_locations.data s ** SM.seq_list_match s voi.page_locations rel_page_location);
      Trade.refl (SM.seq_list_match s voi.page_locations rel_page_location);
      list_fold_validate_offset_index_col_size_add_nonnegative 0 voi.page_locations;
      while (
        SM.seq_list_match_length rel_page_location _ _;
        (!pres && SZ.lt !pi oi.page_locations.len)
      ) invariant b . exists* res accu i sr vlr . (
        Vec.pts_to oi.page_locations.data s **
        pts_to pres res **
        pts_to paccu accu **
        pts_to pi i **
        SM.seq_list_match sr vlr rel_page_location **
        Trade.trade
          (SM.seq_list_match sr vlr rel_page_location)
          (SM.seq_list_match s voi.page_locations rel_page_location) **
        pure (
          0 <= I64.v accu /\
          (let goal = List.Tot.fold_left validate_offset_index_col_size_add 0 voi.page_locations in if res then I64.v accu <= I64.v md.total_compressed_size /\ goal == List.Tot.fold_left validate_offset_index_col_size_add (I64.v accu) vlr else goal <> I64.v md.total_compressed_size) /\
          SZ.v i <= Seq.length s /\
          sr == Seq.slice s (SZ.v i) (Seq.length s) /\
          b == (res && (Cons? vlr))
        )
      ) {
        with sr vlr . assert (SM.seq_list_match sr vlr rel_page_location);
        SM.seq_list_match_length rel_page_location _ _;
        SM.seq_list_match_cons_elim_trade sr vlr rel_page_location;
        Trade.trans _ (SM.seq_list_match sr vlr rel_page_location) _;
        with gpl vpl . assert (rel_page_location gpl vpl);
        let i = !pi;
        let pl = Vec.op_Array_Access oi.page_locations.data i;
        rewrite each gpl as pl;
        unfold (rel_page_location pl vpl);
        Rel.rel_pure_peek pl _;
        fold (rel_page_location pl vpl);
        Trade.elim_hyp_l _ _ _;
        pi := SZ.add i 1sz;
        if (I32.lte 0l pl.compressed_page_size) {
          let accu = !paccu;
          list_fold_validate_offset_index_col_size_add_nonnegative (I64.v accu + I32.v pl.compressed_page_size) (List.Tot.tl vlr);
          let psz = FStar.Int.Cast.int32_to_int64 pl.compressed_page_size;
          if (I64.lt (I64.sub md.total_compressed_size accu) psz) {
            pres := false
          } else {
            paccu := I64.add accu psz
          }
        }
      };
      Trade.elim _ _;
      fold (PV.rel_vec_of_list rel_page_location oi.page_locations voi.page_locations);
      fold (rel_offset_index oi voi);
      (!pres && (!paccu = md.total_compressed_size))
    }
  }
}

fn impl_page_location_offset () : impl_fst_f #_ #_ page_location_offset_and_size rel_page_location
= (pl: _) (vpl: _) {
  unfold (rel_page_location pl vpl);
  Rel.rel_pure_peek _ _;
  fold (rel_page_location pl vpl);
  pl.offset
}

fn impl_page_location_size () : impl_snd_f #_ #_ page_location_offset_and_size rel_page_location
= (pl: _) (vpl: _) {
  unfold (rel_page_location pl vpl);
  Rel.rel_pure_peek _ _;
  fold (rel_page_location pl vpl);
  FStar.Int.Cast.int32_to_int64 pl.compressed_page_size
}

fn impl_validate_offset_index () : PV.impl_pred2 #_ #_ #_ #_ emp rel_column_chunk rel_offset_index validate_offset_index
=
  (cc: _)
  (vcc: _)
  (oi: _)
  (voi: _)
{
  if impl_validate_offset_index_first_loc () cc _ oi _ {
    if impl_validate_offset_index_cc_page_offsets () cc _ oi _ {
      if impl_validate_offset_index_col_size () cc _ oi _ {
        unfold (rel_offset_index oi voi);
        let res = impl_offsets_and_sizes_are_contiguous
          page_location_offset_and_size
          rel_page_location
          (impl_page_location_offset ())
          (impl_page_location_size ())
          oi.page_locations;
        fold (rel_offset_index oi voi);
        assert (pure (res == page_offsets_are_contiguous voi.page_locations));
        res
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
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
  ( impl_validate_offset_index () cc vcc oi voi &&
  impl_validate_offset_index_all_aux pm data vdata oi voi );
}

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
