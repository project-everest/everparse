module LargeExtern
friend EverParse3d.Prelude
friend EverParse3d.Actions.Base
open Pulse.Lib.Pervasives
open EverParse3d.State
#lang-pulse

module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.LowstarExtern
module I = EverParse3d.InputStream.Base
module AD = EverParse3d.Lowstar.ExternAdapter
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module FL = LowParse.Spec.FLData
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module EC = EverParse3d.ErrorCode

noextract let count = 4294967304
noextract let kind : P.parser_kind true P.WeakKindStrongPrefix =
  FL.parse_fldata_kind count P.kind_all_bytes
noextract let parser : P.parser kind P.all_bytes =
  FL.parse_fldata P.parse_all_bytes count

let parser_result (s: Seq.seq U8.t) : Lemma
  ((Some? (LP.parse parser s) <==> count <= Seq.length s) /\
   (Some? (LP.parse parser s) ==> snd (Some?.v (LP.parse parser s)) == count))
  = ()

// O(1) scan: only ghost sequences describe the input; no bytes are allocated.
inline_for_extraction noextract
fn scan_worker (extra: B.extra_t)
  : A.validate_with_action_no_read #B.base_t #B.len_t #B.pos_t
      #B.input_stream_extern parser state_dict_empty false false
  = (ctxt: _) (handler: _) (base: _) (len: _) (cursor: _)
    (lookahead: _) (state: _) (contents: _) (remaining: _) (old: _)
{
  rewrite (I.pts_to #_ #_ #_ #B.pts_to_inst base len cursor contents remaining)
    as (B.stream_pts_to base len cursor contents remaining);
  unfold (B.stream_pts_to base len cursor contents remaining);
  with current. _;
  unfold (B.public_pts_to base current contents remaining);
  assert (pure (Seq.length remaining < 1152921504606846976));
  fold (B.public_pts_to base current contents remaining);
  fold (B.stream_pts_to base len cursor contents remaining);
  let off = !lookahead;
  let high = U64.add off 4294967296UL;
  parser_result (Seq.slice remaining (U64.v old) (Seq.length remaining));
  let prefix = B.stream_has_u64 #extra base len cursor high contents remaining;
  if prefix {
    let enough = B.stream_has_at #extra base len cursor high 8sz contents remaining;
    if enough {
      assert (pure (U64.fits (U64.v high + 8)));
      let next = B.scan_add high 8sz;
      lookahead := next;
      assert (pure (U64.v next == U64.v old + count));
      assert (pure (count <= Seq.length (Seq.slice remaining (U64.v old) (Seq.length remaining))));
      parser_result (Seq.slice remaining (U64.v old) (Seq.length remaining));
      assert (pure (Some? (LP.parse parser (Seq.slice remaining (U64.v old) (Seq.length remaining)))));
      rewrite (B.stream_pts_to base len cursor contents remaining)
        as (I.pts_to #_ #_ #_ #B.pts_to_inst base len cursor contents remaining);
      EC.validator_success
    } else {
      lookahead := 18446744073709551615UL;
      rewrite (B.stream_pts_to base len cursor contents remaining)
        as (I.pts_to #_ #_ #_ #B.pts_to_inst base len cursor contents remaining);
      EC.validator_error_not_enough_data
    }
  } else {
    lookahead := 18446744073709551615UL;
    rewrite (B.stream_pts_to base len cursor contents remaining)
      as (I.pts_to #_ #_ #_ #B.pts_to_inst base len cursor contents remaining);
    EC.validator_error_not_enough_data
  }
}

let no_read (extra: B.extra_t) =
  AD.adapt_no_read #_ #_ #_ #_ #parser #state_dict_empty #false #false
    (scan_worker extra)

let skip (extra: B.extra_t) =
  AD.adapt_read #_ #_ #_ #_ #parser #state_dict_empty #false #false
    (A.validate_drop #B.base_t #B.len_t #B.pos_t #B.input_stream_extern #extra
      (scan_worker extra))

let drain (extra: B.extra_t) =
  AD.adapt_read #_ #_ #_ #_ #P.parse_all_bytes #state_dict_empty #false #false
    (A.validate_all_bytes #B.base_t #B.len_t #B.pos_t #B.input_stream_extern #extra)
