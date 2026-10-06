module EverParse3d.Lowstar.ExternAdapter
friend EverParse3d.Kinds
friend EverParse3d.Prelude
friend EverParse3d.Actions.Base
friend EverParse3d.Lowstar.ExternAdapter.Spec
open Pulse.Lib.Pervasives
open EverParse3d.State
#lang-pulse

module A = EverParse3d.Actions.Base
module B = EverParse3d.InputStream.LowstarExtern
module I = EverParse3d.InputStream.Base
module P = EverParse3d.Prelude
module LP = LowParse.Spec.Base
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module E = EverParse3d.Lowstar.ErrorCode
module EC = EverParse3d.ErrorCode

inline_for_extraction noextract
let no_read_position (status: U8.t) (start offset: U64.t)
  : Pure U64.t
    (requires (status == EC.validator_success ==>
      U64.fits (U64.v start + U64.v offset)))
    (ensures fun position ->
      (status == EC.validator_success ==>
        U64.v position == U64.v start + U64.v offset) /\
      (status <> EC.validator_success ==> position == start))
  = if status = EC.validator_success then U64.add start offset else start

inline_for_extraction noextract
fn adapt_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk)
  (#[@@@erasable] t: Type)
  (#[@@@erasable] p: P.parser #nz #wk k t)
  (#[@@@erasable] d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_extern p d has_action use_error_handler)
  : validator p d has_action true use_error_handler
  = (ctxt: _) (handler: _) (input: _) (start: _)
    (extra: _) (contents: _) (remaining: _)
{
  // Save public facts before packaging them inside the worker predicate.
  unfold (B.public_pts_to input start contents remaining);
  fold (B.public_pts_to input start contents remaining);
  let mut cursor = start;
  fold (B.stream_pts_to input () cursor contents remaining);
  rewrite (B.stream_pts_to input () cursor contents remaining)
    as (I.pts_to #_ #_ #_ #B.pts_to_inst input () cursor contents remaining);
  let status = worker ctxt handler input () cursor extra contents remaining;
  with rest. assert (I.pts_to #_ #_ #_ #B.pts_to_inst input () cursor contents rest);
  rewrite (I.pts_to #_ #_ #_ #B.pts_to_inst input () cursor contents rest)
    as (B.stream_pts_to input () cursor contents rest);
  unfold (B.stream_pts_to input () cursor contents rest);
  with current. _;
  unfold (B.public_pts_to input current contents rest);
  let position = !cursor;
  LP.parser_kind_prop_equiv k p;
  EverParse3d.Lowstar.ExternAdapter.Spec.parse_eq p remaining;
  let result = E.pack status position;
  assert (pure (result_prop p has_action true start remaining position rest result));
  fold (B.public_pts_to input current contents rest);
  result
}

inline_for_extraction noextract
fn adapt_no_read
  (#nz: bool) (#wk: _) (#k: P.parser_kind nz wk)
  (#[@@@erasable] t: Type)
  (#[@@@erasable] p: P.parser #nz #wk k t)
  (#[@@@erasable] d: state_dict)
  (#has_action #use_error_handler: bool)
  (worker: A.validate_with_action_no_read #B.base_t #B.len_t #B.pos_t
    #B.input_stream_extern p d has_action use_error_handler)
  : validator p d has_action false use_error_handler
  = (ctxt: _) (handler: _) (input: _) (start: _)
    (extra: _) (contents: _) (remaining: _)
{
  unfold (B.public_pts_to input start contents remaining);
  fold (B.public_pts_to input start contents remaining);
  let mut cursor = start;
  let mut lookahead = 0UL;
  fold (B.stream_pts_to input () cursor contents remaining);
  rewrite (B.stream_pts_to input () cursor contents remaining)
    as (I.pts_to #_ #_ #_ #B.pts_to_inst input () cursor contents remaining);
  let status = worker ctxt handler input () cursor lookahead extra
    contents remaining (Ghost.hide 0UL);
  let offset = !lookahead;
  Seq.lemma_eq_elim (Seq.slice remaining 0 (Seq.length remaining)) remaining;
  LP.parser_kind_prop_equiv k p;
  EverParse3d.Lowstar.ExternAdapter.Spec.parse_eq p remaining;
  EverParse3d.Lowstar.ExternAdapter.Spec.parse_bounds p remaining;
  rewrite (I.pts_to #_ #_ #_ #B.pts_to_inst input () cursor contents remaining)
    as (B.stream_pts_to input () cursor contents remaining);
  unfold (B.stream_pts_to input () cursor contents remaining);
  with current. _;
  unfold (B.public_pts_to input current contents remaining);
  assert (pure (status == EC.validator_success ==>
    U64.v offset <= Seq.length remaining));
  assert (pure (U64.v start + Seq.length remaining == Seq.length contents));
  assert (pure (Seq.length contents < E.position_limit));
  assert (pure (status == EC.validator_success ==>
    U64.fits (U64.v start + U64.v offset)));
  // Failure deliberately ignores an unconstrained speculative offset.
  let position = no_read_position status start offset;
  let result = E.pack status position;
  assert (pure (result_prop p has_action false start remaining current remaining result));
  fold (B.public_pts_to input current contents remaining);
  result
}
