module EverParse3d.InputStream.Base
open Pulse.Lib.Pervasives

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LP = LowParse.Spec.Base
module LPL = LowParse.PulseParse.Base

let seq_is_suffix_of (#t: Type) (small large: Seq.seq t) : Tot prop =
    Seq.length small <= Seq.length large /\
    Seq.slice large (Seq.length large - Seq.length small) (Seq.length large) `Seq.equal` small

noextract
inline_for_extraction
class input_stream_inst (base_t: Type0) (len_t: Type0) (pos_t: Type0) : Type = {
  
  pts_to: base_t -> len_t -> pos_t -> Seq.seq U8.t -> Seq.seq U8.t -> slprop;

  pts_to_is_suffix_of:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (contents: Seq.seq U8.t) ->
    (v: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
      (pts_to base len pos contents v)
      (fun _ -> pts_to base len pos contents v ** pure (v `seq_is_suffix_of` contents));

  get_position:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      pts_to base len pos contents v
    ))
    (ensures fun res ->
      pts_to base len pos contents v **
      pure (
        SZ.v res + Seq.length v == Seq.length contents
      )
    );

  has:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      pts_to base len pos contents v
    ))
    (ensures (fun res ->
      pts_to base len pos contents v **
      pure (res == true <==> SZ.v n <= Seq.length v)
    ));
  
  read:
    (t': Type0) ->
    (k: LP.parser_kind) ->
    (p: LP.parser k t') ->
    (r: LPL.leaf_reader p) ->
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt t'
    (requires (
      pts_to base len pos contents v ** pure (
      k.LP.parser_kind_subkind == Some LP.ParserStrong /\
      k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
      k.LP.parser_kind_low == SZ.v n /\
      Some? (LP.parse p v)
    )))
    (ensures (fun dst' -> exists* v' .
      pts_to base len pos contents v' ** pure (
      Seq.length v >= SZ.v n /\
      LP.parse p (Seq.slice v 0 (SZ.v n)) == Some (dst', SZ.v n) /\
      LP.parse p v == Some (dst', SZ.v n) /\
      Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
    )));

  skip:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
    (requires (
      pts_to base len pos contents v ** pure (
      Seq.length v >= SZ.v n
    )))
    (ensures (fun _ -> exists* v' .
      pts_to base len pos contents v' ** pure (
      Seq.length v >= SZ.v n /\
      v' `Seq.equal` Seq.slice v (SZ.v n) (Seq.length v)
    )));
  
  empty:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      pts_to base len pos contents v
    ))
    (ensures (fun res ->
      pts_to base len pos contents Seq.empty ** pure (
      SZ.v res == Seq.length v
    )));
}
