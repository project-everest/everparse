module EverParse3d.InputStream.Base
open Pulse.Lib.Pervasives

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LP = LowParse.Spec.Base
module LPL = LowParse.PulseParse.Base

noextract
inline_for_extraction
class input_stream_inst (t: Type) : Type = {
  
  pts_to: t -> Seq.seq U8.t -> slprop;

  has:
    (x: t) ->
    (n: SZ.t) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      pts_to x v
    ))
    (ensures (fun res ->
      pts_to x v **
      pure (res == true <==> SZ.v n <= Seq.length v)
    ));
  
  read:
    (t': Type0) ->
    (k: LP.parser_kind) ->
    (p: LP.parser k t') ->
    (r: LPL.leaf_reader p) ->
    (x: t) ->
    (n: SZ.t) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt t'
    (requires (
      pts_to x v ** pure (
      k.LP.parser_kind_subkind == Some LP.ParserStrong /\
      k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
      k.LP.parser_kind_low == SZ.v n /\
      Some? (LP.parse p v)
    )))
    (ensures (fun dst' -> exists* v' .
      pts_to x v' ** pure (
      Seq.length v >= SZ.v n /\
      LP.parse p (Seq.slice v 0 (SZ.v n)) == Some (dst', SZ.v n) /\
      LP.parse p v == Some (dst', SZ.v n) /\
      Seq.equal v' (Seq.slice v (SZ.v n) (Seq.length v))
    )));

  skip:
    (x: t) ->
    (n: SZ.t) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt unit
    (requires (
      pts_to x v ** pure (
      Seq.length v >= SZ.v n
    )))
    (ensures (fun _ -> exists* v' .
      pts_to x v' ** pure (
      Seq.length v >= SZ.v n /\
      v' `Seq.equal` Seq.slice v (SZ.v n) (Seq.length v)
    )));
  
  empty:
    (x: t) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt SZ.t
    (requires (
      pts_to x v
    ))
    (ensures (fun res ->
      pts_to x Seq.empty ** pure (
      SZ.v res == Seq.length v
    )));

  is_prefix_of:
    (x: t) ->
    (y: t) ->
    (suffix: Seq.seq U8.t) ->
    Tot slprop;

  truncate:
    (x: t) ->
    (n: SZ.t) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt t
    (requires (
      pts_to x v ** pure (
      SZ.v n <= Seq.length v
    )))
    (ensures (fun res -> exists* v1 v2 .
      pts_to res v1 **
      is_prefix_of res x v2 **
      pure (
      	SZ.v n <= Seq.length v /\
        Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
	Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
	Ghost.reveal v == Seq.append v1 v2
    )));

  untruncate:
    (x: t) ->
    (y: t) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    (suffix: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
    (requires (
       pts_to x v **
       is_prefix_of x y suffix
    ))
    (ensures (fun _ ->
       pts_to y (Seq.append v suffix)
    ));
}
