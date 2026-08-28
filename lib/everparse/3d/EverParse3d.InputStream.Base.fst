module EverParse3d.InputStream.Base
open Pulse.Lib.Pervasives

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LP = LowParse.Spec.Base
module API = LowParse.Pulse.ArrayPtr.Int

let seq_is_suffix_of (#t: Type) (small large: Seq.seq t) : Tot prop =
    Seq.length small <= Seq.length large /\
    Seq.slice large (Seq.length large - Seq.length small) (Seq.length large) `Seq.equal` small

noextract
inline_for_extraction
class input_stream_pts_to (base_t: Type0) (len_t: Type0) (pos_t: Type0) : Type = {

  pts_to: base_t -> len_t -> pos_t -> Seq.seq U8.t -> Seq.seq U8.t -> slprop;

  is_prefix_of:
    (base_x: base_t) ->
    (len_x: len_t) ->
    (pos_x: pos_t) ->
    (base_y: base_t) ->
    (len_y: len_t) ->
    (pos_y: pos_t) ->
    (contents: Seq.seq U8.t) ->
    (suffix: Seq.seq U8.t) ->
    Tot slprop;
}

noextract
inline_for_extraction
class input_stream_inst (base_t: Type0) (len_t: Type0) (pos_t: Type0) : Type = {

  [@@@FStar.Tactics.Typeclasses.no_method]
  pts_to_inst: input_stream_pts_to base_t len_t pos_t;

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
  
  (* [has_at base len pos off n] tests whether [n] bytes are available
     starting [off] bytes after the current position, without consuming
     anything. This is what the "no read" (non-consuming) validators need,
     since they track their position in a separate [SZ.t] reference. *)
  has_at:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (off: SZ.t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      pts_to base len pos contents v ** pure (
      SZ.v off <= Seq.length v
    )))
    (ensures (fun res ->
      pts_to base len pos contents v ** pure (
      (res == true <==> SZ.v off + SZ.v n <= Seq.length v) /\
      (res == true ==> SZ.fits (SZ.v off + SZ.v n))
    )));

  read:
    (t': Type0) ->
    (k: LP.parser_kind) ->
    (p: LP.parser k t') ->
    (r: API.leaf_reader p) ->
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

  (* [truncate] conceptually returns a whole (base, len, pos) triple, but
     returning one would extract to a C struct that KaRaMeL monomorphizes into
     whichever *generated* module happens to use it first, and then has to
     share through an `internal/` header. Instead each instance names the one
     component it actually modifies -- [trunc_t] -- and recovers the other two
     from the original stream through the projections below. Buffer sets
     [trunc_t = len_t] (it re-bases nothing and only shortens the length),
     extern sets [trunc_t = base_t] (its length and position are [unit]), so in
     both backends [truncate] extracts to a scalar-returning function and no
     struct is ever built. *)
  [@@@FStar.Tactics.Typeclasses.no_method]
  trunc_t: Type0;

  trunc_base: (base: base_t) -> (len: len_t) -> (pos: pos_t) -> (tr: trunc_t) -> Tot base_t;

  trunc_len: (base: base_t) -> (len: len_t) -> (pos: pos_t) -> (tr: trunc_t) -> Tot len_t;

  trunc_pos: (base: base_t) -> (len: len_t) -> (pos: pos_t) -> (tr: trunc_t) -> Tot pos_t;

  truncate:
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt trunc_t
    (requires (
      pts_to base len pos contents v ** pure (
      SZ.v n <= Seq.length v
    )))
    (ensures (fun res -> exists* contents' v1 v2 .
      pts_to (trunc_base base len pos res) (trunc_len base len pos res) (trunc_pos base len pos res) contents' v1 **
      is_prefix_of (trunc_base base len pos res) (trunc_len base len pos res) (trunc_pos base len pos res) base len pos contents v2 **
      pure (
      	SZ.v n <= Seq.length v /\
        Seq.equal v1 (Seq.slice v 0 (SZ.v n)) /\
	Seq.equal v2 (Seq.slice v (SZ.v n) (Seq.length v)) /\
	Seq.length v <= Seq.length contents /\
	Seq.equal contents' (Seq.append (Seq.slice contents 0 (Seq.length contents - Seq.length v)) v1) /\
	Ghost.reveal v == Seq.append v1 v2
    )));

  untruncate:
    (base_x: base_t) ->
    (len_x: len_t) ->
    (pos_x: pos_t) ->
    (base_y: base_t) ->
    (len_y: len_t) ->
    (pos_y: pos_t) ->
    (contents: Seq.seq U8.t) ->
    (v: Seq.seq U8.t) ->
    (contents0: Seq.seq U8.t) ->
    (suffix: Seq.seq U8.t) ->
    stt_ghost unit emp_inames
    (requires (
       pts_to base_x len_x pos_x contents v **
       is_prefix_of base_x len_x pos_x base_y len_y pos_y contents0 suffix **
       pure (contents0 == Seq.append contents suffix)
    ))
    (ensures (fun _ ->
       pts_to base_y len_y pos_y contents0 (Seq.append v suffix)
    ));
}

noextract
inline_for_extraction
instance input_stream_pts_to_of_inst
  (#base_t: Type0) (#len_t: Type0) (#pos_t: Type0)
  {| inst: input_stream_inst base_t len_t pos_t |}
: Tot (input_stream_pts_to base_t len_t pos_t)
= inst.pts_to_inst
