module EverParse3d.InputStream.Base
open Pulse.Lib.Pervasives

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module LP = LowParse.Spec.Base
module API = LowParse.Pulse.ArrayPtr.Int
module Util = EverParse3d.Util
module AppCtxt = EverParse3d.AppCtxt
module PR = Pulse.Lib.Reference

(* Backed by the generated wrapper's
   `sizeof(size_t) <= sizeof(uint64_t)` static assertion. *)
assume val sizet_to_uint64_exact (x: SZ.t)
  : Lemma (ensures U64.v (SZ.sizet_to_uint64 x) == SZ.v x)

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

(* The type of the error-handler callback.

   This lives here, rather than in EverParse3d.Actions.Common where it used to,
   because [input_stream_inst] below must mention it, and Actions.Common
   depends on this module.

   NOTE: this arrow must have exactly as many binders as the C function-pointer
   type it extracts to. Ghost binders would be extracted by F* as extra [unit]
   parameters of the type abbreviation, whereas Pulse drops them at application
   sites and KaRaMeL drops them when emitting C; the resulting arity mismatch
   makes KaRaMeL's Low* checker reject every generated validator as soon as the
   abbreviation is preserved with -no-inline-type-abbrev (which is what gives
   it the name EVERPARSE_ERROR_HANDLER). Hence the error handler is given
   permission on the application context only: callers keep (and frame) their
   permission on the input stream across the call.
*)
let error_handler_arrow
  (base_t: Type0) (len_t: Type0) (pos_t: Type0)
=
    typename:string ->
    fieldname:string ->
    error_reason:string ->
    error_code:U8.t ->
    ctxt: AppCtxt.app_ctxt ->
    sl_base: base_t ->
    sl_len: len_t ->
    sl_pos: pos_t ->
    (* The offset at which the failing field *started*, sampled before the
       field's validator ran. This is what doc/3d-lang.rst calls
       `StartPosition`, and it is what the Low* backend reports; it is
       measured the same way as the [start_pos] of an [action], i.e. relative
       to the origin of the current validation.

       It has to be passed separately rather than recovered from [sl_pos]:
       [sl_pos] is the live position (a reference, on the buffer backend) and
       has already moved past the bytes the field consumed by the time the
       handler runs, and on the extern backend [pos_t] is the truncation
       origin rather than a position at all.

       It is a [U64.t] rather than a [SZ.t] to match the Low* error handler
       and `EVERPARSE_ERROR_FRAME.start_pos`, and because the no-read wrapper
       has to add the current stream position to the relative offset that the
       non-consuming validators keep in their [pos] reference. [SZ.add] needs
       `fits` of that sum, and none is available there: [get_position] fits by
       construction, but the remaining-length summand carries no such
       evidence.

       Making [validate_with_action_no_read]'s [pos] absolute would remove the
       addition, but it does not remove the obligation -- it moves it onto the
       client. The relative [pos] advances by [SZ.add p0 sz], whose `fits` is
       handed to it by [has_at] below (`res == true ==> SZ.fits (SZ.v off +
       SZ.v n)`); an absolute [pos] would need `fits` of the *absolute* sum,
       i.e. a strengthened [has_at] postcondition, which is one more unchecked
       proof obligation on hand-written C. *)
    start_pos:U64.t ->
    stt unit
      (requires exists* v_ctxt . PR.pts_to ctxt v_ctxt)
      (ensures fun _ -> exists* v_ctxt' . PR.pts_to ctxt v_ctxt')

noextract
inline_for_extraction
class input_stream_inst (base_t: Type0) (len_t: Type0) (pos_t: Type0) : Type = {

  [@@@FStar.Tactics.Typeclasses.no_method]
  pts_to_inst: input_stream_pts_to base_t len_t pos_t;

  (* The error-handler callback type, carried as a member rather than named
     directly as [error_handler_arrow base_t len_t pos_t].

     KaRaMeL has no parameterized typedefs: it inlines such an abbreviation at
     every use site, so a generated validator's prototype would spell the whole
     function-pointer type out instead of naming EVERPARSE_ERROR_HANDLER, as the
     Low* backend does. Carrying the type as a member lets each backend supply
     its own 0-ary alias -- which KaRaMeL can preserve, and the `EverParse`
     bundle can rename -- while [error_handler_arrow_of_t] keeps it
     interchangeable with the arrow type for the few places that call a handler.
     See EverParse3d.Actions.ErrorHandler.Buffer. *)
  [@@@FStar.Tactics.Typeclasses.no_method]
  error_handler_t: Type0;

  (* The way back to the arrow type, for the few places that actually call a
     handler. This is the identity, but it must be a member rather than a
     coercion derived from [error_handler_t == error_handler_arrow ...]: F*
     elaborates such a coercion to [FStar.Pervasives.coerce_eq], which is
     `irreducible` and therefore survives extraction as a real (monomorphized)
     C function. Each backend discharges this with `fun h -> h`, which needs no
     coercion because its alias is transparent there. *)
  [@@@FStar.Tactics.Typeclasses.no_method]
  error_handler_arrow_of_t:
    error_handler_t -> error_handler_arrow base_t len_t pos_t;

  (* The client-supplied context (`EVERPARSE_EXTRA_T`) that the 3D frontend
     threads from the generated wrapper down to the stream primitives. The
     buffer backend sets this to `unit`; the extern/static backends leave it
     abstract so it becomes a real C parameter. Each method below takes it as
     an implicit resolved by [Util.solve_from_ctx] from the enclosing binder,
     exactly as the Low* prelude does. *)
  [@@@FStar.Tactics.Typeclasses.no_method]
  extra_t: Type0;

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
    stt U64.t
    (requires (
      pts_to base len pos contents v
    ))
    (ensures fun res ->
      pts_to base len pos contents v **
      pure (
        U64.v res + Seq.length v == Seq.length contents
      )
    );

  has:
    (#[Util.solve_from_ctx ()] _extra: extra_t) ->
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
     since they track their position in a separate [SZ.t] reference.

     [off] is *relative* to the current position. It carries no precondition:
     on the extern/static backends [has_at] is a client-provided C primitive,
     and a precondition here would be an unchecked proof obligation on
     hand-written code. The out-of-range case is instead left underspecified
     -- callers always have [off] in range, so nothing is lost, and an
     existing client stays correct whatever it answers there.

     Making [off] absolute (so that the non-consuming validators could keep an
     absolute [pos], and the error handler's [start_pos] could be an [SZ.t])
     was considered and rejected. On the extern backend there are three
     distinct positions: the C primitive's own cumulative stream position, the
     [origin] at which the wrapper entered this top-level validation, and
     their difference, which is what [get_position] returns and what the
     field-position actions report. Neither reading of "absolute" works:

       - relative to [origin], the client cannot interpret [off] at all, since
         [stream_has_at] takes the origin as a [Ghost.erased] precisely so the
         C signatures stay free of it (EverParse3d.InputStream.Extern.fst);

       - relative to the stream, the prelude must compute [origin + off] on
         *every* call, and that sum decides whether bytes are in bounds, so it
         needs a real [SZ.add] with a discharged `fits` -- a wrapping
         [add_mod] would be a memory-safety bug, not a cosmetic one.

     The one place a sum of two positions is unavoidable, the error handler's
     [start_pos], is also the one place where it is merely *reported*, so
     [U64.add_mod] is sound there. Keeping [off] relative also keeps the
     client's reasoning purely local, and matches [has], whose [n] is relative
     too. *)
  has_at:
    (#[Util.solve_from_ctx ()] _extra: extra_t) ->
    (base: base_t) ->
    (len: len_t) ->
    (pos: pos_t) ->
    (off: SZ.t) ->
    (n: SZ.t) ->
    (contents: Ghost.erased (Seq.seq U8.t)) ->
    (v: Ghost.erased (Seq.seq U8.t)) ->
    stt bool
    (requires (
      pts_to base len pos contents v
    ))
    (ensures (fun res ->
      pts_to base len pos contents v ** pure (
      SZ.v off <= Seq.length v ==> (
        (res == true <==> SZ.v off + SZ.v n <= Seq.length v) /\
        (res == true ==> SZ.fits (SZ.v off + SZ.v n))
      )
    )));

  read:
    (#[Util.solve_from_ctx ()] _extra: extra_t) ->
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
    (#[Util.solve_from_ctx ()] _extra: extra_t) ->
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
    (#[Util.solve_from_ctx ()] _extra: extra_t) ->
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
     from the original stream through the projections below. Both backends set
     [trunc_t = len_t] -- neither re-bases anything, and truncating only
     shortens the view -- so [truncate] extracts to a scalar-returning function
     and no struct is ever built. *)
  [@@@FStar.Tactics.Typeclasses.no_method]
  trunc_t: Type0;

  trunc_base: (base: base_t) -> (len: len_t) -> (pos: pos_t) -> (tr: trunc_t) -> Tot base_t;

  trunc_len: (base: base_t) -> (len: len_t) -> (pos: pos_t) -> (tr: trunc_t) -> Tot len_t;

  trunc_pos: (base: base_t) -> (len: len_t) -> (pos: pos_t) -> (tr: trunc_t) -> Tot pos_t;

  truncate:
    (#[Util.solve_from_ctx ()] _extra: extra_t) ->
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
