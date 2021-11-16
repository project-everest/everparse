module EverParse3d.InputStream.Base

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LPE = EverParse3d.ErrorCode
module LP = LowParse.Low.Base

noextract
inline_for_extraction
class input_stream_inst (t: Type) : Type = {
  
  live: t -> HS.mem -> Tot prop;

  footprint: (x: t) -> Ghost B.loc
    (requires True)
    (ensures (fun y -> B.address_liveness_insensitive_locs `B.loc_includes` y));

  perm_footprint: (x: t) -> Ghost B.loc
    (requires True)
    (ensures (fun y -> footprint x `B.loc_includes` y));

  live_not_unused_in:
    (x: t) ->
    (h: HS.mem) ->
    Lemma
    (requires (live x h))
    (ensures (B.loc_not_unused_in h `B.loc_includes` footprint x));

  len_all: (x: t) -> GTot LPE.pos_t;

  get_all: (x: t) -> Ghost (Seq.seq U8.t)
    (requires True)
    (ensures (fun y -> Seq.length y == U64.v (len_all x)));

  get_remaining: (x: t) -> (h: HS.mem) -> Ghost (Seq.seq U8.t)
    (requires (live x h))
    (ensures (fun y -> Seq.length y <= U64.v (len_all x)));

  get_read: (x: t) -> (h: HS.mem) -> Ghost (Seq.seq U8.t)
    (requires (live x h))
    (ensures (fun y -> get_all x `Seq.equal` (y `Seq.append` get_remaining x h)));

  preserved:
    (x: t) ->
    (l: B.loc) ->
    (h: HS.mem) ->
    (h' : HS.mem) ->
    Lemma
    (requires (live x h /\ B.modifies l h h' /\ B.loc_disjoint (footprint x) l))
    (ensures (
      live x h' /\
      get_remaining x h' == get_remaining x h /\
      get_read x h' == get_read x h
    ));

  tlen: t -> Type0;

  has:
    (x: t) ->
    (len: tlen x) ->
    (pos: LPE.pos_t) ->
    (n: U64.t) ->
    HST.Stack bool
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h)
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      (res == true <==> Seq.length (get_remaining x h) >= U64.v n)
    ));

  read:
    (t': Type0) ->
    (k: LP.parser_kind) ->
    (p: LP.parser k t') ->
    (r: LP.leaf_reader p) ->
    (x: t) ->
    (pos: LPE.pos_t) ->
    (n: U64.t) ->
    HST.Stack t'
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      k.LP.parser_kind_subkind == Some LP.ParserStrong /\
      k.LP.parser_kind_high == Some k.LP.parser_kind_low /\
      k.LP.parser_kind_low == U64.v n /\
      U64.v n > 0 /\
      U64.v n < 4294967296 /\
      Some? (LP.parse p (get_remaining x h))
    ))
    (ensures (fun h dst' h' ->
      let s = get_remaining x h in
      B.modifies (perm_footprint x) h h' /\
      Seq.length s >= U64.v n /\
      LP.parse p (Seq.slice s 0 (U64.v n)) == Some (dst', U64.v n) /\
      LP.parse p s == Some (dst', U64.v n) /\
      live x h' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ));

  skip:
    (x: t) ->
    (pos: LPE.pos_t) ->
    (n: U64.t) ->
    HST.Stack unit
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      Seq.length (get_remaining x h) >= U64.v n
    ))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (perm_footprint x) h h' /\
      live x h' /\
      get_remaining x h' `Seq.equal` Seq.slice s (U64.v n) (Seq.length s)
    ));

  skip_if_success:
    (x: t) ->
    (pos: LPE.pos_t) ->
    (res: U64.t) ->
    HST.Stack unit
    (requires (fun h ->
      live x h /\
      (LPE.is_success res ==> (
        U64.v pos == Seq.length (get_read x h)) /\
        U64.v res >= U64.v pos /\
        U64.v pos + Seq.length (get_remaining x h) >= U64.v res
    )))
    (ensures (fun h _ h' ->
      let s = get_remaining x h in
      B.modifies (perm_footprint x) h h' /\
      live x h' /\
      get_remaining x h' == (if LPE.is_success res then Seq.slice s (U64.v res - U64.v pos) (Seq.length s) else get_remaining x h)
    ));

  empty:
    (x: t) ->
    (len: tlen x) ->
    (pos: LPE.pos_t) ->
    HST.Stack LPE.pos_t
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h)
    ))
    (ensures (fun h res h' ->
      B.modifies (perm_footprint x) h h' /\
      live x h' /\
      U64.v res == Seq.length (get_read x h') /\
      get_remaining x h' `Seq.equal` Seq.empty
    ));

  is_prefix_of:
    (x: t) ->
    (y: t) ->
    Tot prop;

  get_suffix:
    (x: t) ->
    (y: t) ->
    Ghost (Seq.seq U8.t)
    (requires (x `is_prefix_of` y))
    (ensures (fun _ -> True));

  is_prefix_of_prop:
    (x: t) ->
    (y: t) ->
    (h: HS.mem) ->
    Lemma
    (requires (
      live x h /\
      x `is_prefix_of` y
    ))
    (ensures (
      live y h /\
      get_read y h `Seq.equal` get_read x h /\
      get_remaining y h `Seq.equal` (get_remaining x h `Seq.append` get_suffix x y)
    ));

  truncate:
    (x: t) ->
    (pos: LPE.pos_t) ->
    (n: U64.t) ->
    HST.Stack t
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      U64.v n <= Seq.length (get_remaining x h)
    ))
    (ensures (fun h res h' ->
      B.modifies B.loc_none h h' /\
      res `is_prefix_of` x /\
      footprint res == footprint x /\
      perm_footprint res == perm_footprint x /\
      live res h' /\
      Seq.length (get_remaining res h') == U64.v n
    ));

  truncate_len:
    (x: t) ->
    (pos: LPE.pos_t) ->
    (n: U64.t) ->
    (res: t) ->
    HST.Stack (tlen res)
    (requires (fun h ->
      live x h /\
      U64.v pos == Seq.length (get_read x h) /\
      U64.v n <= Seq.length (get_remaining x h) /\
      res `is_prefix_of` x /\
      footprint res == footprint x /\
      perm_footprint res == perm_footprint x /\
      live res h /\
      Seq.length (get_remaining res h) == U64.v n
    ))
    (ensures (fun h res_len h' ->
      B.modifies B.loc_none h h'
    ));
  
}

let length_all #t (#_: input_stream_inst t) (x: t) : GTot nat = U64.v (len_all x)

let preserved'
    (#t: Type)
    (# [FStar.Tactics.Typeclasses.tcresolve ()] inst : input_stream_inst t)
    (x: t)
    (l: B.loc)
    (h: HS.mem)
    (h' : HS.mem)
 :  Lemma
    (requires (live x h /\ B.modifies l h h' /\ B.loc_disjoint (footprint x) l))
    (ensures (
      live x h' /\
      get_remaining x h' == get_remaining x h /\
      get_read x h' == get_read x h
    ))
    [SMTPatOr [
      [SMTPat (live x h); SMTPat (B.modifies l h h')];
      [SMTPat (live x h'); SMTPat (B.modifies l h h')];
      [SMTPat (get_remaining x h); SMTPat (B.modifies l h h')];
      [SMTPat (get_remaining x h'); SMTPat (B.modifies l h h')];
      [SMTPat (get_read x h); SMTPat (B.modifies l h h')];
      [SMTPat (get_read x h'); SMTPat (B.modifies l h h')];
    ]]
= preserved x l h h'
