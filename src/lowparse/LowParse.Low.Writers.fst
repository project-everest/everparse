module LowParse.Low.Writers
include LowParse.Low.Base

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module L = FStar.List.Tot

let fwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (x: t)
: Tot Type
= (pout_from: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    B.modifies (loc_slice_from sout pout_from0) h0 h /\
    U32.v pout_from0 <= U32.v pout_from /\
    live_slice h sout /\
    U32.v pout_from <= U32.v sout.len /\
    U32.v sout.len < U32.v max_uint32
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from sout pout_from) h h' /\ (
    if res = max_uint32
    then U32.v pout_from + serialized_length s x > U32.v sout.len
    else valid_content_pos p h' sout pout_from x res
)))

assume val writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type

assume val wvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: GTot t

assume val weaken_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
  (h1: HS.mem)
  (pout_from1: U32.t)
: Pure (w' : writer s h1 sout pout_from1 { wvalue w' == wvalue w } )
  (requires (B.modifies (loc_slice_from sout pout_from0) h0 h1 /\ U32.v pout_from0 <= U32.v pout_from1))
  (ensures (fun _ -> True))

assume val write
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: Tot (fwriter s h0 sout pout_from0 (wvalue w))

assume val writer_ifthenelse
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (cond: bool)
  (wtrue: (squash (cond == true) -> Tot (writer s h0 sout pout_from0)))
  (wfalse: (squash (cond == false) -> Tot (writer s h0 sout pout_from0)))
: Tot (x: writer s h0 sout pout_from0 { wvalue x == (if cond then wvalue (wtrue ()) else wvalue (wfalse ())) } )

assume val write_leaf_cs
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_high == Some k.parser_kind_low /\ k.parser_kind_low < 4294967296 } )
  (w: leaf_writer_strong s)
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (x: t)
: Tot (y: writer s h0 sout pout_from0 { wvalue y == x } )

inline_for_extraction
noextract
let flwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (x: list t)
: Tot Type
= (pout_from: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    live_slice h sout /\
    B.modifies (loc_slice_from sout pout_from0) h0 h /\
    U32.v pout_from0 <= U32.v pout_from /\
    U32.v pout_from <= U32.v sout.len /\
    U32.v sout.len < U32.v max_uint32
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from sout pout_from) h h' /\ (
    if res = max_uint32
    then U32.v pout_from + serialized_list_length s x > U32.v sout.len
    else
      valid_list p h' sout pout_from res /\
      contents_list p h' sout pout_from res ==  x
  )))

assume val lwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type

assume val lwvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
: GTot (list t)

assume val weaken_lwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
  (h1: HS.mem)
  (pout_from1: U32.t)
: Pure (w' : lwriter s h1 sout pout_from1 { lwvalue w' == lwvalue w } )
  (requires (B.modifies (loc_slice_from sout pout_from0) h0 h1 /\ U32.v pout_from0 <= U32.v pout_from1))
  (ensures (fun _ -> True))

assume val lwrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
: Tot (flwriter s h0 sout pout_from0 (lwvalue w))

assume val lwriter_nil
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == [] })

assume val lwriter_singleton
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == [wvalue w] } )

assume val lwriter_append
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w1 w2: lwriter s h0 sout pout_from0)
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == lwvalue w1 `List.Tot.append` lwvalue w2 } )

assume val lwriter_ifthenelse
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (cond: bool)
  (wtrue: (squash (cond == true) -> Tot (lwriter s h0 sout pout_from0)))
  (wfalse: (squash (cond == false) -> Tot (lwriter s h0 sout pout_from0)))
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == (if cond then lwvalue (wtrue ()) else lwvalue (wfalse ())) } )

assume val lwriter_list_map
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2 { k2.parser_kind_subkind == Some ParserStrong /\ k2.parser_kind_low > 0 } )
  (f: t1 -> Tot t2)
  (#rrel #rel: _)
  (sin: slice rrel rel)
  (pin_from pin_to: U32.t)
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t {
    B.loc_disjoint (loc_slice_from sout pout_from0) (loc_slice_from_to sin pin_from pin_to) /\
    valid_list p1 h0 sin pin_from pin_to
  })
  (f' : (
    (pos: U32.t {
      U32.v pin_from <= U32.v pos /\
      valid p1 h0 sin pos /\
      U32.v pos + content_length p1 h0 sin pos <= U32.v pin_to
    }) ->
    Tot (y: writer s2 h0 sout pout_from0 { wvalue y == f (contents p1 h0 sin pos) })
  ))
: Tot (x: lwriter s2 h0 sout pout_from0 { lwvalue x == List.Tot.map f (contents_list p1 h0 sin pin_from pin_to) } )


(* With options (other failures) *)

inline_for_extraction
noextract
let fowriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (x: option t)
: Tot Type
= (pout_from: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    B.modifies (loc_slice_from sout pout_from0) h0 h /\
    U32.v pout_from0 <= U32.v pout_from /\
    live_slice h sout /\
    U32.v pout_from <= U32.v sout.len /\
    U32.v sout.len < U32.v max_uint32 - 1
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from sout pout_from) h h' /\ (
    if res = max_uint32
    then (Some? x ==> U32.v pout_from + serialized_length s (Some?.v x) > U32.v sout.len)
    else if res = max_uint32 `U32.sub` 1ul
    then None? x
    else
    Some? x /\
    valid_content_pos p h' sout pout_from (Some?.v x) res
)))

assume val owriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type

assume val owvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
: GTot (option t)

assume val weaken_owriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
  (h1: HS.mem)
  (pout_from1: U32.t)
: Pure (w' : owriter s h1 sout pout_from1 { owvalue w' == owvalue w } )
  (requires (B.modifies (loc_slice_from sout pout_from0) h0 h1 /\ U32.v pout_from0 <= U32.v pout_from1))
  (ensures (fun _ -> True))

assume val owrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
: Tot (fowriter s h0 sout pout_from0 (owvalue w))

assume val owriter_ifthenelse
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (cond: bool)
  (wtrue: (squash (cond == true) -> Tot (owriter s h0 sout pout_from0)))
  (wfalse: (squash (cond == false) -> Tot (owriter s h0 sout pout_from0)))
: Tot (x: owriter s h0 sout pout_from0 { owvalue x == (if cond then owvalue (wtrue ()) else owvalue (wfalse ())) } )

assume val owrite_leaf_cs
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_high == Some k.parser_kind_low /\ k.parser_kind_low < 4294967296 } )
  (w: leaf_writer_strong s)
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (x: t)
: Tot (y: owriter s h0 sout pout_from0 { owvalue y == Some x } )

assume val owriter_of_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: Tot (x: owriter s h0 sout pout_from0 { owvalue x == Some (wvalue w) })

inline_for_extraction
noextract
let folwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (x: option (list t))
: Tot Type
= (pout_from: U32.t) ->
  HST.Stack U32.t
  (requires (fun h ->
    live_slice h sout /\
    B.modifies (loc_slice_from sout pout_from0) h0 h /\
    U32.v pout_from0 <= U32.v pout_from /\
    U32.v pout_from <= U32.v sout.len /\
    U32.v sout.len < U32.v max_uint32 - 1
  ))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from sout pout_from) h h' /\ (
    if res = max_uint32
    then (Some? x ==> U32.v pout_from + serialized_list_length s (Some?.v x) > U32.v sout.len)
    else if res = max_uint32 `U32.sub` 1ul
    then None? x
    else
      Some? x /\
      valid_list p h' sout pout_from res /\
      contents_list p h' sout pout_from res ==  (Some?.v x)
  )))

assume val olwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type

assume val olwvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: olwriter s h0 sout pout_from0)
: GTot (option (list t))

assume val weaken_olwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: olwriter s h0 sout pout_from0)
  (h1: HS.mem)
  (pout_from1: U32.t)
: Pure (w' : olwriter s h1 sout pout_from1 { olwvalue w' == olwvalue w } )
  (requires (B.modifies (loc_slice_from sout pout_from0) h0 h1 /\ U32.v pout_from0 <= U32.v pout_from1))
  (ensures (fun _ -> True))

assume val olwrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: olwriter s h0 sout pout_from0)
: Tot (folwriter s h0 sout pout_from0 (olwvalue w))

assume val olwriter_nil
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == Some [] })

assume val olwriter_singleton
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == (match owvalue w with None -> None | Some x -> Some [x]) })

assume val olwriter_append
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w1 w2: olwriter s h0 sout pout_from0)
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == (match olwvalue w1, olwvalue w2 with | Some l1, Some l2 -> Some (l1 `List.Tot.append` l2) | _ -> None) } )

assume val olwriter_ifthenelse
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (cond: bool)
  (wtrue: (squash (cond == true) -> Tot (olwriter s h0 sout pout_from0)))
  (wfalse: (squash (cond == false) -> Tot (olwriter s h0 sout pout_from0)))
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == (if cond then olwvalue (wtrue ()) else olwvalue (wfalse ())) } )

assume val olwriter_of_lwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
: Tot (w' : olwriter s h0 sout pout_from0 { olwvalue w' == Some (lwvalue w)} )

assume val wcopy
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
  (#rrel #rel: _)
  (sin: slice rrel rel)
  (pin_from pin_to: U32.t)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (sout_from0: U32.t)
  (h0: HS.mem {
    B.loc_disjoint (loc_slice_from_to sin pin_from pin_to) (loc_slice_from sout sout_from0) /\
    valid_pos p h0 sin pin_from pin_to
  })
: Tot (w: writer s h0 sout sout_from0 {
    wvalue w == contents p h0 sin pin_from
  })

assume val wjcopy
  (#k: _)
  (#t: _)
  (#p: parser k t)
  (s: serializer p {k.parser_kind_subkind == Some ParserStrong})
  (j: jumper p)
  (#rrel #rel: _)
  (sin: slice rrel rel)
  (pin_from: U32.t)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (sout_from0: U32.t)
  (h0: HS.mem {
    valid p h0 sin pin_from /\
    B.loc_disjoint (loc_slice_from_to sin pin_from (get_valid_pos p h0 sin pin_from)) (loc_slice_from sout sout_from0)
  })
: Tot (w: writer s h0 sout sout_from0 {
    wvalue w == contents p h0 sin pin_from
  })

(* monadic-style bind to read contents from h0 *)

assume val greader
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (t: Type)
: Tot Type

assume val grvalue
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#t: Type)
  (r: greader h0 sout pout_from0 t)
: GTot t

assume val gread
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#t: Type)
  (r: greader h0 sout pout_from0 t)
: HST.Stack t
  (requires (fun h ->
    B.modifies (loc_slice_from sout pout_from0) h0 h
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == grvalue r
  ))

assume val wbind
  (#tr: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (r: greader h0 sout pout_from0 tr)
  (w: ((x: tr) -> Pure (writer s h0 sout pout_from0) (requires (x == grvalue r)) (ensures (fun _ -> True))))
: Tot (w' : writer s h0 sout pout_from0 { wvalue w' == wvalue (w (grvalue r)) } )

assume val owbind
  (#tr: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (r: greader h0 sout pout_from0 tr)
  (w: ((x: tr { x == grvalue r }) -> Tot (owriter s h0 sout pout_from0))) // (requires (x == grvalue r)) (ensures (fun _ -> True))))
: Tot (w' : owriter s h0 sout pout_from0 { owvalue w' == owvalue (w (grvalue r))})

assume val lwbind
  (#tr: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (r: greader h0 sout pout_from0 tr)
  (w: ((x: tr) -> Pure (lwriter s h0 sout pout_from0) (requires (x == grvalue r)) (ensures (fun _ -> True))))
: Tot (w' : lwriter s h0 sout pout_from0 { lwvalue w' == lwvalue (w (grvalue r)) } )

assume val olwbind
  (#tr: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (r: greader h0 sout pout_from0 tr)
  (w: ((x: tr) -> Pure (olwriter s h0 sout pout_from0) (requires (x == grvalue r)) (ensures (fun _ -> True))))  
: Pure (olwriter s h0 sout pout_from0)
  (requires True)
  (ensures (fun w' -> olwvalue w' == olwvalue (w (grvalue r))))

assume val greader_tot
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (#t: Type)
  (x: t)
: Tot (r: greader h0 sout pout_from0 t { grvalue r == x } )

assume val graccess
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (#g: gaccessor p1 p2 cl)
  (a: accessor g)
  (#rrel #rel: _)
  (sin: slice rrel rel)
  (pin: U32.t)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (h0: HS.mem {
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    valid p1 h0 sin pin /\
    cl.clens_cond (contents p1 h0 sin pin) /\
    B.loc_disjoint (loc_slice_from_to sin pin (get_valid_pos p1 h0 sin pin)) (loc_slice_from sout pout_from0)
  })
: Tot (r: greader h0 sout pout_from0 U32.t { grvalue r == slice_access h0 g sin pin } )
  
assume val read_leaf
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (r: leaf_reader p)
  (#rrel #rel: _)
  (sin: slice rrel rel)
  (pin: U32.t)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (h0: HS.mem {
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h0 sin pin /\
    B.loc_disjoint (loc_slice_from_to sin pin (get_valid_pos p h0 sin pin)) (loc_slice_from sout pout_from0)
  })
: Tot (r' : greader h0 sout pout_from0 t { grvalue r' == contents p h0 sin pin } )

assume val grlexistsb
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool)) // should be GTot, but List.find requires Tot
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos: U32.t)
  (pos' : U32.t)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (h0: HS.mem {
    k.parser_kind_subkind == Some ParserStrong /\
    valid_list p h0 sl pos pos' /\
    B.loc_disjoint (loc_slice_from_to sl pos pos') (loc_slice_from sout pout_from0)
  })
  (f' : (
    (pos1: U32.t {
      valid p h0 sl pos1 /\
      U32.v pos <= U32.v pos1 /\
      U32.v (get_valid_pos p h0 sl pos1) <= U32.v pos'
    }) ->
    Tot (r' : greader h0 sout pout_from0 bool { grvalue r' == f (contents p h0 sl pos1)})
  ))
: Tot (r' : greader h0 sout pout_from0 bool { grvalue r' == L.existsb f (contents_list p h0 sl pos pos') } )

assume val grifthenelse
  (#h0: HS.mem)  
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#t: Type)
  (cond: bool)
  (grtrue: (squash (cond == true) -> Tot (greader h0 sout pout_from0 t)))
  (grfalse: (squash (cond == false) -> Tot (greader h0 sout pout_from0 t)))
: Tot (r' : greader h0 sout pout_from0 t { grvalue r' == (if cond then grvalue (grtrue ()) else grvalue (grfalse ())) } )
