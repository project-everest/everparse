module LowParse.Low.Writers
include LowParse.Low.Base

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module L = FStar.List.Tot

let ifthenelse
  (#t: Type)
  (cond: bool)
  (iftrue: (squash (cond == true) -> GTot t))
  (iffalse: (squash (cond == false) -> GTot t))
: GTot t
= if cond then norm [delta; iota; primops] (iftrue ()) else norm [delta; iota; primops] (iffalse ())

inline_for_extraction
noextract
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

inline_for_extraction
noextract
noeq
type writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type
= | Writer:
    (v: (unit -> GTot t)) ->
    (w: fwriter s h0 sout pout_from0 (v ())) ->
    writer s h0 sout pout_from0

let wvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: GTot t
= norm [delta; iota; primops] (w.v ())

inline_for_extraction
noextract
let weaken_writer
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
= Writer (fun _ -> wvalue w) (fun pout_from -> w.w pout_from)

inline_for_extraction
noextract
let write
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: Tot (fwriter s h0 sout pout_from0 (wvalue w))
= match w with | Writer _ f -> f

inline_for_extraction
noextract
let writer_ifthenelse
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
= Writer (fun _ -> ifthenelse cond (fun _ -> wvalue (wtrue ())) (fun _ -> wvalue (wfalse ())))
  (fun pout_from -> if cond then write (wtrue ()) pout_from else write (wfalse ()) pout_from)

inline_for_extraction
noextract
let write_leaf_cs
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
= Writer (fun _ -> x)
  (fun pout_from ->
    if U32.uint_to_t k.parser_kind_low `U32.gt` (sout.len `U32.sub` pout_from)
    then max_uint32
    else w x sout pout_from
  )

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

inline_for_extraction
noeq
noextract
type lwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type
= | LWriter:
      (v: (unit -> GTot (list t))) ->
      (w: flwriter s h0 sout pout_from0 (v ())) ->
      lwriter s h0 sout pout_from0

inline_for_extraction
noextract
let lwvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
: GTot (list t)
= w.v ()

inline_for_extraction
noextract
let weaken_lwriter
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
= LWriter w.v (fun pout_from -> w.w pout_from)

inline_for_extraction
noextract
let lwrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
: Tot (flwriter s h0 sout pout_from0 (lwvalue w))
= match w with | LWriter _ f -> f

inline_for_extraction
noextract
let lwriter_nil
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == [] })
= LWriter (fun _ -> [])
  (fun pout_from ->
    let h = HST.get () in
    valid_list_nil p h sout pout_from;
    pout_from
  )

inline_for_extraction
noextract
let lwriter_singleton
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == [wvalue w] } )
= LWriter (fun _ -> [wvalue w])
  (fun pout_from ->
    let res = write w pout_from in
    if res `U32.lt` max_uint32
    then begin
      let h = HST.get () in
      valid_list_nil p h sout res;
      valid_list_cons p h sout pout_from res
    end else begin
      [@inline_let]
      let f () : Lemma (ensures (let v = wvalue w in serialized_list_length s [v] == serialized_length s v)) =
        serialized_list_length_cons s (wvalue w) [];
        serialized_list_length_nil s
      in
      f ()
    end;
    res
  )

inline_for_extraction
noextract
let lwriter_append
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w1 w2: lwriter s h0 sout pout_from0)
: Tot (x: lwriter s h0 sout pout_from0 { lwvalue x == lwvalue w1 `List.Tot.append` lwvalue w2 } )
= LWriter (fun _ -> (lwvalue w1 `List.Tot.append` lwvalue w2)) (fun pout_from ->
    let res1 = lwrite w1 pout_from in
    Classical.forall_intro_2 (serialized_list_length_append s);
    if res1 = max_uint32
    then
      res1
    else begin
      let res2 = lwrite w2 res1 in
      let h = HST.get () in
      valid_list_serialized_list_length s h sout pout_from res1;
      if res2 `U32.lt` (max_uint32)
      then begin
        valid_list_serialized_list_length s h sout res1 res2;
        valid_list_append p h sout pout_from res1 res2;
        valid_list_serialized_list_length s h sout pout_from res2
      end;
      res2
    end
  )

inline_for_extraction
noextract
let lwriter_cons
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (whead: writer s h0 sout pout_from0)
  (wtail: lwriter s h0 sout pout_from0)
: Tot (w' : lwriter s h0 sout pout_from0 { lwvalue w' == wvalue whead :: lwvalue wtail } )
= LWriter (fun _ -> wvalue whead :: lwvalue wtail) (fun pout -> lwrite (lwriter_append (lwriter_singleton whead) wtail) pout)

inline_for_extraction
noextract
let lwriter_ifthenelse
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
= LWriter (fun _ -> ifthenelse cond (fun _ -> lwvalue (wtrue ())) (fun _ -> lwvalue (wfalse ())))
  (fun pout_from -> if cond then lwrite (wtrue ()) pout_from else lwrite (wfalse ()) pout_from)

inline_for_extraction
noextract
let lwriter_list_map
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
= LWriter (fun _ -> (List.Tot.map f (contents_list p1 h0 sin pin_from pin_to))) (fun pout_from ->
    assert (k1.parser_kind_subkind == Some ParserStrong);
    let h = HST.get () in
    list_map
      j1
      s2
      f
      h
      sin pin_from pin_to
      sout pout_from
      (fun pin_ pout_ ->
        valid_pos_frame_strong p1 h0 sin pin_ (get_valid_pos p1 h sin pin_) (loc_slice_from sout pout_from0) h;
        write (f' pin_) pout_
      )
  )


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

inline_for_extraction
noextract
noeq
type owriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type
= | OWriter:
    (v: (unit -> GTot (option t))) ->
    (w: fowriter s h0 sout pout_from0 (v ())) ->
    owriter s h0 sout pout_from0

let owvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
: GTot (option t)
= w.v ()

inline_for_extraction
noextract
let weaken_owriter
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
= OWriter w.v (fun pout_from -> w.w pout_from)

inline_for_extraction
noextract
let owrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
: Tot (fowriter s h0 sout pout_from0 (owvalue w))
= match w with | OWriter _ f -> f

inline_for_extraction
noextract
let owriter_ifthenelse
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
= OWriter (fun _ -> ifthenelse cond (fun _ -> owvalue (wtrue ())) (fun _ -> owvalue (wfalse ())))
  (fun pout_from -> if cond then owrite (wtrue ()) pout_from else owrite (wfalse ()) pout_from)

inline_for_extraction
noextract
let owrite_leaf_cs
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
= OWriter (fun _ -> (Some x))
  (fun pout_from ->
    if U32.uint_to_t k.parser_kind_low `U32.gt` (sout.len `U32.sub` pout_from)
    then max_uint32
    else w x sout pout_from
  )

inline_for_extraction
noextract
let owriter_of_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: writer s h0 sout pout_from0)
: Tot (x: owriter s h0 sout pout_from0 { owvalue x == Some (wvalue w) })
= OWriter (fun _ -> (Some (wvalue w))) (fun pout_from -> write w pout_from)

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

inline_for_extraction
noeq
noextract
type olwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Type
= | OLWriter:
      (v: (unit -> GTot (option (list t)))) ->
      (w: folwriter s h0 sout pout_from0 (v ())) ->
      olwriter s h0 sout pout_from0

inline_for_extraction
noextract
let olwvalue
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: olwriter s h0 sout pout_from0)
: GTot (option (list t))
= w.v ()

inline_for_extraction
noextract
let weaken_olwriter
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
= OLWriter w.v (fun pout_from -> w.w pout_from)

inline_for_extraction
noextract
let olwrite
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: olwriter s h0 sout pout_from0)
: Tot (folwriter s h0 sout pout_from0 (olwvalue w))
= match w with | OLWriter _ f -> f

inline_for_extraction
noextract
let olwriter_nil
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == Some [] })
= OLWriter (fun _ -> (Some []))
  (fun pout_from ->
    let h = HST.get () in
    valid_list_nil p h sout pout_from;
    pout_from
  )

inline_for_extraction
noextract
let olwriter_singleton
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: owriter s h0 sout pout_from0)
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == (match owvalue w with None -> None | Some x -> Some [x]) })
= OLWriter (fun _ -> (match owvalue w with None -> None | Some x -> Some [x]))
  (fun pout_from ->
    let res = owrite w pout_from in
    if res `U32.lt` (max_uint32 `U32.sub` 1ul)
    then begin
      let h = HST.get () in
      valid_list_nil p h sout res;
      valid_list_cons p h sout pout_from res
    end else begin
      [@inline_let]
      let f () : Lemma (requires (Some? (owvalue w))) (ensures (match owvalue w with | None -> False | Some v -> serialized_list_length s [v] == serialized_length s v)) =
        serialized_list_length_cons s (Some?.v (owvalue w)) [];
        serialized_list_length_nil s
      in
      Classical.move_requires f ()
    end;
    res
  )

inline_for_extraction
noextract
let olwriter_append
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w1 w2: olwriter s h0 sout pout_from0)
: Tot (x: olwriter s h0 sout pout_from0 { olwvalue x == (match olwvalue w1, olwvalue w2 with | Some l1, Some l2 -> Some (l1 `List.Tot.append` l2) | _ -> None) } )
= OLWriter (fun _ -> (match norm [delta; iota; primops] (olwvalue w1) with | None -> None | Some l1 -> match norm [delta; iota; primops] (olwvalue w2) with | Some l2 -> Some (l1 `List.Tot.append` l2) | _ -> None)) (fun pout_from ->
    let res1 = olwrite w1 pout_from in
    Classical.forall_intro_2 (serialized_list_length_append s);
    if (max_uint32 `U32.sub` 1ul) `U32.lte` res1
    then
      res1
    else begin
      let res2 = olwrite w2 res1 in
      let h = HST.get () in
      valid_list_serialized_list_length s h sout pout_from res1;
      if res2 `U32.lt` (max_uint32 `U32.sub` 1ul)
      then begin
        valid_list_serialized_list_length s h sout res1 res2;
        valid_list_append p h sout pout_from res1 res2;
        valid_list_serialized_list_length s h sout pout_from res2
      end;
      res2
    end
  )

inline_for_extraction
noextract
let olwriter_ifthenelse
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
= OLWriter (fun _ -> ifthenelse cond (fun _ -> olwvalue (wtrue ())) (fun _ -> olwvalue (wfalse ())))
  (fun pout_from -> if cond then olwrite (wtrue ()) pout_from else olwrite (wfalse ()) pout_from)

inline_for_extraction
noextract
let olwriter_of_lwriter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (w: lwriter s h0 sout pout_from0)
: Tot (olwriter s h0 sout pout_from0)
= OLWriter (fun _ -> (Some (lwvalue w))) (fun pout_from -> lwrite w pout_from)

inline_for_extraction
noextract
let wcopy
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
= Writer (fun _ -> (contents p h0 sin pin_from)) (fun sout_from ->
    copy_weak_with_length p sin pin_from pin_to sout sout_from
  )

inline_for_extraction
noextract
let wjcopy
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
= Writer (fun _ -> (contents p h0 sin pin_from)) (fun sout_from ->
    copy_weak p j sin pin_from sout sout_from
  )

(* monadic-style bind to read contents from h0 *)

inline_for_extraction
let fgreader
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (#t: Type)
  (x: t)
: Tot Type
=
      unit ->
      HST.Stack t
      (requires (fun h ->
        B.modifies (loc_slice_from sout pout_from0) h0 h
      ))
      (ensures (fun h res h' ->
        B.modifies B.loc_none h h' /\
        res == x
      ))

inline_for_extraction
noextract
noeq
type greader
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (t: Type)
= | GReader:
    (v: (unit -> GTot t)) ->
    (f: fgreader h0 sout pout_from0 (v ())) ->
    greader h0 sout pout_from0 t

let grvalue
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#t: Type)
  (r: greader h0 sout pout_from0 t)
: GTot t
= (GReader?.v r) ()

inline_for_extraction
noextract
let gread
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
= match r with
  | GReader _ f -> f ()

inline_for_extraction
noextract
let wbind
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
= Writer (fun _ -> (wvalue (w (grvalue r)))) (fun pout_from ->
    let v = gread r in
    write (w v) pout_from
  )

inline_for_extraction
noextract
let owbind
  (#tr: Type)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p { k.parser_kind_subkind == Some ParserStrong } )
  (#h0: HS.mem)
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (r: greader h0 sout pout_from0 tr)
  (w: ((x: tr) -> Pure (owriter s h0 sout pout_from0) (requires (x == grvalue r)) (ensures (fun _ -> True))))
: Tot (w' : owriter s h0 sout pout_from0 { owvalue w' == owvalue (w (grvalue r))})
= OWriter (fun _ -> (owvalue (w (grvalue r)))) (fun pout_from ->
    let v = gread r in
    owrite (w v) pout_from
  )

inline_for_extraction
noextract
let lwbind
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
= LWriter (fun _ -> (lwvalue (w (grvalue r)))) (fun pout_from ->
    let v = gread r in
    lwrite (w v) pout_from
  )

inline_for_extraction
noextract
let olwbind
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
= OLWriter (fun _ -> (olwvalue (w (grvalue r)))) (fun pout_from ->
    let v = gread r in
    olwrite (w v) pout_from
  )

inline_for_extraction
noextract
let greader_tot
  (h0: HS.mem)
  (sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t)
  (#t: Type)
  (x: t)
: Tot (r: greader h0 sout pout_from0 t { grvalue r == x } )
= GReader (fun _ -> x) (fun _ -> let _ = HST.get () in x)

inline_for_extraction
noextract
let graccess
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
= GReader (fun _ -> (slice_access h0 g sin pin)) (fun _ ->
    a sin pin
  )
  
inline_for_extraction
noextract
let read_leaf
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
= GReader (fun _ -> (contents p h0 sin pin)) (fun _ ->
    r sin pin
  )

assume val grlexistsb'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool)) // should be GTot, but List.find requires Tot
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
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
    Tot (r: greader h0 sout pout_from0 bool { grvalue r == f (contents p h0 sl pos1) })
  ))
: Tot (r' : fgreader h0 sout pout_from0 (L.existsb f (contents_list p h0 sl pos pos')))

inline_for_extraction
noextract
let grlexistsb
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> Tot bool)) // should be GTot, but List.find requires Tot
  (#rrel #rel: _)
  (sl: slice rrel rel)
  (pos pos' : U32.t)
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
    Tot (r: greader h0 sout pout_from0 bool { grvalue r == f (contents p h0 sl pos1) })
  ))
: Tot (r' : greader h0 sout pout_from0 bool { grvalue r' == L.existsb f (contents_list p h0 sl pos pos') } )
= GReader (fun _ -> (L.existsb f (contents_list p h0 sl pos pos'))) (grlexistsb' j f sl pos pos' sout pout_from0 h0 f')
// (fun _ -> list_existsb j f f' sl pos pos')

inline_for_extraction
noextract
let grifthenelse
  (#h0: HS.mem)  
  (#sout: slice (srel_of_buffer_srel (B.trivial_preorder _)) (srel_of_buffer_srel (B.trivial_preorder _)))
  (#pout_from0: U32.t)
  (#t: Type)
  (cond: bool)
  (grtrue: (squash (cond == true) -> Tot (greader h0 sout pout_from0 t)))
  (grfalse: (squash (cond == false) -> Tot (greader h0 sout pout_from0 t)))
: Tot (r' : greader h0 sout pout_from0 t { grvalue r' == (if cond then grvalue (grtrue ()) else grvalue (grfalse ())) } )
= GReader (fun _ -> ifthenelse cond (fun _ -> grvalue (grtrue ())) (fun _ -> grvalue (grfalse ()))) (fun _ ->
    if cond then gread (grtrue ()) else gread (grfalse ())
  )
