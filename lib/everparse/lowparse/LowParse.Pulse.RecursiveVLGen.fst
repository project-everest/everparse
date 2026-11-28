module LowParse.Pulse.RecursiveVLGen
#lang-pulse
open LowParse.Spec.Base
include LowParse.Spec.RecursiveVLGen
open Pulse.Lib.Pervasives
open LowParse.Pulse.Base

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module U32 = FStar.UInt32

(* A constant-stack validator for length-delimited recursive formats
   (e.g. ASN.1 DER TLV trees.) The validator walks the tree in preorder
   with a single cursor. When it enters a node, it first checks that the
   headers of the direct children of that node exactly tile the node
   contents, so that the remaining well-formedness obligations of the
   node and of the rest of the enclosing lists are all subsumed by a
   single obligation on the cursor position, up to a fixed end position.
   Thus, no stack is needed. Each header is read at most twice. *)

let rec_vlgen_hdr_eq
  (p: rec_vlgen_param)
  (v: bytes)
  (pos: nat { pos <= Seq.length v })
: Lemma
  (rec_vlgen_hdr p v pos == begin match parse p.parse_tag (Seq.slice v pos (Seq.length v)) with
  | None -> None
  | Some (h, c1) ->
    begin match parse p.parse_len (Seq.slice v (pos + c1) (Seq.length v)) with
    | None -> None
    | Some (len, c2) -> Some (h, c1 + c2, U32.v len)
    end
  end)
= match parse p.parse_tag (Seq.slice v pos (Seq.length v)) with
  | None -> ()
  | Some (_, c1) -> Seq.slice_slice v pos (Seq.length v) c1 (Seq.length v - pos)

let rec_vlgen_list_ok_tiles'
  (p: rec_vlgen_param)
  (v: bytes)
  (i: nat)
  (e: nat { i <= e /\ e <= Seq.length v })
: Lemma
  (rec_vlgen_list_ok p v i e ==> rec_vlgen_tiles p v i e)
= Classical.move_requires (rec_vlgen_list_ok_tiles p v i) e

let read_header_post
  (p: rec_vlgen_param)
  (v: bytes)
  (pos: SZ.t)
  (bound: SZ.t)
  (cs ce: SZ.t)
  (isn: bool)
  (res: bool)
: Tot prop
= SZ.v pos <= SZ.v bound /\ SZ.v bound <= Seq.length v /\
  begin if res
  then begin match rec_vlgen_hdr p v (SZ.v pos) with
  | Some (h, hs, len) ->
    SZ.v cs == SZ.v pos + hs /\ SZ.v ce == SZ.v cs + len /\ SZ.v ce <= SZ.v bound /\ isn == p.is_node h
  | None -> False
  end
  else begin match rec_vlgen_hdr p v (SZ.v pos) with
  | Some (_, hs, len) -> SZ.v pos + hs + len > SZ.v bound
  | None -> True
  end
  end

(* Reads the header at `pos` and checks that the element fits within `bound` *)
inline_for_extraction
let read_header_t
  (p: rec_vlgen_param u#0 u#0 u#0)
: Tot Type
= (input: S.slice byte) ->
  (pos: SZ.t) ->
  (bound: SZ.t) ->
  (pcs: R.ref SZ.t) ->
  (pce: R.ref SZ.t) ->
  (pisn: R.ref bool) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  (#cs0: Ghost.erased SZ.t) ->
  (#ce0: Ghost.erased SZ.t) ->
  (#isn0: Ghost.erased bool) ->
  stt bool
    (pts_to input #pm v ** R.pts_to pcs cs0 ** R.pts_to pce ce0 ** R.pts_to pisn isn0 ** pure (SZ.v pos <= SZ.v bound /\ SZ.v bound <= Seq.length v))
    (fun res -> pts_to input #pm v ** (exists* cs ce isn . R.pts_to pcs cs ** R.pts_to pce ce ** R.pts_to pisn isn ** pure (read_header_post p v pos bound cs ce isn res)))

let tag_is_node_post
  (p: rec_vlgen_param)
  (v: bytes)
  (pos: SZ.t)
  (res: bool)
: Tot prop
= SZ.v pos <= Seq.length v /\
  begin match parse p.parse_tag (Seq.slice v (SZ.v pos) (Seq.length v)) with
  | Some (h, _) -> res == p.is_node h
  | None -> False
  end

(* Decides whether the tag at `pos` is a node tag *)
inline_for_extraction
let tag_is_node_t
  (p: rec_vlgen_param u#0 u#0 u#0)
: Tot Type
= (input: S.slice byte) ->
  (pos: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt bool
    (pts_to input #pm v ** pure (SZ.v pos <= Seq.length v /\ Some? (parse p.parse_tag (Seq.slice v (SZ.v pos) (Seq.length v)))))
    (fun res -> pts_to input #pm v ** pure (tag_is_node_post p v pos res))

let read_len_post
  (p: rec_vlgen_param)
  (v: bytes)
  (pos: SZ.t)
  (res: SZ.t)
: Tot prop
= SZ.v pos <= Seq.length v /\
  begin match parse p.parse_len (Seq.slice v (SZ.v pos) (Seq.length v)) with
  | Some (len, _) -> SZ.v res == U32.v len
  | None -> False
  end

(* Reads the length at `pos` *)
inline_for_extraction
let read_len_t
  (p: rec_vlgen_param u#0 u#0 u#0)
: Tot Type
= (input: S.slice byte) ->
  (pos: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt SZ.t
    (pts_to input #pm v ** pure (SZ.v pos <= Seq.length v /\ Some? (parse p.parse_len (Seq.slice v (SZ.v pos) (Seq.length v)))))
    (fun res -> pts_to input #pm v ** pure (read_len_post p v pos res))

#push-options "--z3rlimit 32"

#restart-solver

inline_for_extraction
fn mk_read_header
  (#p: Ghost.erased (rec_vlgen_param u#0 u#0 u#0))
  (w_tag: validator (parser_of_tot_parser p.parse_tag))
  (f_is_node: tag_is_node_t p)
  (w_len: validator (parser_of_tot_parser p.parse_len))
  (f_len: read_len_t p)
: read_header_t p
=
  (input: S.slice byte)
  (pos: SZ.t)
  (bound: SZ.t)
  (pcs: R.ref SZ.t)
  (pce: R.ref SZ.t)
  (pisn: R.ref bool)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (#cs0: Ghost.erased SZ.t)
  (#ce0: Ghost.erased SZ.t)
  (#isn0: Ghost.erased bool)
{
  rec_vlgen_hdr_eq p v (SZ.v pos);
  let mut poff = pos;
  let ok1 = w_tag input poff;
  if (not ok1) {
    false
  } else {
    let tag_end = !poff;
    let isn = f_is_node input pos;
    let ok2 = w_len input poff;
    if (not ok2) {
      false
    } else {
      let len_end = !poff;
      if (SZ.gt len_end bound) {
        false
      } else {
        let len = f_len input tag_end;
        if (SZ.gt len (SZ.sub bound len_end)) {
          false
        } else {
          pcs := len_end;
          pce := SZ.add len_end len;
          pisn := isn;
          true
        }
      }
    }
  }
}

#pop-options

let validate_leaf_pre
  (p: rec_vlgen_param)
  (v: bytes)
  (pos cs ce: SZ.t)
: Tot prop
= SZ.v pos <= Seq.length v /\
  begin match rec_vlgen_hdr p v (SZ.v pos) with
  | Some (h, hs, len) ->
    SZ.v cs == SZ.v pos + hs /\ SZ.v ce == SZ.v cs + len /\ SZ.v ce <= Seq.length v /\ p.is_node h == false
  | None -> False
  end

let validate_leaf_post
  (p: rec_vlgen_param)
  (v: bytes)
  (pos cs ce: SZ.t)
  (res: bool)
: Tot prop
= SZ.v pos <= Seq.length v /\
  begin match rec_vlgen_hdr p v (SZ.v pos) with
  | Some (h, hs, len) ->
    SZ.v cs <= SZ.v ce /\ SZ.v ce <= Seq.length v /\
    res == rec_vlgen_leaf_ok p h v (SZ.v cs) (SZ.v ce)
  | None -> False
  end

(* Validates the contents [cs, ce) of a leaf whose header starts at `pos`
   (so that the tag can be read again from `pos`) *)
inline_for_extraction
let validate_leaf_t
  (p: rec_vlgen_param u#0 u#0 u#0)
: Tot Type
= (input: S.slice byte) ->
  (pos: SZ.t) ->
  (cs: SZ.t) ->
  (ce: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased bytes) ->
  stt bool
    (pts_to input #pm v ** pure (validate_leaf_pre p v pos cs ce))
    (fun res -> pts_to input #pm v ** pure (validate_leaf_post p v pos cs ce res))

#push-options "--z3rlimit 32"

#restart-solver

inline_for_extraction
fn validate_rec_vlgen_tiles
  (#p: Ghost.erased (rec_vlgen_param u#0 u#0 u#0))
  (rh: read_header_t p)
  (input: S.slice byte)
  (cs: SZ.t)
  (ce: SZ.t)
  (pcs: R.ref SZ.t)
  (pce: R.ref SZ.t)
  (pisn: R.ref bool)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** (exists* c1 c2 b . R.pts_to pcs c1 ** R.pts_to pce c2 ** R.pts_to pisn b) ** pure (SZ.v cs <= SZ.v ce /\ SZ.v ce <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* c1 c2 b . R.pts_to pcs c1 ** R.pts_to pce c2 ** R.pts_to pisn b) ** pure (SZ.v cs <= SZ.v ce /\ SZ.v ce <= Seq.length v /\ res == rec_vlgen_tiles p v (SZ.v cs) (SZ.v ce))
{
  let mut pq = cs;
  let mut pt = true;
  while (
    let t = !pt;
    let q = !pq;
    (t && SZ.lt q ce)
  ) invariant exists* t q c1 c2 b .
    R.pts_to pt t **
    R.pts_to pq q **
    R.pts_to pcs c1 ** R.pts_to pce c2 ** R.pts_to pisn b **
    pts_to input #pm v **
    pure (
      SZ.v cs <= SZ.v q /\ SZ.v q <= SZ.v ce /\ SZ.v ce <= Seq.length v /\
      rec_vlgen_tiles p v (SZ.v cs) (SZ.v ce) == (t && rec_vlgen_tiles p v (SZ.v q) (SZ.v ce))
    )
    decreases %[(if !pt then 1 else 0); (SZ.v ce - SZ.v (!pq))]
  {
    let q = !pq;
    rec_vlgen_hdr_pos p v (SZ.v q);
    let ok = rh input q ce pcs pce pisn;
    if ok {
      let q' = !pce;
      pq := q'
    } else {
      pt := false
    }
  };
  !pt
}

#pop-options

let validate_rec_vlgen_step_lemma
  (p: rec_vlgen_param)
  (v: bytes)
  (pos: nat)
  (e: nat { pos < e /\ e <= Seq.length v })
: Lemma
  (ensures (
    match rec_vlgen_hdr p v pos with
    | Some (h, hs, len) ->
      (pos + hs + len > e ==> rec_vlgen_list_ok p v pos e == false) /\
      (pos + hs + len <= e ==> (
        (p.is_node h ==> (
          (rec_vlgen_tiles p v (pos + hs) (pos + hs + len) == false ==> rec_vlgen_list_ok p v pos e == false) /\
          (rec_vlgen_tiles p v (pos + hs) (pos + hs + len) == true ==> rec_vlgen_list_ok p v pos e == rec_vlgen_list_ok p v (pos + hs) e)
        )) /\
        (p.is_node h == false ==> rec_vlgen_list_ok p v pos e == (rec_vlgen_leaf_ok p h v (pos + hs) (pos + hs + len) && rec_vlgen_list_ok p v (pos + hs + len) e))
      ))
    | None -> rec_vlgen_list_ok p v pos e == false
  ))
= rec_vlgen_list_ok_cons p v pos e;
  rec_vlgen_hdr_pos p v pos;
  match rec_vlgen_hdr p v pos with
  | Some (h, hs, len) ->
    if pos + hs + len <= e && p.is_node h
    then begin
      rec_vlgen_list_ok_tiles' p v (pos + hs) (pos + hs + len);
      if rec_vlgen_tiles p v (pos + hs) (pos + hs + len)
      then rec_vlgen_list_ok_split p v (pos + hs) (pos + hs + len) e
      else ()
    end
    else ()
  | None -> ()

let validate_rec_vlgen_init_lemma
  (p: rec_vlgen_param)
  (v: bytes)
  (pos: nat { pos <= Seq.length v })
: Lemma
  (ensures (
    match rec_vlgen_hdr p v pos with
    | Some (h, hs, len) ->
      (pos + hs + len > Seq.length v ==> None? (parse (parse_rec_vlgen p) (Seq.slice v pos (Seq.length v)))) /\
      (pos + hs + len <= Seq.length v ==> (
      rec_vlgen_list_ok p v pos (pos + hs + len) == Some? (parse (parse_rec_vlgen p) (Seq.slice v pos (Seq.length v))) /\
      begin match parse (parse_rec_vlgen p) (Seq.slice v pos (Seq.length v)) with
      | Some (_, c) -> c == hs + len
      | None -> True
      end))
    | None -> None? (parse (parse_rec_vlgen p) (Seq.slice v pos (Seq.length v)))
  ))
= parse_rec_vlgen_ok p v pos;
  rec_vlgen_hdr_pos p v pos;
  match rec_vlgen_hdr p v pos with
  | Some (h, hs, len) ->
    if pos + hs + len <= Seq.length v
    then begin
      rec_vlgen_list_ok_cons p v pos (pos + hs + len);
      rec_vlgen_list_ok_nil p v (pos + hs + len)
    end
    else ()
  | None -> ()

#push-options "--z3rlimit 64"

#restart-solver

inline_for_extraction
fn validate_rec_vlgen
  (#p: Ghost.erased (rec_vlgen_param u#0 u#0 u#0))
  (rh: read_header_t p)
  (fl: validate_leaf_t p)
: validator #p.t #(rec_vlgen_kind p) (parse_rec_vlgen p)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset0: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  let off0 = !poffset;
  let mut pcs = 0sz;
  let mut pce = 0sz;
  let mut pisn = false;
  validate_rec_vlgen_init_lemma p v (SZ.v off0);
  let ok0 = rh input off0 (S.len input) pcs pce pisn;
  if (not ok0) {
    false
  } else {
    let end0 = !pce;
    let mut ppos = off0;
    let mut pres = true;
    while (
      let res = !pres;
      let pos = !ppos;
      (res && SZ.lt pos end0)
    ) invariant exists* res pos c1 c2 b .
      R.pts_to pres res **
      R.pts_to ppos pos **
      R.pts_to pcs c1 ** R.pts_to pce c2 ** R.pts_to pisn b **
      pts_to input #pm v **
      R.pts_to poffset off0 **
      pure (
        SZ.v off0 <= SZ.v pos /\ SZ.v pos <= SZ.v end0 /\ SZ.v end0 <= Seq.length v /\
        rec_vlgen_list_ok p v (SZ.v off0) (SZ.v end0) == (res && rec_vlgen_list_ok p v (SZ.v pos) (SZ.v end0))
      )
      decreases %[(if !pres then 1 else 0); (SZ.v end0 - SZ.v (!ppos))]
    {
      let pos = !ppos;
      validate_rec_vlgen_step_lemma p v (SZ.v pos) (SZ.v end0);
      rec_vlgen_hdr_pos p v (SZ.v pos);
      let ok = rh input pos end0 pcs pce pisn;
      if (not ok) {
        pres := false
      } else {
        let cs = !pcs;
        let ce = !pce;
        let isn = !pisn;
        if isn {
          let t = validate_rec_vlgen_tiles rh input cs ce pcs pce pisn;
          if t {
            ppos := cs
          } else {
            pres := false
          }
        } else {
          let b = fl input pos cs ce;
          if b {
            ppos := ce
          } else {
            pres := false
          }
        }
      }
    };
    rec_vlgen_list_ok_nil p v (SZ.v end0);
    let res = !pres;
    if res {
      poffset := end0;
      true
    } else {
      false
    }
  }
}

#pop-options

inline_for_extraction
fn jump_rec_vlgen
  (#p: Ghost.erased (rec_vlgen_param u#0 u#0 u#0))
  (rh: read_header_t p)
: jumper #p.t #(rec_vlgen_kind p) (parse_rec_vlgen p)
=
  (input: S.slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  let mut pcs = 0sz;
  let mut pce = 0sz;
  let mut pisn = false;
  validate_rec_vlgen_init_lemma p v (SZ.v offset);
  parse_rec_vlgen_ok p v (SZ.v offset);
  let ok = rh input offset (S.len input) pcs pce pisn;
  !pce
}
