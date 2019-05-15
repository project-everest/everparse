module LowParse.TestLib.Low

open FStar.HyperStack.ST
open FStar.HyperStack.IO
open FStar.Printf
open LowParse.Low.Base

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module U32 = FStar.UInt32
module M = LowStar.Modifies

#reset-options "--using_facts_from '* -LowParse'"
#reset-options "--z3cliopt smt.arith.nl=false"

(** The type of a unit test.  It takes an input buffer8, parses it,
    and returns a newly formatted buffer8.  Or it returns None if
    there is a fail to parse. *)
inline_for_extraction
type testbuffer_t = (#rrel: _) -> (#rel: _) -> (input: slice rrel rel) -> ST (option (slice rrel rel))
  (requires(fun h -> live_slice h input))
  (ensures(fun h0 y h1 ->
    M.modifies M.loc_none h0 h1 /\ (
    match y with
    | None -> true
    | Some out ->
      B.unused_in out.base h0 /\
      live_slice h1 out
  )))

assume val load_file_buffer: (filename:string) -> ST (slice (srel_of_buffer_srel (IB.immutable_preorder _)) (srel_of_buffer_srel (IB.immutable_preorder _)))
  (requires (fun h -> True))
  (ensures (fun h out h' ->
    M.modifies M.loc_none h h' /\ B.unused_in out.base h /\ live_slice h' out
  ))

assume val load_file_buffer_c: (filename:C.String.t) -> ST (slice (srel_of_buffer_srel (IB.immutable_preorder _)) (srel_of_buffer_srel (IB.immutable_preorder _)))
  (requires (fun h -> True))
  (ensures (fun h out h' ->
    M.modifies M.loc_none h h' /\ B.unused_in out.base h /\ live_slice h' out
  ))

(* TODO: implement in LowStar.Buffer *)

module U32 = FStar.UInt32

(** Corresponds to memcmp for `eqtype` *)
(* dirty trick: the additional unit arg prevents F* and KReMLin from viewing preorder arguments as sources of polymorphism *)
assume
val beqb: unit -> (#rrel1: _) -> (#rel1: _) -> (#rrel2: _) -> (#rel2: _) -> b1:B.mbuffer byte (buffer_srel_of_srel rrel1) (buffer_srel_of_srel rel1) -> b2:B.mbuffer byte (buffer_srel_of_srel rrel2) (buffer_srel_of_srel rel2)
  -> len:U32.t{U32.v len <= B.length b1 /\ U32.v len <= B.length b2}
  -> Stack bool
    (requires (fun h ->
      B.live h b1 /\
      B.live h b2
    ))
    (ensures  (fun h0 z h1 -> h1 == h0 /\
      (z <==> Seq.equal (Seq.slice (B.as_seq h0 b1) 0 (U32.v len)) (Seq.slice (B.as_seq h0 b2) 0 (U32.v len)))))

(** Test one parser+formatter pair against an in-memory buffer of UInt8.t *)
inline_for_extraction
noextract
let test_buffer (t:testbuffer_t) (testname:string) (#rrel #rel: _) (input:slice rrel rel)
: ST unit 
(requires (fun h -> live_slice h input))
(ensures (fun _ _ _ -> true)) =
  push_frame();
  print_string (sprintf "==== Testing buffer %s ====\n" testname);
  let result = t input in
  (match result with
  | Some output -> (
    if U32.lte output.len input.len then (
      if beqb () input.base output.base output.len then
        print_string "Formatted data matches original input data\n"
      else (
        print_string "FAIL:  formatted data does not match original input data\n"
      )
    ) else (  
      print_string "Invalid length return - it is longer than the input buffer!"
    ))
  | _ -> print_string "Failed to parse\n"
  ); 
  print_string (sprintf "==== Finished %s ====\n" testname);
  pop_frame()

(** Test one parser+formatter pair against a disk file, using buffer *)
inline_for_extraction
noextract
let test_file_buffer (t:testbuffer_t) (filename:string): ST unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input = load_file_buffer filename in
  (*test_buffer t filename input inputlen;*)
  pop_frame()
