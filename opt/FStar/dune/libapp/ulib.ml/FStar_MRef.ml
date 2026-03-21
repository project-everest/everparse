open Prims
type ('uuuuu, 'p, 'rel) stable = unit
type ('a, 'b, 'r, 'p, 'h) p_pred = unit
type ('uuuuu, 'uuuuu1, 'r, 'p) token = unit FStar_ST.witnessed
let witness_token (m : ('uuuuu, 'uuuuu1) FStar_ST.mref) (p : unit) : 
  unit= FStar_ST.gst_recall (); FStar_ST.gst_witness ()
let recall_token (m : ('uuuuu, 'uuuuu1) FStar_ST.mref) (p : unit) : unit=
  FStar_ST.gst_recall ()
type ('a, 'rel) spred = unit
let recall (uu___ : unit) : unit= FStar_ST.gst_recall ()
let witness (uu___ : unit) : unit= FStar_ST.gst_witness ()
