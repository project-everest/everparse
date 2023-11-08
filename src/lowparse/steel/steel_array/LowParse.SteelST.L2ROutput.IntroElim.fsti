module LowParse.SteelST.L2ROutput.IntroElim
open Steel.ST.Util
include LowParse.SteelST.L2ROutput

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference

val is_l2r_output_buffer
  (a: R.ref (AP.t byte))
  (sz: R.ref SZ.t)
  (res: t)
: Tot vprop

inline_for_extraction
val intro_vp
  (#vsz: Ghost.erased SZ.t)
  (#va: AP.v byte)
  (#a: Ghost.erased (AP.t byte))
  (pa: R.ref (AP.t byte))
  (sz: R.ref SZ.t)
: ST t
     (R.pts_to pa full_perm a `star`
       AP.arrayptr a va `star`
       R.pts_to sz full_perm vsz)
     (fun res ->
       vp res (AP.array_of va) `star`
       is_l2r_output_buffer pa sz res
     )
     (SZ.v vsz == AP.length (AP.array_of va) /\
       AP.array_perm (AP.array_of va) == full_perm
     )
     (fun _ -> True)

inline_for_extraction
val elim_vp
  (#pa: Ghost.erased (R.ref (AP.t byte)))
  (#sz: Ghost.erased (R.ref SZ.t))
  (#va': AP.array byte)
  (a': t)
: STT (AP.t byte)
    (vp a' va' `star`
      is_l2r_output_buffer pa sz a'
    )
    (fun res -> exists_ (fun vres ->
      R.pts_to pa full_perm res `star`
      AP.arrayptr res vres `star`
      R.pts_to sz full_perm (AP.len va') `star`
      pure (
        AP.array_of vres == va'
    )))
