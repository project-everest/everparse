/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/tahina/everest/master/kremlin/krml -ccopt -Ofast -drop FStar.Tactics.\* -drop FStar.Tactics -drop FStar.Reflection.\* -tmpdir out -I .. -bundle LowParse.\* -add-include "kremlin/internal/compat.h" -warn-error -9 ../../src/lowparse/LowParse_TestLib_Low_c.c -no-prefix Test kremlin/FStar_Pervasives_Native.krml kremlin/FStar_Pervasives.krml kremlin/FStar_Preorder.krml kremlin/FStar_Calc.krml kremlin/FStar_Squash.krml kremlin/FStar_Classical.krml kremlin/FStar_StrongExcludedMiddle.krml kremlin/FStar_FunctionalExtensionality.krml kremlin/FStar_List_Tot_Base.krml kremlin/FStar_List_Tot_Properties.krml kremlin/FStar_List_Tot.krml kremlin/FStar_Seq_Base.krml kremlin/FStar_Seq_Properties.krml kremlin/FStar_Seq.krml kremlin/FStar_Mul.krml kremlin/FStar_Math_Lib.krml kremlin/FStar_Math_Lemmas.krml kremlin/FStar_BitVector.krml kremlin/FStar_UInt.krml kremlin/FStar_UInt32.krml kremlin/FStar_Int.krml kremlin/FStar_Int16.krml kremlin/FStar_Range.krml kremlin/FStar_Reflection_Types.krml kremlin/FStar_Tactics_Types.krml kremlin/FStar_Tactics_Result.krml kremlin/FStar_Tactics_Effect.krml kremlin/FStar_Tactics_Util.krml kremlin/FStar_Reflection_Data.krml kremlin/FStar_Reflection_Const.krml kremlin/FStar_Char.krml kremlin/FStar_Exn.krml kremlin/FStar_Set.krml kremlin/FStar_Monotonic_Witnessed.krml kremlin/FStar_Ghost.krml kremlin/FStar_ErasedLogic.krml kremlin/FStar_PropositionalExtensionality.krml kremlin/FStar_PredicateExtensionality.krml kremlin/FStar_TSet.krml kremlin/FStar_Monotonic_Heap.krml kremlin/FStar_Heap.krml kremlin/FStar_ST.krml kremlin/FStar_All.krml kremlin/FStar_List.krml kremlin/FStar_String.krml kremlin/FStar_Order.krml kremlin/FStar_Reflection_Basic.krml kremlin/FStar_Reflection_Derived.krml kremlin/FStar_Tactics_Builtins.krml kremlin/FStar_Reflection_Formula.krml kremlin/FStar_Reflection_Derived_Lemmas.krml kremlin/FStar_Reflection.krml kremlin/FStar_Tactics_Derived.krml kremlin/FStar_Tactics_Logic.krml kremlin/FStar_Tactics.krml kremlin/FStar_Map.krml kremlin/FStar_Monotonic_HyperHeap.krml kremlin/FStar_Monotonic_HyperStack.krml kremlin/FStar_HyperStack.krml kremlin/FStar_HyperStack_ST.krml kremlin/FStar_Universe.krml kremlin/FStar_GSet.krml kremlin/FStar_ModifiesGen.krml kremlin/FStar_BigOps.krml kremlin/LowStar_Monotonic_Buffer.krml kremlin/LowStar_Buffer.krml kremlin/FStar_UInt8.krml kremlin/LowParse_Bytes.krml kremlin/LowParse_Spec_Base.krml kremlin/LowParse_Spec_Combinators.krml kremlin/LowParse_Spec_FLData.krml kremlin/Spec_Loops.krml kremlin/FStar_UInt64.krml kremlin/LowStar_BufferOps.krml kremlin/C_Loops.krml kremlin/LowParse_Math.krml kremlin/LowParse_Slice.krml kremlin/LowParse_Low_Base.krml kremlin/LowParse_Low_Combinators.krml kremlin/LowParse_Low_FLData.krml kremlin/FStar_Int64.krml kremlin/FStar_Int63.krml kremlin/FStar_Int32.krml kremlin/FStar_Int8.krml kremlin/FStar_UInt63.krml kremlin/FStar_UInt16.krml kremlin/FStar_Int_Cast.krml kremlin/FStar_HyperStack_All.krml kremlin/FStar_Kremlin_Endianness.krml kremlin/LowParse_BigEndian.krml kremlin/LowParse_Spec_Int_Aux.krml kremlin/LowParse_Spec_Int.krml kremlin/LowParse_Spec_BoundedInt.krml kremlin/LowStar_Modifies.krml kremlin/LowStar_ModifiesPat.krml kremlin/LowParse_BigEndianImpl_Base.krml kremlin/LowParse_BigEndianImpl_Low.krml kremlin/LowParse_Low_BoundedInt.krml kremlin/LowParse_Spec_SeqBytes_Base.krml kremlin/LowParse_Spec_DER.krml kremlin/LowParse_Spec_BCVLI.krml kremlin/LowParse_Spec_AllIntegers.krml kremlin/LowParse_Spec_VLData.krml kremlin/LowParse_Low_VLData.krml kremlin/LowParse_Spec_VLGen.krml kremlin/LowParse_Low_VLGen.krml kremlin/LowParse_Spec_Int_Unique.krml kremlin/LowParse_Low_Int_Aux.krml kremlin/LowParse_Low_Int.krml kremlin/LowParse_Low_DER.krml kremlin/LowParse_Low_BCVLI.krml kremlin/LowParse_Spec_List.krml kremlin/LowParse_Low_List.krml kremlin/LowParse_Spec_Array.krml kremlin/LowParse_Spec_VCList.krml kremlin/LowParse_Low_VCList.krml kremlin/LowParse_Spec_IfThenElse.krml kremlin/LowParse_Low_IfThenElse.krml kremlin/LowParse_TacLib.krml kremlin/LowParse_Spec_Enum.krml kremlin/LowParse_Spec_Sum.krml kremlin/LowParse_Low_Enum.krml kremlin/LowParse_Low_Sum.krml kremlin/LowParse_Low_Tac_Sum.krml kremlin/LowParse_Spec_Option.krml kremlin/LowParse_Low_Option.krml kremlin/FStar_Bytes.krml kremlin/LowParse_Bytes32.krml kremlin/LowParse_Spec_Bytes.krml kremlin/LowParse_Low_Bytes.krml kremlin/LowParse_Low_Array.krml kremlin/LowParse_Low.krml kremlin/LowParse_SLow_Base.krml kremlin/LowParse_SLow_Combinators.krml kremlin/LowParse_SLow_FLData.krml kremlin/LowParse_SLow_VLGen.krml kremlin/LowParse_BigEndianImpl_SLow.krml kremlin/LowParse_SLow_BoundedInt.krml kremlin/LowParse_SLow_Int_Aux.krml kremlin/LowParse_SLow_Int.krml kremlin/LowParse_SLow_DER.krml kremlin/LowParse_SLow_BCVLI.krml kremlin/LowParse_SLow_List.krml kremlin/LowParse_SLow_VCList.krml kremlin/LowParse_SLow_IfThenElse.krml kremlin/LowParse_SLow_Option.krml kremlin/LowParse_SLow_Enum.krml kremlin/LowParse_SLow_Sum.krml kremlin/LowParse_SLow_Tac_Enum.krml kremlin/LowParse_SLow_Tac_Sum.krml kremlin/LowParse_SLow_VLData.krml kremlin/LowParse_SLow_Bytes.krml kremlin/LowParse_SLow_Array.krml kremlin/LowParse_Spec_Tac_Combinators.krml kremlin/LowParse_SLow.krml kremlin/Tag2.krml kremlin/T15_body.krml kremlin/T3.krml kremlin/T5.krml kremlin/T9_b.krml kremlin/Amount.krml kremlin/Txout_scriptPubKey.krml kremlin/Txout.krml kremlin/Transaction_outputs.krml kremlin/Txin_scriptSig.krml kremlin/Sha256.krml kremlin/Txin.krml kremlin/Transaction_inputs.krml kremlin/Transaction.krml kremlin/Block_tx.krml kremlin/Block.krml kremlin/T25_bpayload.krml kremlin/FStar_Int128.krml kremlin/FStar_Int31.krml kremlin/FStar_UInt128.krml kremlin/FStar_UInt31.krml kremlin/FStar_Integers.krml kremlin/FStar_Printf.krml kremlin/Tagle.krml kremlin/T4.krml kremlin/T6le.krml kremlin/T24_y.krml kremlin/T24.krml kremlin/T25_payload.krml kremlin/T25.krml kremlin/T14_x.krml kremlin/T13_x.krml kremlin/T13.krml kremlin/T18_x_b.krml kremlin/T20.krml kremlin/T21.krml kremlin/C_Endianness.krml kremlin/C.krml kremlin/C_String.krml kremlin/T26.krml kremlin/Tag.krml kremlin/T16_x.krml kremlin/T16.krml kremlin/LowStar_ImmutableBuffer.krml kremlin/FStar_HyperStack_IO.krml kremlin/LowParse_TestLib_Low.krml kremlin/T18_x_a.krml kremlin/T33.krml kremlin/T19.krml kremlin/T1.krml kremlin/T17_x_b.krml kremlin/T22_body_b.krml kremlin/T12_z.krml kremlin/T12.krml kremlin/T2.krml kremlin/T7.krml kremlin/T8_z.krml kremlin/T27.krml kremlin/T14.krml kremlin/T32.krml kremlin/T29.krml kremlin/T36.krml kremlin/T10.krml kremlin/T17_x_a.krml kremlin/T17.krml kremlin/T15.krml kremlin/T35.krml kremlin/T22_body_a.krml kremlin/FStar_Float.krml kremlin/FStar_IO.krml kremlin/T18.krml kremlin/T23.krml kremlin/T9.krml kremlin/T8.krml kremlin/T28.krml kremlin/T6.krml kremlin/Test.krml kremlin/T30.krml kremlin/T11_z.krml kremlin/T34.krml kremlin/T11.krml kremlin/T31.krml kremlin/T22.krml -o test.exe
  F* version: 74c6d2a5
  KreMLin version: 1bd260eb
 */

#include "Sha256.h"

uint32_t Sha256_sha256_validator(LowParse_Slice_slice input, uint32_t pos)
{
  if (input.len - pos < (uint32_t)32U)
    return LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    return pos + (uint32_t)32U;
}

uint32_t Sha256_sha256_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)32U;
}

