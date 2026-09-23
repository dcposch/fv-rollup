import proofs.BatchCorrespondence
import proofs.SelectorTable
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchABITypes : List ABIType :=
  [abiUInt256, abiBytes32, abiBytes32, abiAddress, abiUInt256, abiAddress, abiUInt256]

def batchABINames : List Ident :=
  ["nextBatchNumber", "oldRoot", "newRoot", "depositOwner", "depositAmount", "withdrawalOwner", "withdrawalAmount"]

private theorem calldata_root_value (cd : ByteArray) (off : Nat) (enough : off + 32 ≤ cd.size) :
    Value.fixedBytes abiBytes32Width ((cd.toList.drop off).take 32) =
      rootValue (calldataWord cd off).val := by
  have read := readBytes_at_toList_any cd off enough
  have readSize : (cd.readBytes off 32).size = 32 := by
    change (cd.readBytes off 32).data.size = 32
    rw [← Array.length_toList, read, List.length_take, List.length_drop, Array.length_toList]
    change min 32 (cd.size - off) = 32
    omega
  have bytes : (calldataWord cd off).toByteArray.toList = (cd.toList.drop off).take 32 := by
    rw [toByteArray_eq_toBytesBE, byteArray_toList_eq]
    rw [toBytesBE_uInt256OfByteArray_of_size readSize]
    simpa only [byteArray_toList_eq] using read
  rw [← bytes]
  rfl

private theorem batch_decode_cons {ty : ABIType} {types : List ABIType} {bytes : List UInt8}
    {cursor : Nat} {value : Value}
    (static : isDynamicABIType ty = false) (size : staticABIEncodedSize? ty = some 32)
    (decoded : decodeABIValue? ty bytes cursor = some (value, cursor + 32))
    (bound : cursor + 32 ≤ 224) :
    decodeABIValues? (ty :: types) bytes 0 cursor 224 224 =
      (decodeABIValues? types bytes 0 (cursor + 32) 224 224).map
        (fun result => (value :: result.1, result.2)) := by
  rw [decodeABIValues?, static]
  simp only [Bool.false_eq_true, if_false, size, bind, Option.bind, Nat.zero_add, decoded]
  simp only [max_eq_left bound]
  cases decodeABIValues? types bytes 0 (cursor + 32) 224 224 <;> rfl

/-- Decode all seven static ABI values, including the two roots. -/
theorem batch_abi_values (I : ExecutionEnv) (length : 228 ≤ I.calldata.size)
    (depositCanonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (withdrawalCanonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus) :
    decodeABIValues? batchABITypes (I.calldata.toList.drop 4) 0 0 224 224 =
      some (entryArguments (.executeBatch (batchFromCalldata I)), 224) := by
  have size : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have enough (off : Nat) (bound : off + 36 ≤ 228) :
      (((I.calldata.toList.drop 4).drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, size]
    omega
  have word (off : Nat) (bound : off + 36 ≤ 228) :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop off).take 32) = calldataWord I.calldata (off + 4) := by
    rw [List.drop_drop]
    simpa only [Nat.add_comm] using decode_word_at_eq I.calldata (off + 4) (by omega) (by
      have limit : 228 < 2 ^ 64 := by decide
      omega)
  have root (off : Nat) (bound : off + 36 ≤ 228) :
      Value.fixedBytes abiBytes32Width (((I.calldata.toList.drop 4).drop off).take 32) =
        rootValue (calldataWord I.calldata (off + 4)).val := by
    rw [List.drop_drop]
    simpa only [Nat.add_comm] using calldata_root_value I.calldata (off + 4) (by omega)
  have first := decodeABIValue_uint256_ok (enough 0 (by decide))
  have oldRoot := decodeABIValue_bytes32_ok (enough 32 (by decide))
  have newRoot := decodeABIValue_bytes32_ok (enough 64 (by decide))
  have depositOwner := decodeABIValue_address_ok (enough 96 (by decide)) (by
    rw [word 96 (by decide)]; exact depositCanonical)
  have depositAmount := decodeABIValue_uint256_ok (enough 128 (by decide))
  have withdrawalOwner := decodeABIValue_address_ok (enough 160 (by decide)) (by
    rw [word 160 (by decide)]; exact withdrawalCanonical)
  have withdrawalAmount := decodeABIValue_uint256_ok (enough 192 (by decide))
  rw [word 0 (by decide)] at first
  rw [root 32 (by decide)] at oldRoot
  rw [root 64 (by decide)] at newRoot
  rw [word 96 (by decide)] at depositOwner
  rw [word 128 (by decide)] at depositAmount
  rw [word 160 (by decide)] at withdrawalOwner
  rw [word 192 (by decide)] at withdrawalAmount
  unfold batchABITypes
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) first (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) oldRoot (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) newRoot (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) depositOwner (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) depositAmount (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) withdrawalOwner (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) withdrawalAmount (by decide)]
  rw [decodeABIValues?]
  rfl

/-- Valid batch calldata decodes to the source parameter store. -/
theorem batch_abi_decode (I : ExecutionEnv) (length : 228 ≤ I.calldata.size)
    (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (depositCanonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus)
    (withdrawalCanonical : (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (contract.transitions[1]!.params.map Param.name)
      (transitionSignature contract.transitions[1]!).paramTypes I.calldata =
      some (batchLocals (batchFromCalldata I)) := by
  change decodeCalldata batchABINames batchABITypes I.calldata = _
  have size : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  rw [if_neg (by rw [size]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [batchABITypes, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, huge⟩; rw [List.length_drop, size] at huge; omega)]
  rw [if_neg (by simp [batchABITypes, solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? batchABITypes = some 224 from by
    simp [batchABITypes, abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?]]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, size]; omega : ¬ (I.calldata.toList.drop 4).length < 224)]
  rw [batch_abi_values I length depositCanonical withdrawalCanonical]
  rfl

private theorem batch_decode_failure {ty : ABIType} {types : List ABIType} {bytes : List UInt8}
    {cursor : Nat}
    (static : isDynamicABIType ty = false) (size : staticABIEncodedSize? ty = some 32)
    (decoded : decodeABIValue? ty bytes cursor = none) :
    decodeABIValues? (ty :: types) bytes 0 cursor 224 224 = none := by
  rw [decodeABIValues?, static]
  simp only [Bool.false_eq_true, if_false, size, bind, Option.bind, Nat.zero_add, decoded]

/-- Either noncanonical address makes the batch argument decoder reject. -/
theorem batch_abi_bad_owner (I : ExecutionEnv) (length : 228 ≤ I.calldata.size)
    (invalid : ¬ ((calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
      (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus)) :
    decodeABIValues? batchABITypes (I.calldata.toList.drop 4) 0 0 224 224 = none := by
  have size : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have enough (off : Nat) (bound : off + 36 ≤ 228) :
      (((I.calldata.toList.drop 4).drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, size]
    omega
  have word (off : Nat) (bound : off + 36 ≤ 228) :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop off).take 32) = calldataWord I.calldata (off + 4) := by
    rw [List.drop_drop]
    simpa only [Nat.add_comm] using decode_word_at_eq I.calldata (off + 4) (by omega) (by
      have limit : 228 < 2 ^ 64 := by decide
      omega)
  have root (off : Nat) (bound : off + 36 ≤ 228) :
      Value.fixedBytes abiBytes32Width (((I.calldata.toList.drop 4).drop off).take 32) =
        rootValue (calldataWord I.calldata (off + 4)).val := by
    rw [List.drop_drop]
    simpa only [Nat.add_comm] using calldata_root_value I.calldata (off + 4) (by omega)
  have first := decodeABIValue_uint256_ok (enough 0 (by decide))
  have oldRoot := decodeABIValue_bytes32_ok (enough 32 (by decide))
  have newRoot := decodeABIValue_bytes32_ok (enough 64 (by decide))
  rw [word 0 (by decide)] at first
  rw [root 32 (by decide)] at oldRoot
  rw [root 64 (by decide)] at newRoot
  unfold batchABITypes
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) first (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) oldRoot (by decide)]
  rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) newRoot (by decide)]
  by_cases canonical : (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus
  · have depositOwner := decodeABIValue_address_ok (enough 96 (by decide)) (by
      rw [word 96 (by decide)]; exact canonical)
    have depositAmount := decodeABIValue_uint256_ok (enough 128 (by decide))
    have withdrawalOwner := decodeABIValue_address_none_noncanon (enough 160 (by decide)) (by
      rw [word 160 (by decide)]; exact fun allowed => invalid ⟨canonical, allowed⟩)
    rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) depositOwner (by decide)]
    rw [batch_decode_cons (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) depositAmount (by decide)]
    rw [batch_decode_failure (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) withdrawalOwner]
    rfl
  · have depositOwner := decodeABIValue_address_none_noncanon (enough 96 (by decide)) (by
      rw [word 96 (by decide)]; exact canonical)
    rw [batch_decode_failure (by simp [isDynamicABIType]) (by simp [staticABIEncodedSize?]) depositOwner]
    rfl

/-- Invalid length or address words cause ABI rejection before source execution. -/
theorem batch_abi_rejected (I : ExecutionEnv)
    (invalid : ¬ (228 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 100).toNat < _root_.EVM.addressModulus ∧
      (calldataWord I.calldata 164).toNat < _root_.EVM.addressModulus)) :
    decodeCalldataWithMode config.abiDecodeMode (contract.transitions[1]!.params.map Param.name)
      (transitionSignature contract.transitions[1]!).paramTypes I.calldata = none := by
  change decodeCalldata batchABINames batchABITypes I.calldata = none
  have size : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldata
  by_cases four : I.calldata.toList.length < 4
  · rw [if_pos four]
  rw [if_neg four]
  rw [if_neg (by simp [batchABITypes, isDynamicABIType])]
  by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
  · rw [if_neg (by rintro ⟨_, huge⟩; rw [List.length_drop, size] at huge; omega)]
    rw [if_neg (by simp [batchABITypes, solcTotalSizeDynamicGuard])]
    simp only [decodeCalldata.decodeArgs]
    rw [show abiTupleHeadSize? batchABITypes = some 224 from by
      simp [batchABITypes, abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?]]
    simp only [bind, Option.bind]
    by_cases length : 228 ≤ I.calldata.size
    · rw [if_neg (by rw [List.length_drop, size]; omega : ¬ (I.calldata.toList.drop 4).length < 224)]
      rw [batch_abi_bad_owner I length (fun canonical => invalid ⟨length, signedBound, canonical⟩)]
      rfl
    · rw [if_pos (by rw [List.length_drop, size]; omega : (I.calldata.toList.drop 4).length < 224)]
      rfl
  · rw [if_pos (show batchABITypes.isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length from
      ⟨rfl, by rw [List.length_drop, size]; omega⟩)]

end Rollup.EVM
