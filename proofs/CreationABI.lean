import proofs.CreationExecution
import proofs.CreationSource

open Solm ABI Ethereum Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- The deployment encoder emits the two words consumed by the bytecode proof. -/
theorem creation_deployment (sequencer : Address) (root : Root) :
    config.selfDeployment creationBytecode [.address sequencer, rootValue root] =
      some (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) := by
  have length : (UInt256.toByteArray ⟨root⟩).toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    exact toByteArray_size _
  simp [config, genSolidityConstructorDeployment, contract,
    encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType, encodeABIValue?, encodeABIWord?, rootValue, length, zeroBytes,
    creationArgs, word_toBytesBE_toByteArray_eq_toByteArray]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [byteArray_toList_eq]

theorem bytes32_root (bytes : List UInt8) (length : bytes.length = 32) :
    ∃ root : Root, .fixedBytes ⟨31, by decide⟩ bytes = rootValue root := by
  let word := uInt256OfByteArray bytes.toByteArray
  refine ⟨word.val, ?_⟩
  have roundtrip := toBytesBE_uInt256OfByteArray_of_size
    (arr := bytes.toByteArray) (by rw [list_toByteArray_size, length])
  have read : word.toByteArray.toList = bytes := by
    rw [toByteArray_eq_toBytesBE, byteArray_toList_eq]
    simpa [word, byteArray_toList_eq] using roundtrip
  change Value.fixedBytes ⟨31, by decide⟩ bytes = .fixedBytes ⟨31, by decide⟩ word.toByteArray.toList
  rw [read]

theorem encode_address_shape {value : Value} {bytes : List UInt8}
    (encoded : encodeABIValue? (.elem .address) value = some bytes) :
    ∃ address : Address, value = .address address := by
  cases value <;> simp [encodeABIValue?, encodeABIWord?] at encoded
  exact ⟨_, rfl⟩

theorem encode_root_shape {value : Value} {bytes : List UInt8}
    (encoded : encodeABIValue? (.elem (.bytes ⟨31, by decide⟩)) value = some bytes) :
    ∃ root : Root, value = rootValue root := by
  cases value <;> simp [encodeABIValue?, encodeABIWord?, zeroBytes] at encoded
  rename_i width data
  obtain ⟨⟨rfl, length⟩, _⟩ := encoded
  exact bytes32_root data length

/-- Successful deployment encoding fixes both argument types and their count. -/
theorem creation_deployment_shape {args : List Value} {deployed : ByteArray}
    (encoded : config.selfDeployment creationBytecode args = some deployed) :
    ∃ (sequencer : Address) (root : Root),
      args = [.address sequencer, rootValue root] ∧
      deployed = creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩ := by
  have original := encoded
  change (encodeABIValues? [.elem .address, .elem (.bytes ⟨31, by decide⟩)] args).bind
    (fun bytes => some (creationBytecode ++ bytes.toByteArray)) = some deployed at encoded
  obtain ⟨bytes, encoded, _⟩ := Option.bind_eq_some_iff.mp encoded
  simp [encodeABIValues?, abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType] at encoded
  cases args with
  | nil => simp [encodeABIValuesFrom?] at encoded
  | cons first rest =>
    rw [encodeABIValuesFrom?] at encoded
    change (encodeABIValue? (.elem .address) first).bind
      (fun head => encodeABIValuesFrom? [.elem (.bytes ⟨31, by decide⟩)] rest 64 head []) =
        some bytes at encoded
    obtain ⟨head, firstEncoded, restEncoded⟩ := Option.bind_eq_some_iff.mp encoded
    obtain ⟨sequencer, rfl⟩ := encode_address_shape firstEncoded
    cases rest with
    | nil => simp [encodeABIValuesFrom?] at restEncoded
    | cons second tail =>
      rw [encodeABIValuesFrom?] at restEncoded
      change (encodeABIValue? (.elem (.bytes ⟨31, by decide⟩)) second).bind
        (fun word => encodeABIValuesFrom? [] tail 64 (head ++ word) []) = some bytes at restEncoded
      obtain ⟨word, secondEncoded, tailEncoded⟩ := Option.bind_eq_some_iff.mp restEncoded
      obtain ⟨root, rfl⟩ := encode_root_shape secondEncoded
      cases tail with
      | cons _ _ => simp [encodeABIValuesFrom?] at tailEncoded
      | nil =>
        refine ⟨sequencer, root, rfl, ?_⟩
        rw [creation_deployment] at original
        exact (Option.some.inj original).symm

end Rollup.EVM
