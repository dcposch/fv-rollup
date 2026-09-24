import proofs.RuntimeReturn

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

noncomputable def mappingReturnMem (slot owner word : UInt256) : ByteArray :=
  (UInt256.toByteArray word).write 0 (solcMappingHashMem slot owner) 128 32

private theorem mapping_return_memory (slot owner word : UInt256) :
    mappingReturnMem slot owner word =
      (solcMappingHashMem slot owner ++ ByteArray.zeroes 32) ++ UInt256.toByteArray word := by
  rw [mappingReturnMem, toByteArray_write_eq _ _ _
    (by rw [solcMappingHashMem_size]; omega)
    (by rw [solcMappingHashMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [solcMappingHashMem_size]

private theorem mapping_return_size (slot owner word : UInt256) :
    (mappingReturnMem slot owner word).size = 160 := by
  rw [mapping_return_memory, ByteArray.size_append, ByteArray.size_append,
    solcMappingHashMem_size, zeroes_ofNat_size _ (by norm_num), toByteArray_size]

private theorem mapping_return_read64 (slot owner word : UInt256) :
    (mappingReturnMem slot owner word).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have padded : (solcMappingHashMem slot owner ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcMappingHashMem_size, zeroes_ofNat_size _ (by norm_num)]
  rw [readWithPadding_eq_extract _ _ (by rw [mapping_return_size]; omega), mapping_return_memory,
    extract_append_left _ _ _ _ (by omega),
    extract_append_left _ _ _ _ (by rw [solcMappingHashMem_size]),
    ← readWithPadding_eq_extract _ _ (by rw [solcMappingHashMem_size]),
    solcMappingHashMem_read64]

/-- The return store preserves the free memory pointer. -/
theorem mapping_return_pointer (slot owner word : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (mappingReturnMem slot owner word).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩ else
        UInt256.ofNat (fromByteArrayBigEndian
          ((mappingReturnMem slot owner word).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [mapping_return_size]; decide) (by decide)
    (mapping_return_read64 slot owner word)

/-- The return store contains the requested word. -/
theorem mapping_return_read128 (slot owner word : UInt256) :
    (mappingReturnMem slot owner word).readWithPadding 128 32 = UInt256.toByteArray word := by
  have padded : (solcMappingHashMem slot owner ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcMappingHashMem_size, zeroes_ofNat_size _ (by norm_num)]
  rw [readWithPadding_eq_extract _ _ (by rw [mapping_return_size]), mapping_return_memory,
    extract_append_right' _ _ _ _ (by omega) (by have := toByteArray_size word; omega)]

end Rollup.EVM
