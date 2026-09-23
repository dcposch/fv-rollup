import proofs.Storage

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- Store an address in the low 160 bits. Keep the upper bits. -/
def packedAddress (old address : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land solcAddrMask address)
    (UInt256.land (UInt256.lnot solcAddrMask) old)

theorem high_address_bits (old : UInt256) :
    (UInt256.land (UInt256.lnot solcAddrMask) old).toNat =
      (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  rw [u256_land_comm, u256_land_toNat]
  have mask : (UInt256.lnot solcAddrMask).toNat = 2 ^ 256 - 2 ^ 160 := by decide
  rw [mask, natLandClearLow old.toNat 160 (by norm_num) old.val.isLt]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt)

theorem packedAddress_toNat (old address : UInt256)
    (canonical : address.toNat < _root_.EVM.addressModulus) :
    (packedAddress old address).toNat = address.toNat + old.toNat / 2 ^ 160 * 2 ^ 160 := by
  rw [packedAddress, solcAddrMask_clean_left canonical, u256_lor_toNat, high_address_bits]
  rw [nat_lor_shift_add address.toNat (old.toNat / 2 ^ 160) 160 canonical]
  exact Nat.mod_eq_of_lt (setAddressOffset0Nat_lt_size old address canonical)

theorem packedAddress_zero (address : UInt256)
    (canonical : address.toNat < _root_.EVM.addressModulus) :
    packedAddress ⟨0⟩ address = address := by
  apply u256_inj
  rw [packedAddress_toNat _ _ canonical]
  simp

/-- The source address write has the same packed word as the EVM write. -/
theorem store_address_packed (evm : Ethereum.State) (slot address : UInt256)
    (canonical : address.toNat < _root_.EVM.addressModulus) :
    storageLocStore evm (addressOffset0Loc slot)
      (.address (AccountAddress.ofNat address.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (packedAddress (readWord evm evm.executionEnv.codeOwner slot) address)) := by
  unfold storageLocStore storageLocWriteWord addressOffset0Loc
  simp only [valueToWord_address_ofNat_canonical address canonical, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take 0 _ ++ List.take 20 _ ++ List.drop 20 _) =
      (packedAddress (readWord evm evm.executionEnv.codeOwner slot) address).toNat
  rw [List.take_zero, List.nil_append, fromBytes'_append,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, packedAddress_toNat _ _ canonical]
  rw [Nat.mod_eq_of_lt (show address.toNat < 256 ^ 20 from canonical)]
  rw [List.length_take, (_root_.EVM.Word.toBytesLEWithSizeProof address).2]
  change address.toNat + 2 ^ 160 * ((readWord evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 160) = _
  ring

end Rollup.EVM
