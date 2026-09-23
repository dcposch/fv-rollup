import proofs.WorldCreation

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

def incrementNonce (accounts : AccountMap) (sender : Address) : AccountMap :=
  accounts.insert sender { (accounts.findD sender default) with
    nonce := (accounts.findD sender default).nonce + ⟨1⟩ }

/-- The creation nonce update preserves all ETH balances. -/
theorem incrementNonce_ethLedger (accounts : AccountMap) (sender : Address) :
    ethLedger (incrementNonce accounts sender) = ethLedger accounts :=
  ethLedger_insert_same_balance accounts sender _ rfl

/-- The creation nonce update preserves all code and storage. -/
theorem incrementNonce_storage (accounts : AccountMap) (sender self : Address) :
    CodeStorageFrame self accounts (incrementNonce accounts sender) := by
  apply accountStaticStateEq_of_storage_code
  · apply accountStorageStateEq_insert_preserve <;> rfl
  · apply accountCodeStateEq_insert_preserve
    rfl

/-- The opcode's nonce bound prevents increment wraparound. -/
theorem incrementNonce_nonzero (accounts : AccountMap) (sender : Address)
    (bound : (accounts.findD sender default).nonce.toNat < 2 ^ 64 - 1) :
    ((incrementNonce accounts sender).findD sender default).nonce ≠ ⟨0⟩ := by
  simp only [incrementNonce, Batteries.RBMap.findD, accountMap_find_insert_self, Option.getD_some]
  intro zero
  have equation := congrArg UInt256.toNat zero
  rw [uadd_toNat] at equation
  have small : (accounts.findD sender default).nonce.toNat + 1 < UInt256.size := by
    change (accounts.findD sender default).nonce.toNat + 1 < 2 ^ 256
    omega
  simp only [UInt256.zero_toNat] at equation
  change ((accounts.findD sender default).nonce.toNat + 1) % UInt256.size = 0 at equation
  rw [Nat.mod_eq_of_lt small] at equation
  omega

theorem incrementNonce_lockedWorld {accounts : AccountMap} {sender self : Address}
    (initial : LockedWorld self accounts) : LockedWorld self (incrementNonce accounts sender) := by
  apply initial.next (incrementNonce_storage accounts sender self)
  simp only [EthFrame, worldEth, incrementNonce_ethLedger]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Rollup.EVM
