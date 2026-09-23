import proofs.WorldBalances

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Account metadata changes preserve the ETH ledger if the balance is unchanged. -/
theorem ethLedger_insert_same_balance (accounts : AccountMap) (owner : Address) (account : Account)
    (same : account.balance.toNat = ethLedger accounts owner) :
    ethLedger (accounts.insert owner account) = ethLedger accounts := by
  rw [ethLedger_insert, same]
  exact Function.update_eq_self owner (ethLedger accounts)

/-- Persistent storage writes preserve every ETH balance. -/
theorem sstore_ethLedger (evm : Ethereum.State) (slot value : UInt256) :
    ethLedger (evm.sstore slot value).accountMap = ethLedger evm.accountMap := by
  unfold Ethereum.State.sstore
  cases found : evm.lookupAccount evm.executionEnv.codeOwner with
  | none => simp [found, Option.option]
  | some account =>
    simp only [found, Option.option, Ethereum.State.setAccount, Ethereum.State.addAccessedStorageKey]
    apply ethLedger_insert_same_balance
    have old : ethLedger evm.accountMap evm.executionEnv.codeOwner = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, Ethereum.State.lookupAccount] at found ⊢
      rw [found]
      rfl
    rw [old]
    unfold Account.updateStorage
    split <;> rfl

/-- Transient storage writes preserve every ETH balance. -/
theorem tstore_ethLedger (evm : Ethereum.State) (slot value : UInt256) :
    ethLedger (evm.tstore slot value).accountMap = ethLedger evm.accountMap := by
  unfold Ethereum.State.tstore
  cases found : evm.lookupAccount evm.executionEnv.codeOwner with
  | none => simp [found, Option.option]
  | some account =>
    simp only [found, Option.option, Ethereum.State.updateAccount]
    apply ethLedger_insert_same_balance
    have old : ethLedger evm.accountMap evm.executionEnv.codeOwner = account.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, Ethereum.State.lookupAccount] at found ⊢
      rw [found]
      rfl
    rw [old]
    unfold Account.updateTransientStorage
    split <;> rfl

end Rollup.EVM
