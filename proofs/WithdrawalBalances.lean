import proofs.CallbackPaymentBalances
import proofs.CallbackPayment

open Solm Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- The model's ETH field is the account ledger balance. -/
theorem project_ethLedger (evm : Ethereum.State) (self : Address) (keys : AccessScope) :
    (project evm self keys).eth = ethLedger evm.accountMap self := by
  rw [ethLedger_lookup]
  rfl

/-- A successful source payment has the proved EVM balance bounds. -/
theorem source_payment_balances {before after : Ethereum.State} {owner : Address}
    {value : Int} {input output : ByteArray} {writable : Bool}
    (initial : LockedWorld before.executionEnv.codeOwner before.accountMap)
    (call : callViaEVM before owner value input (true, after, output) writable) :
    worldEth after.accountMap ≤ worldEth before.accountMap ∧
      ethLedger before.accountMap before.executionEnv.codeOwner - (_root_.EVM.wordOfInt value).toNat ≤
        ethLedger after.accountMap before.executionEnv.codeOwner := by
  cases call with
  | callMade word payment state balance depth =>
    obtain ⟨gas, substate, run⟩ := payment
    subst after
    rw [word] at balance run
    have funds : (_root_.EVM.wordOfInt value).toNat ≤
        ethLedger before.accountMap before.executionEnv.codeOwner := by
      rw [ethLedger_lookup]
      exact balance
    exact payment_call_balances funds initial run.symm

/-- Acquiring the withdrawal lock preserves the ETH bound and pinned code. -/
theorem withdrawal_locked_world {before : Ethereum.State}
    (code : OwnCode before) (world : WorldBounded before) :
    LockedWorld before.executionEnv.codeOwner (withdrawalLockedState before).accountMap := by
  have lockedCode : OwnCode (withdrawalLockedState before) := ownCode_store _ _ _ _ code
  have pinned := ownCode_default code
  obtain ⟨account, found, _⟩ := pinned_account_present pinned
  have lockValue : readWord (withdrawalLockedState before) before.executionEnv.codeOwner ⟨6⟩ = ⟨1⟩ :=
    storageLoad_storageStore_same_present before before.executionEnv.codeOwner found ⟨6⟩ ⟨1⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [withdrawalLockedState, storageStore_executionEnv] using ownCode_default lockedCode
  · rw [← readWord_default, lockValue]
    decide
  · apply (worldBounded_iff_worldEth (withdrawalLockedState before)).mp
    exact worldBounded_store _ _ _ _ world

/-- A withdrawal payment can lose only its specified ETH amount. -/
theorem withdrawal_payment_balances {before after : Ethereum.State} {owner : Address}
    {amount : Nat} {output : ByteArray}
    (code : OwnCode before) (world : WorldBounded before) (amountBound : amount < wordLimit)
    (call : callViaEVM (withdrawalLockedState before) owner amount ByteArray.empty
      (true, after, output)) :
    WorldBounded after ∧
      ethLedger (withdrawalLockedState before).accountMap before.executionEnv.codeOwner - amount ≤
        ethLedger after.accountMap before.executionEnv.codeOwner := by
  have initial := withdrawal_locked_world code world
  have initial' : LockedWorld (withdrawalLockedState before).executionEnv.codeOwner
      (withdrawalLockedState before).accountMap := by
    simpa only [withdrawalLockedState, storageStore_executionEnv] using initial
  have result := source_payment_balances initial' call
  have word : (_root_.EVM.wordOfInt (amount : Int)).toNat = amount := by
    have asWord : (UInt256.ofNat amount).toNat = amount := UInt256.toNat_ofNat_of_lt amountBound
    have encoded := congrArg UInt256.toNat (wordOfInt_ofNat_toNat (UInt256.ofNat amount))
    simpa only [asWord] using encoded
  refine ⟨(worldBounded_iff_worldEth after).mpr
    (result.1.trans_lt (LockedWorld.bounded initial)), ?_⟩
  simpa only [word, withdrawalLockedState, storageStore_executionEnv] using result.2

end Rollup.EVM
