import proofs.BatchBytecodePrefix
import proofs.BatchBytecodeOwners
import proofs.BatchBytecodeDepositStore

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
-- This syntax linter unfolds symbolic calldata guards. Kernel checks remain active.
set_option linter.constructorNameAsVariable false

namespace Rollup.EVM

/-- Checks made before the backing update. Deposit credit is read after locking. -/
structure BatchAccountingChecks (accounts : AccountMap) (env : ExecutionEnv) : Prop
    extends BatchPrefixChecks accounts env where
  depositOwner : if calldataWord env.calldata 132 = ⟨0⟩ then calldataWord env.calldata 100 = ⟨0⟩
    else calldataWord env.calldata 100 ≠ ⟨0⟩ ∧ UInt256.ofNat env.codeOwner.val ≠ calldataWord env.calldata 100
  withdrawalOwner : if calldataWord env.calldata 196 = ⟨0⟩ then calldataWord env.calldata 164 = ⟨0⟩
    else calldataWord env.calldata 164 ≠ ⟨0⟩ ∧ UInt256.ofNat env.codeOwner.val ≠ calldataWord env.calldata 164
  depositCovered : (calldataWord env.calldata 132).toNat ≤
    (batchDepositWord (sstoreAccountMap env.codeOwner accounts ⟨6⟩ ⟨1⟩) env).toNat

/-- A batch rejects or debits deposit credit and starts the backing calculation. -/
theorem batch_bytecode_accounting_entry {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) :
    let locked := sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩
    let credit := batchDepositWord locked I
    let debited := batchDepositWrite locked I credit
    let mem := twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ solcFreePtrMem
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (BatchAccountingChecks σ I ∧
       ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1385⟩
         (solcSlotWord debited I ⟨3⟩ :: calldataWord I.calldata 132 ::
           ⟨747⟩ :: ⟨0⟩ :: credit :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
         (twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ mem) (UInt256.ofNat 3) ByteArray.empty
         (cA, debited) k C) := by
  dsimp only
  rcases batch_bytecode_prefix (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨header, _, _, entered⟩
  · exact Or.inl rejected
  · rcases batch_bytecode_deposit_owner _ (by decide) header.depositCanonical entered with
      rejected | ⟨depositOwner, _, _, afterDepositOwner⟩
    · exact Or.inl rejected
    · rcases batch_bytecode_withdrawal_owner _ (by decide) header.withdrawalCanonical afterDepositOwner with
        rejected | ⟨withdrawalOwner, _, _, afterOwners⟩
      · exact Or.inl rejected
      · obtain ⟨_, _, loaded⟩ := batch_bytecode_deposit_load _ (by decide) header.depositCanonical
          solcFreePtrMem_size afterOwners
        rcases batch_bytecode_deposit_check _ _ (by decide) loaded with
          rejected | ⟨covered, _, _, checked⟩
        · exact Or.inl rejected
        · obtain ⟨steps, cost, stored⟩ := batch_bytecode_deposit_store _ _ (by decide) writable
            header.depositCanonical (twoWordHashMem_size_96 _ _ solcFreePtrMem_size) checked
          have allChecks : BatchAccountingChecks σ I := by
            constructor
            · with_reducible exact header
            · with_reducible exact depositOwner
            · with_reducible exact withdrawalOwner
            · with_reducible exact covered
          exact Or.inr ⟨allChecks, steps, cost, stored⟩

/-- Every accepted writable batch passed the owner and deposit-credit checks. -/
theorem batch_xi_accounting_checks {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (writable : I.perm = true) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    BatchAccountingChecks σ I := by
  rcases batch_bytecode_accounting_entry (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, _⟩
  · rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  · exact checks

end Rollup.EVM
