import proofs.WithdrawalCall

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def withdrawalInputCredit (accounts : AccountMap) (I : ExecutionEnv) : UInt256 :=
  withdrawalClaimWord (sstoreAccountMap I.codeOwner accounts ⟨6⟩ ⟨1⟩) I

def withdrawalOutputAccounts (before after : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner after (withdrawalClaimSlot I)
      (UInt256.sub (withdrawalInputCredit before I) (calldataWord I.calldata 36))) ⟨6⟩ ⟨0⟩

/-- Every writable withdrawal rejects or pays, debits saved credit, and releases the lock. -/
theorem withdrawal_bytecode_classification {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (WithdrawalBytecodeChecks σ I ∧ ∃ cA' after data,
        WithdrawalPaymentWitness (initState cA gh bl σ σ₀ g A I) I cA
          (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩)
          (calldataWord I.calldata 4) (calldataWord I.calldata 36) cA' after data ∧
        RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
          (cA', withdrawalOutputAccounts σ after I) ByteArray.empty) := by
  rcases withdrawal_bytecode_prelude (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, _, _, checked⟩
  · exact .inl rejected
  · have memorySize := twoWordHashMem_size_96 (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem_size
    have freePointer := twoWordHashMem_read64 (calldataWord I.calldata 4) ⟨5⟩
      solcFreePtrMem_size solcFreePtrMem_read64
    obtain ⟨gasArg, _, _, setup⟩ := withdrawal_bytecode_payment_setup
      (withdrawalInputCredit σ I) [⟨226⟩, ⟨0xbb3ef682⟩] (by decide)
      checks.canonical memorySize freePointer checked
    rcases withdrawal_bytecode_call gasArg (withdrawalInputCredit σ I)
        (calldataWord I.calldata 36) (calldataWord I.calldata 4) [⟨226⟩, ⟨0xbb3ef682⟩]
        (by decide) writable memorySize freePointer setup with
      rejected | ⟨cA', after, data, _, _, _, _, payment, paid⟩
    · exact .inl rejected
    · obtain ⟨_, _, _, _, finished⟩ := withdrawal_bytecode_debit ⟨1⟩ (withdrawalInputCredit σ I)
        (calldataWord I.calldata 36) (calldataWord I.calldata 4) ⟨226⟩ [⟨0xbb3ef682⟩]
        (by decide) writable checks.canonical checks.covered
        (jumpScan_valid runtimeBytecode 226 240 (by decide +kernel)) paid
      exact .inr ⟨checks, cA', after, data, payment,
        (runtime_run finished with [jumpdest]).stop (by decide +kernel) (by evm_ov)⟩

/-- Accepted EVM execution has an actual payment witness and the exact final debit. -/
theorem withdrawal_xi_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    WithdrawalBytecodeChecks σ I ∧ output = ByteArray.empty ∧ ∃ after data,
      WithdrawalPaymentWitness (initState cA gh bl σ σ₀ g A I) I cA
        (sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩)
        (calldataWord I.calldata 4) (calldataWord I.calldata 36) cA' after data ∧
      σ' = withdrawalOutputAccounts σ after I := by
  rcases withdrawal_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, created, after, data, payment, returned⟩
  · rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  · rcases returned with failed | ⟨finalState, result, accounts⟩
    · have impossible := Xi_error_of_X (g := g.toUInt256) (by
        rw [← code] at failed
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using failed)
      rw [success] at impossible
      cases impossible
    · have actual := Xi_success_of_X (g := g.toUInt256) (by
        rw [← code] at result
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using result)
      rw [success] at actual
      cases actual
      have createdEq : finalState.createdAccounts = created := congrArg Prod.fst accounts
      rw [← createdEq] at payment
      exact ⟨checks, rfl, after, data, payment, congrArg Prod.snd accounts⟩

end Rollup.EVM
