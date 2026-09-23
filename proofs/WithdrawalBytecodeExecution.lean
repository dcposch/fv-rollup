import proofs.WithdrawalCallResult
import proofs.WithdrawalBytecodeClassification
import proofs.WithdrawalABI
import proofs.WithdrawalCorrespondence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Valid prelude checks reach payment setup, unless gas runs out. -/
theorem withdrawal_bytecode_checked_setup {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) (checks : WithdrawalBytecodeChecks σ I) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨908⟩
      [withdrawalInputCredit σ I, calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨226⟩, ⟨0xbb3ef682⟩]
      (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k C := by
  obtain ⟨_, _, dispatched⟩ := mutation_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) .withdrawal code (by have := checks.length; omega) bounded selector
  obtain ⟨_, _, decoder⟩ := mutation_decoder .withdrawal [⟨0xbb3ef682⟩] (by decide) checks.nonpayable dispatched
  obtain ⟨_, _, decoded⟩ := withdrawal_decode ⟨310⟩ [⟨226⟩, ⟨0xbb3ef682⟩]
    checks.length checks.signedBound bounded checks.canonical
    (jumpScan_valid runtimeBytecode 310 340 (by decide +kernel)) (by decide) decoder
  have entry := runtime_run decoded with [jumpdest, push2 ⟨843⟩,
    jump (jumpScan_valid runtimeBytecode 843 880 (by decide +kernel))]
  obtain ⟨_, _, entered⟩ := withdrawal_bytecode_enter _ (by simp) writable checks.unlocked entry
  rcases withdrawal_bytecode_amount _ _ [⟨226⟩, ⟨0xbb3ef682⟩] (by decide) entered with
    ⟨_, zero⟩ | ⟨_, _, _, checkedAmount⟩
  · exact (checks.positive zero).elim
  · obtain ⟨_, _, loaded⟩ := withdrawal_bytecode_credit_load _ (by decide) checks.canonical
      solcFreePtrMem_size checkedAmount
    rcases withdrawal_bytecode_credit_check _ _ _ [⟨226⟩, ⟨0xbb3ef682⟩] (by decide) loaded with
      ⟨_, uncovered⟩ | ⟨_, _, _, checkedCredit⟩
    · exact (uncovered checks.covered).elim
    · exact ⟨_, _, checkedCredit⟩

/-- Keep the EVM call result and the matching bytecode completion for both payment outcomes. -/
theorem withdrawal_bytecode_checked_call {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩) (checks : WithdrawalBytecodeChecks σ I) :
    let initial := initState cA gh bl σ σ₀ g A I
    ∃ paid after data,
      callViaEVM (withdrawalLockedState initial) (withdrawalOwnerFromCalldata I)
        (Int.ofNat (calldataWord I.calldata 36).toNat) ByteArray.empty (paid, after, data) ∧
      after.executionEnv = I ∧
      (if paid then RDret runtimeBytecode g initial
        (after.createdAccounts, withdrawalOutputAccounts σ after.accountMap I) ByteArray.empty
       else RDrev runtimeBytecode g initial) := by
  let initial := initState cA gh bl σ σ₀ g A I
  have ownerWord : UInt256.ofNat (withdrawalOwnerFromCalldata I).val = calldataWord I.calldata 4 := by
    have same := keyValueToWord_address_of_canonical _ checks.canonical
    rw [keyValueToWord_address] at same
    exact same
  obtain ⟨_, _, checked⟩ := withdrawal_bytecode_checked_setup (cA := cA) (gh := gh) (bl := bl)
    (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector checks
  have memorySize := twoWordHashMem_size_96 (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem_size
  have freePointer := twoWordHashMem_read64 (calldataWord I.calldata 4) ⟨5⟩
    solcFreePtrMem_size solcFreePtrMem_read64
  obtain ⟨gasArg, _, _, setup⟩ := withdrawal_bytecode_payment_setup
    (withdrawalInputCredit σ I) [⟨226⟩, ⟨0xbb3ef682⟩] (by decide)
    checks.canonical memorySize freePointer checked
  rw [← ownerWord] at setup
  obtain ⟨paid, after, data, _, _, call, environment, returned⟩ :=
    withdrawal_call_result (s0 := initial) (g := g) (withdrawalLockedState initial) gasArg (withdrawalInputCredit σ I)
      (calldataWord I.calldata 36) (withdrawalOwnerFromCalldata I) [⟨226⟩, ⟨0xbb3ef682⟩]
      (by decide) (by simpa only [withdrawal_locked_state, initial, initState] using writable)
      (by rw [withdrawal_locked_state]) (by rw [withdrawal_locked_state]) (by rw [withdrawal_locked_state])
      (by simpa only [withdrawal_locked_state, initial, initState] using setup)
  simp only [withdrawal_locked_state, initial, initState] at environment returned
  rw [ownerWord] at returned
  obtain ⟨_, _, _, _, checkedData⟩ := withdrawal_bytecode_return_data
    (if paid then ⟨1⟩ else ⟨0⟩) (withdrawalInputCredit σ I) (calldataWord I.calldata 36)
    (calldataWord I.calldata 4) [⟨226⟩, ⟨0xbb3ef682⟩] (by decide) memorySize freePointer returned
  refine ⟨paid, after, data, call, environment, ?_⟩
  cases paid
  · rcases withdrawal_bytecode_payment_check ⟨0⟩ (withdrawalInputCredit σ I)
        (calldataWord I.calldata 36) (calldataWord I.calldata 4) [⟨226⟩, ⟨0xbb3ef682⟩]
        (by decide) checkedData with ⟨rejected, _⟩ | ⟨nonzero, _⟩
    · exact rejected
    · exact (nonzero rfl).elim
  · rcases withdrawal_bytecode_payment_check ⟨1⟩ (withdrawalInputCredit σ I)
        (calldataWord I.calldata 36) (calldataWord I.calldata 4) [⟨226⟩, ⟨0xbb3ef682⟩]
        (by decide) checkedData with ⟨_, zero⟩ | ⟨_, _, _, checkedPayment⟩
    · cases zero
    · obtain ⟨_, _, _, _, finished⟩ := withdrawal_bytecode_debit ⟨1⟩ (withdrawalInputCredit σ I)
        (calldataWord I.calldata 36) (calldataWord I.calldata 4) ⟨226⟩ [⟨0xbb3ef682⟩]
        (by decide) writable checks.canonical checks.covered
        (jumpScan_valid runtimeBytecode 226 240 (by decide +kernel)) checkedPayment
      exact (runtime_run finished with [jumpdest]).stop (by decide +kernel) (by evm_ov)

end Rollup.EVM
