import proofs.WorldExecution
import proofs.LockedCallBalances

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- The nested-call obligation includes the actual code and transfer source. -/
def ProtectedCallBalances (self : Address) (depth : Fin 1025) : Prop :=
  ∀ blobs cA gh bl accounts original substate sender origin receiver code gas price value contextValue
    calldata header writable cA' after gas' substate' accepted output,
    (receiver = self → code = toExecute accounts self) →
    (self ≠ sender ∨ value = ⟨0⟩) →
    value.toNat ≤ ethLedger accounts sender → LockedWorld self accounts →
    Θ blobs cA gh bl accounts original substate sender origin receiver code
      gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output) →
    EthFrame self accounts after

/-- Opcode balance proofs imply balance protection for calls at that depth. -/
theorem protected_call_balances_of_steps {self : Address} {depth : Fin 1025}
    (steps : ForeignStepBalances self depth) : ProtectedCallBalances self depth := by
  intro blobs cA gh bl accounts original substate sender origin receiver code gas price value contextValue
    calldata header writable cA' after gas' substate' accepted output selected safeSender funds initial run
  have pinned := LockedWorld.pinned initial
  have locked := LockedWorld.locked initial
  have world := LockedWorld.bounded initial
  by_cases own : receiver = self
  · have selected' := selected own
    subst receiver
    rw [selected'] at run
    have result := locked_own_call_balances pinned locked funds world run
    exact ⟨result.1.le, result.2⟩
  have foreign : self ≠ receiver := Ne.symm own
  have transfer : EthFrame self accounts (sendEth receiver sender value true accounts) :=
    ⟨(sendEth_world accounts receiver sender value true funds world).le,
      sendEth_protected_balance accounts receiver sender self value true safeSender funds world⟩
  cases code with
  | Precompiled pc =>
    rcases precompiled_call_accounts run with rfl | rfl
    · exact EthFrame.refl self _
    · exact transfer
  | Code bytes =>
    let environment : ExecutionEnv := {
      codeOwner := receiver, sender := origin, source := sender, weiValue := contextValue,
      calldata := calldata, code := bytes, gasPrice := price.toNat, header := header,
      depth := depth, perm := writable, blobVersionedHashes := blobs }
    have storage : CodeStorageFrame self accounts (sendEth receiver sender value true accounts) :=
      sendEth_accountStaticStateEq receiver sender value true accounts self
    have transferred := initial.next storage transfer
    unfold Θ at run
    simp at run
    split at run <;> rename_i execute
    · simp at run
      rcases run with ⟨_, same, _, _, _, _⟩
      rw [← same]
      exact EthFrame.refl self _
    · simp at run
      rcases run with ⟨_, same, _, _, _, _⟩
      rw [← same]
      exact EthFrame.refl self _
    · rename_i finalCreated finalAccounts finalGas finalSubstate returnedData
      simp at run
      rcases run with ⟨_, same, _, _, _, _⟩
      split_ifs at same with empty
      · rw [← same]
        exact EthFrame.refl self _
      · rw [← same]
        have execution : EthFrame self (sendEth receiver sender value true accounts) finalAccounts := by
          apply foreign_xi_balances (env := environment) (cA := cA) (gh := gh) (bl := bl)
            (original := original) (gas := gas) (substate := substate)
            (cA' := finalCreated) (gas' := finalGas) (substate' := finalSubstate)
            (output := returnedData) steps foreign transferred
          simpa [sendEth, environment] using execute
        exact transfer.trans execution

end Rollup.EVM
