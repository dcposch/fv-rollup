import semantics.SourceResult
import semantics.Environment
import proofs.GetterValues
import proofs.SolmGuards

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

private theorem address_of_word (word : UInt256) :
    AccountAddress.ofNat word.toNat = AccountAddress.ofUInt256 word := by
  apply Fin.ext
  simp [AccountAddress.ofNat, AccountAddress.ofUInt256, UInt256.toNat]

theorem getter_source_nonpayable (getter : Getter)
    (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (values : Option (List Value))
    (run : ExecTransitionBody config contract evm locals
      (entryTransition (.read getter)).body (.returned frame out values)) :
    evm.executionEnv.weiValue = ⟨0⟩ := by
  by_contra nonzero
  have rejected : ExecResult.returned frame out values = .reverted := by
    cases getter <;>
      exact func_only_reverts (fun _ block => require_false_only_reverts
        (evalCallvalueEq_false nonzero) block) run
  cases rejected

theorem getter_model_return (evm : Ethereum.State) (getter : Getter) (keys : AccessScope)
    (accesses : entryKeys (.read getter) ⊆ keys) :
    some [getterValue evm getter] =
      returnValues (readGetter (project evm evm.executionEnv.codeOwner keys) getter) := by
  cases getter with
  | sequencer =>
    have masked := (solcAddressValue_masked
      (readWord evm evm.executionEnv.codeOwner ⟨0⟩)).symm
    change some [Value.address (AccountAddress.ofNat
        (UInt256.land (readWord evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask).toNat)] =
      some [Value.address (AccountAddress.ofUInt256 (readWord evm evm.executionEnv.codeOwner ⟨0⟩))]
    rw [← address_of_word]
    simpa only [u256_land_comm] using
      congrArg (fun value => some [value]) masked
  | stateRoot =>
    simp [getterValue, readGetter, project, returnValues, rootValue,
      toByteArray_eq_toBytesBE, byteArray_toList_eq]
  | batchNumber => rfl
  | backing => rfl
  | pendingDeposits owner =>
    have tracked : StorageKey.pending owner ∈ keys := accesses (by simp [entryKeys])
    simp [getterValue, readGetter, project, returnValues, pendingLedger, tracked]
  | pendingWithdrawals owner =>
    have tracked : StorageKey.claims owner ∈ keys := accesses (by simp [entryKeys])
    simp [getterValue, readGetter, project, returnValues, claimLedger, tracked]

/-- Every accepted source getter has the exact labeled model result. -/
theorem getter_source_refines (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (caller : Address) (value : Nat) (getter : Getter) (values : Option (List Value))
    (keys : AccessScope)
    (bound : CallBound evm locals ⟨caller, value, .read getter⟩)
    (accesses : entryKeys (.read getter) ⊆ keys)
    (code : OwnCode evm) (world : WorldBounded evm)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (run : ExecTransitionBody config contract evm locals
      (entryTransition (.read getter)).body (.returned frame out values)) :
    SourceResult evm out locals frame ⟨caller, value, .read getter⟩ values keys := by
  have nonpayable := getter_source_nonpayable getter evm out locals frame values run
  have zeroNat : evm.executionEnv.weiValue.toNat = 0 := by rw [nonpayable]; rfl
  have valueZero : value = 0 := bound.2.1.trans zeroNat
  subst value
  have args := bound.2.2.2.2
  have binding : entryArgumentStore (.read getter) = some (getterLocals getter) := by
    cases getter <;> rfl
  rw [binding] at args
  have localEq := Option.some.inj args
  subst locals
  have result := (getter_source_exact evm getter nonpayable).2 _ run
  cases result
  refine ⟨ready, unlocked, rfl, code, world,
    readGetter (project evm evm.executionEnv.codeOwner keys) getter, [],
    getter_model_return evm getter keys accesses, ?_, trivial⟩
  simp only [beforeCall, zeroNat, Nat.sub_zero]
  exact CallStep.read _ caller getter

end Rollup.EVM
