import semantics.SourceResult
import semantics.Environment
import proofs.DepositChecks
import proofs.World

open Solm Ethereum Reasoning.Theory

namespace Rollup.EVM

/-- Every accepted deposit source call meets the full source refinement result. -/
theorem deposit_source_refines (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (caller owner : Address) (value : Nat) (values : Option (List Value)) (keys : AccessScope)
    (bound : CallBound evm locals ⟨caller, value, .deposit owner⟩)
    (accesses : entryKeys (.deposit owner) ⊆ keys)
    (code : OwnCode evm) (world : WorldBounded evm)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (funds : evm.executionEnv.weiValue.toNat ≤ (project evm evm.executionEnv.codeOwner keys).eth)
    (run : ExecTransitionBody config contract evm locals (entryTransition (.deposit owner)).body
      (.returned frame out values)) :
    SourceResult evm out locals frame ⟨caller, value, .deposit owner⟩ values keys := by
  have args := bound.2.2.2.2
  change some (depositLocals owner) = some locals at args
  have localEq := Option.some.inj args
  subst locals
  have callerEq := bound.1
  have valueEq := bound.2.1
  change caller = evm.executionEnv.source at callerEq
  change value = evm.executionEnv.weiValue.toNat at valueEq
  subst caller
  subst value
  have ownerKey : StorageKey.pending owner ∈ keys := accesses (by simp [entryKeys])
  have lockKey : StorageKey.fixed 6 ∈ keys := ready.1 (by simp [fixedKeys])
  have separate : keySlot (.pending owner) ≠ ⟨6⟩ := by
    intro same
    have impossible := ready.2.1 (.pending owner) ownerKey (.fixed 6) lockKey same
    cases impossible
  obtain ⟨checks, output, returned⟩ := deposit_success_checks evm out owner frame values separate run
  subst out
  subst values
  have present : ∃ acc, evm.lookupAccount evm.executionEnv.codeOwner = some acc := by
    cases account : evm.lookupAccount evm.executionEnv.codeOwner with
    | none => simp [OwnCode, account] at code
    | some acc => exact ⟨acc, rfl⟩
  obtain ⟨acc, account⟩ := present
  refine ⟨deposit_storage_ready evm owner keys ready ownerKey, ?_, ?_, ?_, ?_, .unit, [], rfl, ?_, trivial⟩
  · have slot := deposit_storage evm owner keys account ready ownerKey checks.1 (.fixed 6) lockKey
    simpa using slot.trans checks.1
  · simp only [depositState, storageStore_executionEnv]
  · unfold depositState
    apply ownCode_store
    apply ownCode_store
    exact ownCode_store _ _ _ _ code
  · unfold depositState
    apply worldBounded_store
    apply worldBounded_store
    exact worldBounded_store _ _ _ _ world
  · rw [deposit_projection evm owner keys account ready ownerKey checks.1 checks.2.2.2.2 funds]
    exact .deposit (deposit_enabled evm owner keys ownerKey checks.2.1 checks.2.2.1
      checks.2.2.2.1 checks.2.2.2.2 funds)

end Rollup.EVM
