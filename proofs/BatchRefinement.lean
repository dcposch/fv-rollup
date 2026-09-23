import proofs.BatchProjection

open Solm Ethereum Reasoning.Theory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- An accepted source batch implements its exact labeled model transition. -/
theorem batch_source_refines (evm out : Ethereum.State) (locals : Store) (frame : Frame)
    (caller : Address) (value : Nat) (batch : Batch) (values : Option (List Value)) (keys : AccessScope)
    (bound : CallBound evm locals ⟨caller, value, .executeBatch batch⟩)
    (accesses : entryKeys (.executeBatch batch) ⊆ keys)
    (code : OwnCode evm) (world : WorldBounded evm)
    (ready : StorageReady evm evm.executionEnv.codeOwner keys)
    (run : ExecTransitionBody config contract evm locals (entryTransition (.executeBatch batch)).body
      (.returned frame out values)) :
    SourceResult evm out locals frame ⟨caller, value, .executeBatch batch⟩ values keys := by
  have binding : entryArgumentStore (.executeBatch batch) = some (batchLocals batch) := rfl
  have args := bound.2.2.2.2
  rw [binding] at args
  have sameLocals := Option.some.inj args
  subst locals
  have pendingKey : StorageKey.pending batch.depositOwner ∈ keys := accesses (by simp [entryKeys])
  have claimsKey : StorageKey.claims batch.withdrawalOwner ∈ keys := accesses (by simp [entryKeys])
  have present : ∃ account, evm.lookupAccount evm.executionEnv.codeOwner = some account := by
    cases found : evm.lookupAccount evm.executionEnv.codeOwner with
    | none => simp [OwnCode, found] at code
    | some account => exact ⟨account, rfl⟩
  have authorized := batch_source_call_authorized evm out (batchLocals batch) frame values
    caller value batch keys bound run
  have zero := (batch_source_authorized evm out (batchLocals batch) frame values
    (by simp [batchLocals]) (by simp [batchLocals]) run).1
  have continuity := batch_source_continuity evm out batch frame values run
  have owners := batch_source_after_owners evm out batch frame values keys run
  have consumed := (batch_source_after_deposit evm out batch frame values keys run).1
  have backing := batch_source_after_backing evm out batch frame values keys run
  have credit := (batch_source_after_claims evm out batch frame values keys run).1
  have reads := batch_read_values evm batch keys ready pendingKey claimsKey
  have enabled : BatchEnabled (project evm evm.executionEnv.codeOwner keys) caller batch := by
    refine ⟨rfl, authorized.1, continuity.1, continuity.2.1, continuity.2.2,
      owners.1, owners.2.1, ?_, ?_, ?_, ?_⟩
    · rwa [reads.1] at consumed
    · simpa only [reads.2.1] using backing.1
    · rw [← reads.2.1]
      exact backing.2.1
    · rwa [reads.2.2] at credit
  have state := batch_source_exact evm out batch frame values keys run
  have before : beforeCall evm keys = project evm evm.executionEnv.codeOwner keys := by
    simp [beforeCall, zero]
  have valueZero := authorized.2
  subst value
  obtain ⟨outputEq, _, valuesEq⟩ := state
  subst out
  subst values
  have tracked := batch_writes_tracked evm batch keys ready.1 pendingKey claimsKey
  refine ⟨?_, ?_, ?_, ?_, ?_, .unit, [], rfl, ?_, trivial⟩
  · rw [batch_execution_writes]
    exact storeKeys_ready evm _ _ keys ready tracked
  · have lock := batch_storage evm batch keys present ready pendingKey claimsKey (.fixed 6)
      (ready.1 (by simp [fixedKeys]))
    simpa using lock
  · rw [batch_execution_writes]
    exact storeKeys_environment evm _ _
  · rw [batch_execution_writes]
    exact storeKeys_ownCode evm _ _ code
  · rw [batch_execution_writes]
    exact storeKeys_worldBounded evm _ _ world
  · rw [before, batch_projection evm batch keys present ready pendingKey claimsKey
      continuity.2.1 backing.1 credit]
    exact CallStep.batch enabled

end Rollup.EVM
