import proofs.Calls
import proofs.SourceRefinement

namespace Rollup.EVM

/-- Every accepted source call preserves custody. -/
theorem source_custody
    (evm out : Ethereum.State) (locals : Solm.Store) (frame : Solm.Frame)
    (call : Call) (values : Option (List Solm.Value)) (keys : AccessScope)
    (bound : CallBound evm locals call)
    (accesses : entryKeys call.entry ⊆ keys)
    (code : OwnCode evm)
    (world : WorldBounded evm)
    (storage : StorageReady evm evm.executionEnv.codeOwner keys)
    (unlocked : readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩)
    (funds : evm.executionEnv.weiValue.toNat ≤ (project evm evm.executionEnv.codeOwner keys).eth)
    (safe : Safe (beforeCall evm keys))
    (run : Solm.ExecTransitionBody config contract evm locals (entryTransition call.entry).body
      (.returned frame out values)) :
    liabilities (project out evm.executionEnv.codeOwner keys) ≤
      (project out evm.executionEnv.codeOwner keys).eth := by
  obtain ⟨_, _, _, _, _, result, payments, _, step, _⟩ :=
    source_refines_model evm out locals frame call values keys bound accesses code world storage unlocked funds safe run
  have solv := (callStep_safe safe step).1
  simpa [Solvent, reserved, project] using solv

end Rollup.EVM
