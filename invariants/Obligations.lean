import invariants.Invariants
import semantics.SourceResult
import semantics.Payments
import semantics.Bytecode
import Solm.Equiv

namespace Rollup.EVM

/-- Proved in proofs/RuntimeEquivalence. Static calls and model refinement remain separate. -/
def BytecodeCorrect : Prop :=
  Solm.contractEquivalence config creationBytecode runtimeBytecode contract

/-- Constructor storage starts at zero. Proved in proofs/Constructor.lean. -/
def ConstructorInitializes : Prop :=
  ∀ (evm out : Ethereum.State) (locals : Solm.Store) (frame : Solm.Frame)
    (sequencer : Address) (root : Root),
    Solm.bindParams? contract.ctor.params [.address sequencer, rootValue root] = some locals →
    (evm.lookupAccount evm.executionEnv.codeOwner).isSome →
    (∀ slot, readWord evm evm.executionEnv.codeOwner slot = ⟨0⟩) →
    Solm.ExecTransitionBody config contract evm locals contract.ctor.body (.returned frame out none) →
    sequencer ≠ 0 ∧
    project out evm.executionEnv.codeOwner fixedKeys =
      initial evm.executionEnv.codeOwner sequencer root
        (project evm evm.executionEnv.codeOwner fixedKeys).eth ∧
    StorageReady out evm.executionEnv.codeOwner fixedKeys ∧
    readWord out evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ ∧
    out.executionEnv = evm.executionEnv

/-- All accepted source calls have the exact labeled model effect.
    Proved in proofs/SourceRefinement.lean. -/
def SourceRefinesModel : Prop :=
  ∀ (evm out : Ethereum.State) (locals : Solm.Store) (frame : Solm.Frame)
    (call : Call) (values : Option (List Solm.Value)) (keys : AccessScope),
    CallBound evm locals call →
    entryKeys call.entry ⊆ keys →
    OwnCode evm →
    WorldBounded evm →
    StorageReady evm evm.executionEnv.codeOwner keys →
    readWord evm evm.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ →
    evm.executionEnv.weiValue.toNat ≤ (project evm evm.executionEnv.codeOwner keys).eth →
    Safe (beforeCall evm keys) →
    Solm.ExecTransitionBody config contract evm locals (entryTransition call.entry).body
      (.returned frame out values) →
    SourceResult evm out locals frame call values keys

end Rollup.EVM
