import proofs.ContractCorrect
import proofs.RuntimeEquivalence
import proofs.Constructor
import proofs.SourceRefinement

namespace Rollup.EVM

/-- The completion gate requires each final theorem at its stated type. -/
theorem contract_verification_complete :
    BytecodeCorrect ∧ ConstructorInitializes ∧ SourceRefinesModel ∧ DeployedContractCorrect :=
  ⟨bytecode_correct, constructor_initializes, source_refines_model, deployed_contract_correct⟩

end Rollup.EVM
