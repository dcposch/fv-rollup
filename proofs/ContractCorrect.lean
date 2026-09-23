import invariants.ContractCorrect
import proofs.TransactionRootRefinement
import proofs.TransactionPaymentSafety
import proofs.TransactionPaymentStorage
import proofs.TransactionSequence

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Actual root invocations and their receiver trees satisfy the contract claims. -/
theorem transaction_observations_correct {event self keys}
    (ordinary : self ∉ π) (admissible : event.admissible self)
    (ready : BoundaryReady self event.before keys) (safe : Safe (boundaryModel self event.before keys)) :
    TransactionObservationsCorrect event self keys := by
  intro start root entry path
  refine ⟨transaction_root_message_refined entry path admissible ordinary ready safe, ?_⟩
  intro cursor child current earlier entered active
  exact ⟨transaction_payment_storage entry path admissible ordinary ready safe earlier entered active,
    transaction_payment_safe entry path admissible ordinary ready safe earlier entered active⟩

/-- Pinned deployment and arbitrary admissible transactions establish all boundary and observation claims. -/
theorem deployed_contract_correct : DeployedContractCorrect := by
  intro deployment sequencer root keys self created accounts gas substate data events after
    fixed distinct nonzero fresh present world ordinary deployed trace covered
  have bounded := (worldBounded_iff_worldEth (accountView self deployment.accounts)).mp world
  obtain ⟨ready, model, safe⟩ := deployment_refines_scope deployment sequencer root keys
    fixed distinct nonzero fresh present bounded deployed
  have effect := transaction_sequence_refines ordinary ready safe trace covered
  refine ⟨effect.1, effect.2.1, ?_, ?_⟩
  · have committed := effect.2.2
    rw [model] at committed
    exact committed
  · intro event before admissible
    apply transaction_observations_correct ordinary admissible
    · rw [before]
      exact effect.1
    · rw [before]
      exact effect.2.1

end Rollup.EVM
