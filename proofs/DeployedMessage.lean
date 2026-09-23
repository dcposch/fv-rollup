import proofs.DeploymentBoundary
import proofs.MessageRefinement

open Ethereum Ethereum.EVM Solm Reasoning.Theory

namespace Rollup.EVM

/-- The first accepted message starts from the model established by actual deployment. -/
theorem deployed_message_refines_model
    (d : Deployment) (sequencer : Address) (root : Root)
    (call : MessageCall) (locals : Store) (label : Call) (keys : AccessScope)
    (fixed : fixedKeys ⊆ keys) (distinct : NoAlias keys)
    (nonzero : sequencer ≠ 0)
    (fresh : d.fresh (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩))
    (present : (d.accounts.find? d.sender).isSome)
    (world : worldEth d.accounts < wordLimit)
    {deploymentCreated deploymentGas deploymentSubstate deploymentData}
    (deployed : d.run (creationBytecode ++ creationArgs (UInt256.ofNat sequencer.val) ⟨root⟩) =
      (call.receiver, deploymentCreated, call.accounts, deploymentGas, deploymentSubstate, true, deploymentData))
    (ordinary : call.receiver ∉ π) (different : call.receiver ≠ call.sender)
    (value : call.contextValue = call.value)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (bounded : call.calldata.size < UInt256.size)
    (bound : CallBound call.entryState locals label)
    (accesses : entryKeys label.entry ⊆ keys)
    {created accounts gas substate output}
    (run : call.selectedRun = (created, accounts, gas, substate, true, output)) :
    BoundaryReady call.receiver accounts keys ∧ Safe (boundaryModel call.receiver accounts keys) ∧
      ∃ result payments,
        CallStep (initial call.receiver sequencer root (ethLedger d.accounts call.receiver))
          label (.success result) payments (boundaryModel call.receiver accounts keys) ∧
        returnDataEquiv output (returnValues result) (.abi (entryTransition label.entry).returnType) := by
  obtain ⟨ready, model, safe⟩ := deployment_refines_scope d sequencer root keys fixed distinct
    nonzero fresh present world deployed
  obtain ⟨nextReady, result, payments, step, returned⟩ := message_refines_model call locals label keys
    ready safe ordinary different value funds bounded bound accesses run
  refine ⟨nextReady, callStep_safe safe step, result, payments, ?_, returned⟩
  rwa [model] at step

end Rollup.EVM
