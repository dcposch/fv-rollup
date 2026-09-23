import proofs.RuntimeSuccess
import proofs.SourceRefinement

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Accepted bytecode has a matching source call and equivalent output accounts. -/
theorem runtime_accepted_source {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output} (locals : Store) (call : Call)
    (code : I.code = runtimeBytecode)
    (bounded : I.calldata.size < UInt256.size)
    (bound : CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) locals call)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    ∃ frame out values,
      ExecTransitionBody config contract (initState cA gh bl σ σ₀ (.ofUInt256 g) A I)
        locals (entryTransition call.entry).body (.returned frame out values) ∧
      accountMapEquiv σ' out.accountMap ∧
      returnDataEquiv output values (.abi (entryTransition call.entry).returnType) := by
  have dispatchedCall : selectorDispatchMsg contract I.calldata = some (entryTransition call.entry) :=
    bound.2.2.1
  have decodedCall : ABI.decodeCalldataWithMode config.abiDecodeMode
      ((entryTransition call.entry).params.map Param.name)
      (transitionSignature (entryTransition call.entry)).paramTypes I.calldata = some locals :=
    bound.2.2.2.1
  have equivalent : runtimeEquivalenceFor config contract cA gh bl σ σ σ₀ g A I :=
    runtime_success_equivalence_for code bounded (accountMapEquiv.refl σ) success
  cases equivalent with
  | noDispatch missing rejected => rw [success] at rejected; cases rejected
  | decodingFailed dispatched signature failed rejected => rw [success] at rejected; cases rejected
  | outOfGas rejected => rw [success] at rejected; cases rejected
  | execution execution source related =>
    rw [success] at execution
    cases execution
    cases related with
    | revert rejected result => cases rejected
    | invalidHalt rejected result => cases rejected
    | success accepted result created maps returned =>
      cases accepted
      cases result
      cases source with
      | intro dispatched signature decoded state body =>
        rw [dispatchedCall] at dispatched
        cases dispatched
        subst_vars
        rw [decodedCall] at decoded
        cases decoded
        exact ⟨_, _, _, body, maps, returned⟩
      | fallback dispatched receiveMissing fallback args convention state body =>
        rw [dispatchedCall] at dispatched
        cases dispatched
      | receive dispatched args returnType state body =>
        simp [receiveDispatchMsg, contract] at dispatched

end Rollup.EVM
