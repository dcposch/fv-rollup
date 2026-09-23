import semantics.ExecutionScope
import proofs.RecordedExecution
import proofs.CreationTree

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Actual foreign creation preserves the rollup without an initialization-correctness premise. -/
theorem foreign_creation_refines (call : CreationCall) {self : Address} {keys : AccessScope}
    {address created accounts gas substate accepted output}
    (executed : call.run = (address, created, accounts, gas, substate, accepted, output))
    (ordinary : self ∉ π) (foreign : self ≠ call.sender)
    (ready : BoundaryReady self call.accounts keys) (safe : Safe (boundaryModel self call.accounts keys))
    (nonce : (call.accounts.findD call.sender default).nonce ≠ ⟨0⟩)
    (funds : call.value.toNat ≤ ethLedger call.accounts call.sender)
    (scope : creationExecutionScope call self ⊆ keys) :
    BoundaryRefines self keys call.accounts accounts := by
  apply creation_execution_refines call executed ready safe foreign nonce funds
  intro fresh
  have receiver := creation_fresh_foreign call (BoundaryReady.pinned ready) fresh
  have different := creation_fresh_not_sender call nonce fresh
  have transfer := boundary_creation_transfer_refines self call.sender call.address call.accounts call.value keys
    ready safe foreign different funds
  exact foreign_execution_refines _ _ call.entryState self keys ordinary receiver
    transfer.1 transfer.2.1 scope

end Rollup.EVM
