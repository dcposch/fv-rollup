import proofs.CreationCall
import proofs.BoundaryTransfer
import proofs.WorldStorage

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- Rejected creation restores the input accounts, including failed code checks. -/
theorem creation_call_rejected (call : CreationCall)
    {address created accounts gas substate output}
    (run : call.run = (address, created, accounts, gas, substate, false, output)) :
    accounts = call.accounts := by
  unfold CreationCall.run Lambda at run
  simp at run
  split at run
  · exact (congrArg (fun result => result.2.2.1) run).symm
  · exact (congrArg (fun result => result.2.2.1) run).symm
  · have same := congrArg (fun result => result.2.2.1) run
    have rejected := congrArg (fun result => result.2.2.2.2.2.1) run
    dsimp only at same rejected
    split_ifs at same with failed
    · exact same.symm
    · simp at failed rejected
      tauto

/-- Accepted creation installs the bytes returned by initialization. -/
theorem creation_call_installed (call : CreationCall)
    {address created accounts gas substate output initCreated initAccounts initGas initSubstate returned}
    (execution : call.execute = .ok (.success (initCreated, initAccounts, initGas, initSubstate) returned))
    (run : call.run = (address, created, accounts, gas, substate, true, output)) :
    accounts = initAccounts.insert call.address
      { initAccounts.findD call.address default with code := returned } := by
  unfold CreationCall.execute CreationCall.initialCreated CreationCall.initialAccounts
    CreationCall.environment CreationCall.collision CreationCall.address Deployment.address at execution
  unfold CreationCall.run Lambda at run
  dsimp only at execution run
  simp only [apply_ite] at execution run
  erw [execution] at run
  have same := congrArg (fun result => result.2.2.1) run
  have accepted := congrArg (fun result => result.2.2.2.2.2.1) run
  dsimp only at same accepted
  split_ifs at same with failed
  · rw [failed] at accepted
    cases accepted
  · exact same.symm

/-- Code installation at another address preserves the rollup boundary. -/
theorem boundary_foreign_code_refines (self owner : Address) (accounts : AccountMap)
    (code : ByteArray) (keys : AccessScope) (foreign : self ≠ owner)
    (ready : BoundaryReady self accounts keys) (safe : Safe (boundaryModel self accounts keys)) :
    BoundaryRefines self keys accounts
      (accounts.insert owner { accounts.findD owner default with code := code }) := by
  apply boundary_frame_refines ready safe
  · unfold CodeStorageFrame
    simp only [Batteries.RBMap.findD, accountMap_find?_insert_ne _ _ _ _ foreign]
    exact ⟨True.intro, True.intro, True.intro⟩
  · have same := ethLedger_insert_same_balance accounts owner
      { accounts.findD owner default with code := code } rfl
    simp only [EthFrame, worldEth, same, le_refl, and_self]

end Rollup.EVM
