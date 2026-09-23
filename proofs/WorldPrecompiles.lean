import proofs.WorldTransfers
import Ethereum.Theory.StaticStorage

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private theorem final_accounts_cases {before transferred result : AccountMap}
    (cases : result = ∅ ∨ result = transferred) :
    (if result == ∅ then before else result) = before ∨
      (if result == ∅ then before else result) = transferred := by
  rcases cases with rfl | rfl
  · simp [rbMap_empty_beq_empty]
  · split
    · exact .inl rfl
    · exact .inr rfl

/-- A precompile call either rolls back or keeps only the incoming transfer. -/
theorem precompiled_call_accounts
    {blobs cA gh bl accounts original substate sender origin receiver pc gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (run : Θ blobs cA gh bl accounts original substate sender origin receiver (.Precompiled pc)
      gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    after = accounts ∨ after = sendEth receiver sender value true accounts := by
  let transferred := sendEth receiver sender value true accounts
  let environment : ExecutionEnv := {
    codeOwner := receiver, sender := origin, source := sender, weiValue := contextValue,
    calldata := calldata, code := default, gasPrice := price.toNat, header := header,
    depth := depth, perm := writable, blobVersionedHashes := blobs }
  have projection := congrArg (fun result => result.2.1) run
  change (Θ blobs cA gh bl accounts original substate sender origin receiver (.Precompiled pc)
    gas price value contextValue calldata depth header writable).2.1 = after at projection
  rw [← projection, precompiled_Theta_accountMap_eq]
  exact final_accounts_cases
    (precompiled_result_accountMap_empty_or_self pc transferred gas substate environment)

/-- A funded precompile call conserves total ETH. -/
theorem precompiled_call_world
    {blobs cA gh bl accounts original substate sender origin receiver pc gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit)
    (run : Θ blobs cA gh bl accounts original substate sender origin receiver (.Precompiled pc)
      gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    worldEth after = worldEth accounts := by
  rcases precompiled_call_accounts run with rfl | rfl
  · rfl
  · exact sendEth_world accounts receiver sender value true funds world

/-- A funded precompile call cannot debit a different account. -/
theorem precompiled_call_other_balance
    {blobs cA gh bl accounts original substate sender origin receiver pc gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (self : Address) (different : self ≠ sender)
    (funds : value.toNat ≤ ethLedger accounts sender)
    (world : worldEth accounts < wordLimit)
    (run : Θ blobs cA gh bl accounts original substate sender origin receiver (.Precompiled pc)
      gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    ethLedger accounts self ≤ ethLedger after self := by
  rcases precompiled_call_accounts run with rfl | rfl
  · exact Nat.le_refl _
  · exact sendEth_other_balance accounts receiver sender self value true different funds world

end Rollup.EVM
