import proofs.PrecompileSubstate
import proofs.SurvivalEntry
import proofs.WorldPrecompiles

open Ethereum Ethereum.EVM

namespace Rollup.EVM

private def precompiledRaw (pc : AccountAddress) (accounts : AccountMap) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv) :
    Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × ByteArray :=
  match pc with
  | 1 => (∅, Ξ_ECREC accounts gas substate env)
  | 2 => (∅, Ξ_SHA256 accounts gas substate env)
  | 3 => (∅, Ξ_RIP160 accounts gas substate env)
  | 4 => (∅, Ξ_ID accounts gas substate env)
  | 5 => (∅, Ξ_EXPMOD accounts gas substate env)
  | 6 => (∅, Ξ_BN_ADD accounts gas substate env)
  | 7 => (∅, Ξ_BN_MUL accounts gas substate env)
  | 8 => (∅, Ξ_SNARKV accounts gas substate env)
  | 9 => (∅, Ξ_BLAKE2_F accounts gas substate env)
  | 10 => (∅, Ξ_PointEval accounts gas substate env)
  | _ => default

private theorem precompiled_raw_metadata (pc : AccountAddress) (accounts : AccountMap) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv) :
    (precompiledRaw pc accounts gas substate env).1 = ∅ ∧
      ((precompiledRaw pc accounts gas substate env).2.1 = ∅ ∨
        (precompiledRaw pc accounts gas substate env).2.2.2.1 = substate) := by
  have parts := precompile_substate accounts gas substate env
  unfold precompiledRaw
  repeat' split
  all_goals refine ⟨rfl, ?_⟩
  all_goals first
    | exact .inr parts.1
    | exact .inr parts.2.1
    | exact .inr parts.2.2.1
    | exact .inr parts.2.2.2.1
    | exact .inr parts.2.2.2.2.1
    | exact .inr parts.2.2.2.2.2.1
    | exact .inr parts.2.2.2.2.2.2.1
    | exact .inr parts.2.2.2.2.2.2.2.1
    | exact .inr parts.2.2.2.2.2.2.2.2.1
    | exact .inr parts.2.2.2.2.2.2.2.2.2
    | exact .inl rfl

/-- Precompile calls return an empty created-account set and preserve the input substate. -/
theorem precompiled_call_metadata
    (blobs : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (accounts original : AccountMap)
    (substate : Substate) (sender origin receiver pc : Address) (gas price value contextValue : UInt256)
    (calldata : ByteArray) (depth : Fin 1025) (header : BlockHeader) (writable : Bool) :
    let result := Θ blobs created genesis blocks accounts original substate sender origin receiver
      (.Precompiled pc) gas price value contextValue calldata depth header writable
    result.1 = ∅ ∧ result.2.2.2.1 = substate := by
  let transferred := sendEth receiver sender value true accounts
  let env : ExecutionEnv :=
    { codeOwner := receiver, sender := origin, source := sender, weiValue := contextValue,
      calldata := calldata, code := default, gasPrice := price.toNat, header := header,
      depth := depth, perm := writable, blobVersionedHashes := blobs }
  let result := precompiledRaw pc transferred gas substate env
  have metadata := precompiled_raw_metadata pc transferred gas substate env
  unfold Θ
  simp only
  change result.1 = ∅ ∧ (if result.2.1 == ∅ then substate else result.2.2.2.1) = substate
  refine ⟨metadata.1, ?_⟩
  rcases metadata.2 with empty | same
  · change result.2.1 = ∅ at empty
    rw [empty, rbMap_empty_beq_empty]
    rfl
  · change result.2.2.2.1 = substate at same
    rw [same]
    exact ite_self _

/-- Every modeled precompile preserves the existing rollup's account lifecycle conditions. -/
theorem precompiled_call_survives
    {blobs created genesis blocks accounts original substate sender origin receiver pc gas price value contextValue
      calldata depth header writable nextCreated after remaining nextSubstate accepted output}
    {self : Address} (initial : AccountSurvives self accounts created substate)
    (run : Θ blobs created genesis blocks accounts original substate sender origin receiver (.Precompiled pc)
      gas price value contextValue calldata depth header writable =
        (nextCreated, after, remaining, nextSubstate, accepted, output)) :
    AccountSurvives self after nextCreated nextSubstate := by
  have metadata := precompiled_call_metadata blobs created genesis blocks accounts original substate
    sender origin receiver pc gas price value contextValue calldata depth header writable
  rw [run] at metadata
  dsimp only at metadata
  refine ⟨(accountCodeStateEq_of_precompiled_Theta run self).symm.trans (AccountSurvives.pinned initial), ?_, ?_⟩
  · rw [metadata.1]
    intro member
    rcases (Batteries.RBSet.mem_iff_mem_toList
      (t := (∅ : Batteries.RBSet AccountAddress compare))).mp member with ⟨owner, listed, _⟩
    exact List.not_mem_nil listed
  · rw [metadata.2]
    exact AccountSurvives.notDeleted initial

end Rollup.EVM
