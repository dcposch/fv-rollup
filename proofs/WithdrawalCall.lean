import proofs.WithdrawalPostlude
import proofs.RuntimeCall

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- The EVM made a successful ETH call to the specified owner and amount. -/
def WithdrawalPaymentWitness (s0 : Ethereum.State) (I : ExecutionEnv)
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
    (owner amount : UInt256) (cA' : Batteries.RBSet AccountAddress compare)
    (σ' : AccountMap) (data : ByteArray) : Prop :=
  amount ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth.val < 1024 ∧
    ∃ (inputSubstate : Substate) (callGas returnedGas : UInt256) (outputSubstate : Substate),
      (cA', σ', returnedGas, outputSubstate, true, data) =
        Θ I.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ inputSubstate
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 owner) (toExecute σ (AccountAddress.ofUInt256 owner))
          callGas (UInt256.ofNat I.gasPrice) amount amount ByteArray.empty
          (I.depth + 1) I.header I.perm

private theorem failed_payment_reject {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (credit amount owner : UInt256) (rest : List UInt256) (space : rest.length + 16 ≤ 1024)
    (memorySize : mem.size = 96)
    (freePointer : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (reached : RD runtimeBytecode I g s0 ⟨936⟩
      (⟨0⟩ :: ⟨128⟩ :: amount :: owner :: ⟨0⟩ :: credit :: amount :: owner :: rest)
      mem (UInt256.ofNat 3) rdata acc k C) : RDrev runtimeBytecode g s0 := by
  obtain ⟨_, _, _, _, checkedData⟩ := withdrawal_bytecode_return_data ⟨0⟩ credit amount owner rest
    space memorySize freePointer reached
  rcases withdrawal_bytecode_payment_check ⟨0⟩ credit amount owner rest (by omega) checkedData with
    ⟨rejected, _⟩ | ⟨nonzero, _⟩
  · exact rejected
  · exact False.elim (nonzero rfl)

/-- A withdrawal rejects, or the actual CALL gives a successful payment witness. -/
theorem withdrawal_bytecode_call {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (gasArg credit amount owner : UInt256) (rest : List UInt256) (space : rest.length + 16 ≤ 1024)
    (writable : I.perm = true)
    (memorySize : mem.size = 96)
    (freePointer : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (reached : RD runtimeBytecode I g s0 ⟨935⟩
      (gasArg :: owner :: amount :: ⟨128⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨128⟩ :: amount :: owner :: ⟨0⟩ :: credit :: amount :: owner :: rest)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev runtimeBytecode g s0 ∨
      ∃ cA' σ' data mem' aw' k' C',
        WithdrawalPaymentWitness s0 I cA σ owner amount cA' σ' data ∧
        RD runtimeBytecode I g s0 ⟨999⟩ (⟨1⟩ :: credit :: amount :: owner :: rest)
          mem' aw' data (cA', σ') k' C' := by
  by_cases depth : I.depth = 1024
  · obtain ⟨_, _, returned⟩ := reached.callValueDepthLimitEmptyInOut writable
      (by decide +kernel) depth (by simp; omega)
    exact .inl (failed_payment_reject credit amount owner rest space memorySize freePointer returned)
  · have depthBound : I.depth.val < 1024 := by
      have bound := I.depth.isLt
      have ne : I.depth.val ≠ 1024 := by
        intro same
        apply depth
        apply Fin.ext
        exact same
      omega
    by_cases balance : amount ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
    · obtain ⟨cA', σ', paid, data, inputSubstate, callGas, _, _, call, returned⟩ :=
        runtime_call_value_made_empty reached (by decide +kernel) writable balance depthBound (by simp; omega)
      cases paid
      · exact .inl (failed_payment_reject credit amount owner rest space memorySize freePointer returned)
      · obtain ⟨_, _, _, _, checkedData⟩ := withdrawal_bytecode_return_data ⟨1⟩ credit amount owner rest
          space memorySize freePointer returned
        rcases withdrawal_bytecode_payment_check ⟨1⟩ credit amount owner rest (by omega) checkedData with
          ⟨_, zero⟩ | ⟨_, _, _, checkedPayment⟩
        · exact False.elim (by cases zero)
        · obtain ⟨returnedGas, outputSubstate, call⟩ := call
          exact .inr ⟨cA', σ', data, _, _, _, _,
            ⟨balance, depthBound, inputSubstate, callGas, returnedGas, outputSubstate, call⟩,
            checkedPayment⟩
    · obtain ⟨_, _, returned⟩ := reached.callValueInsufficientBalanceEmptyInOut writable
        (by decide +kernel) balance depthBound (by simp; omega)
      exact .inl (failed_payment_reject credit amount owner rest space memorySize freePointer returned)

end Rollup.EVM
