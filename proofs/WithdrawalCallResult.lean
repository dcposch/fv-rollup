import proofs.WithdrawalPaymentBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Keep the source call result for successful and failed EVM payments. -/
theorem withdrawal_call_result {g : Sat256} {s0 : Ethereum.State}
    (before : Ethereum.State) {mem rdata : ByteArray} {k C : Nat}
    (gasArg credit amount : UInt256) (owner : Address) (rest : List UInt256)
    (space : rest.length + 16 ≤ 1024)
    (writable : before.executionEnv.perm = true)
    (original : before.σ₀ = s0.σ₀)
    (genesis : before.genesisBlockHeader = s0.genesisBlockHeader)
    (blocks : before.blocks = s0.blocks)
    (reached : RD runtimeBytecode before.executionEnv g s0 ⟨935⟩
      (gasArg :: UInt256.ofNat owner.val :: amount :: ⟨128⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨128⟩ :: amount :: UInt256.ofNat owner.val :: ⟨0⟩ :: credit :: amount ::
        UInt256.ofNat owner.val :: rest)
      mem (UInt256.ofNat 3) rdata (before.createdAccounts, before.accountMap) k C) :
    ∃ paid after data k' C',
      callViaEVM before owner (Int.ofNat amount.toNat) ByteArray.empty (paid, after, data) ∧
      after.executionEnv = before.executionEnv ∧
      RD runtimeBytecode before.executionEnv g s0 ⟨936⟩
        ((if paid then ⟨1⟩ else ⟨0⟩) :: ⟨128⟩ :: amount :: UInt256.ofNat owner.val :: ⟨0⟩ ::
          credit :: amount :: UInt256.ofNat owner.val :: rest)
        mem (UInt256.ofNat 3) data (after.createdAccounts, after.accountMap) k' C' := by
  by_cases depth : before.executionEnv.depth = 1024
  · obtain ⟨_, _, returned⟩ := reached.callValueDepthLimitEmptyInOut writable
      (by decide +kernel) depth (by simp; omega)
    let after := { before with substate := (before.addAccessedAccount owner).substate }
    have call : callViaEVM before owner (Int.ofNat amount.toNat) ByteArray.empty
        (false, after, ByteArray.empty) := .callNotMade rfl rfl (by
      rintro ⟨_, notFull⟩
      exact notFull depth)
    exact ⟨false, after, ByteArray.empty, _, _, call, rfl, returned⟩
  · have depthBound : before.executionEnv.depth.val < 1024 := by
      have bound := before.executionEnv.depth.isLt
      have ne : before.executionEnv.depth.val ≠ 1024 := by
        intro same
        apply depth
        exact Fin.ext same
      omega
    by_cases balance : amount ≤ (before.accountMap.find? before.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
    · obtain ⟨cA', σ', paid, data, inputSubstate, callGas, _, _, call, returned⟩ :=
        runtime_call_value_made_empty reached (by decide +kernel) writable balance depthBound (by simp; omega)
      obtain ⟨returnedGas, outputSubstate, call⟩ := call
      rw [accountAddress_roundtrip, accountAddress_roundtrip, writable,
        ← original, ← genesis, ← blocks] at call
      let after := { before with accountMap := σ', substate := outputSubstate, createdAccounts := cA' }
      have source : callViaEVM before owner (Int.ofNat amount.toNat) ByteArray.empty
          (paid, after, data) := .callMade (wordOfInt_ofNat_toNat amount).symm
        ⟨callGas, inputSubstate, call⟩ rfl balance depth
      exact ⟨paid, after, data, _, _, source, rfl, returned⟩
    · obtain ⟨_, _, returned⟩ := reached.callValueInsufficientBalanceEmptyInOut writable
        (by decide +kernel) balance depthBound (by simp; omega)
      let after := { before with substate := (before.addAccessedAccount owner).substate }
      have call : callViaEVM before owner (Int.ofNat amount.toNat) ByteArray.empty
          (false, after, ByteArray.empty) := .callNotMade rfl rfl (by
        rintro ⟨covered, _⟩
        rw [wordOfInt_ofNat_toNat] at covered
        exact balance covered)
      exact ⟨false, after, ByteArray.empty, _, _, call, rfl, returned⟩

end Rollup.EVM
