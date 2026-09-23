import proofs.WorldMessageCalls

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- The call helper uses a funded sender and the selected storage context. -/
theorem call_helper_balances
    {self : Address} {before after : Ethereum.State}
    {gasCost : Nat} {blobs : List ByteArray}
    {gas source recipient target value contextValue inOffset inSize outOffset outSize result : UInt256}
    {permission : Bool}
    (calls : ProtectedCallBalances self (before.executionEnv.depth + 1))
    (foreign : self ≠ before.executionEnv.codeOwner)
    (sourceBound : AccountAddress.ofUInt256 source = before.executionEnv.codeOwner ∨ value = ⟨0⟩)
    (selected : AccountAddress.ofUInt256 recipient = self → AccountAddress.ofUInt256 target = self)
    (initial : LockedWorld self before.accountMap)
    (run : call gasCost blobs gas source recipient target value contextValue
      inOffset inSize outOffset outSize permission before = .ok (result, after)) :
    EthFrame self before.accountMap after.accountMap := by
  let outcome := Θ blobs before.createdAccounts before.genesisBlockHeader before.blocks
    before.accountMap before.σ₀ (before.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
    (AccountAddress.ofUInt256 source) before.executionEnv.sender (AccountAddress.ofUInt256 recipient)
    (toExecute before.accountMap (AccountAddress.ofUInt256 target))
    (.ofNat (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value gas before.accountMap before.machineState before.substate))
    (.ofNat before.executionEnv.gasPrice) value contextValue
    (before.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
    (before.executionEnv.depth + 1) before.executionEnv.header permission
  unfold call at run
  simp at run
  split at run
  · rename_i allowed
    rcases run with ⟨_, same⟩
    rw [← same]
    change EthFrame self before.accountMap outcome.2.1
    apply calls blobs before.createdAccounts before.genesisBlockHeader before.blocks
      before.accountMap before.σ₀ _ _ _ _ _ _ _ _ _ _ _ _
      outcome.1 outcome.2.1 outcome.2.2.1 outcome.2.2.2.1 outcome.2.2.2.2.1 outcome.2.2.2.2.2
      _ _ _ initial rfl
    · intro receiver
      rw [selected receiver]
    · rcases sourceBound with sameSource | zero
      · exact .inl (by simpa [sameSource] using foreign)
      · exact .inr zero
    · rcases sourceBound with sameSource | zero
      · rw [sameSource, ethLedger_lookup]
        have enough := allowed.1
        change value.toNat ≤ (Option.option (⟨0⟩ : UInt256) (fun (x : Account) => x.balance)
          (before.accountMap.find? before.executionEnv.codeOwner)).toNat at enough
        cases found : before.accountMap.find? before.executionEnv.codeOwner <;>
          simpa [found, Option.option, UInt256.toNat] using enough
      · simp [zero, UInt256.toNat]
  · rcases run with ⟨_, same⟩
    rw [← same]
    exact EthFrame.refl self before.accountMap

/-- All four call opcodes bind the transfer source and storage context correctly. -/
theorem call_step_balances {self : Address} {before after : Ethereum.State}
    {gasCost : Nat} {op : Operation} {arg : Option (UInt256 × Nat)}
    (kind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (calls : ProtectedCallBalances self (before.executionEnv.depth + 1))
    (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (run : step gasCost (op, arg) before = .ok after) :
    EthFrame self before.accountMap after.accountMap := by
  rcases kind with rfl | rfl | rfl | rfl
  all_goals
    simp [step, bind, Except.bind] at run
    split at run <;> try contradiction
    rename_i popped pop
    split at run <;> try contradiction
    rename_i outcome execute
    rcases outcome with ⟨result, during⟩
    have same := Except.ok.inj run
    rw [← same]
    change EthFrame self before.accountMap during.accountMap
    apply call_helper_balances
      (before := { before with machineState.execLength := before.machineState.execLength + 1 })
      calls foreign _ _ initial execute
  all_goals try simp only [AccountAddress.ofUInt256_ofNat]
  all_goals first
    | exact Or.inl True.intro
    | exact Or.inr True.intro
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact fun h => h
    | intro h; exact (foreign h.symm).elim

end Rollup.EVM
