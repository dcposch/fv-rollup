import proofs.WorldNonce

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Rollup.EVM

/-- Both creation opcodes use the checked nonce and funded endowment. -/
theorem creation_step_balances {self : Address} {before after : Ethereum.State}
    {gasCost : Nat} {op : Operation} {arg : Option (UInt256 × Nat)}
    (kind : op = .CREATE ∨ op = .CREATE2)
    (creates : ∀ depth : Fin 1025, depth.val = before.executionEnv.depth.val + 1 →
      ProtectedCreationBalances self depth)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (initial : LockedWorld self before.accountMap)
    (run : step gasCost (op, arg) before = .ok after) :
    EthFrame self before.accountMap after.accountMap := by
  rcases kind with rfl | rfl
  all_goals simp only [step] at run
  all_goals split at run <;> try contradiction
  all_goals first
    | (rename_i stack value offset size salt pop
       guard_hyp value : UInt256
       let creationSalt : Option ByteArray := some (UInt256.toByteArray salt))
    | (rename_i stack value offset size pop
       let creationSalt : Option ByteArray := none)
  all_goals
    by_cases limit : ((before.accountMap.find? before.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2 ^ 64 - 1
    · simp at run
      repeat' first | split at run | contradiction
      all_goals
        have same := Except.ok.inj run
        rw [← same]
        exact EthFrame.refl self before.accountMap
    · by_cases allowed : value ≤ Option.option (⟨0⟩ : UInt256) (fun (x : Account) => x.balance)
          (before.accountMap.find? before.executionEnv.codeOwner) ∧
          before.executionEnv.depth < 1024 ∧
          (before.machineState.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152
      · let nextDepth : Fin 1025 := ⟨before.executionEnv.depth.val + 1, Nat.succ_lt_succ allowed.2.1⟩
        let accounts := incrementNonce before.accountMap before.executionEnv.codeOwner
        let outcome := Lambda before.executionEnv.blobVersionedHashes before.createdAccounts
          before.genesisBlockHeader before.blocks accounts before.σ₀ before.substate
          before.executionEnv.codeOwner before.executionEnv.sender
          (.ofNat (L (before.machineState.gasAvailable.subNat gasCost).toNat))
          (.ofNat before.executionEnv.gasPrice) value
          (before.machineState.memory.readWithPadding offset.toNat size.toNat) nextDepth creationSalt
          before.executionEnv.header before.executionEnv.perm
        have next := incrementNonce_lockedWorld (sender := before.executionEnv.codeOwner) initial
        have ledger := incrementNonce_ethLedger before.accountMap before.executionEnv.codeOwner
        have nonce := incrementNonce_nonzero before.accountMap before.executionEnv.codeOwner
          (Nat.lt_of_not_ge limit)
        have funds : value.toNat ≤ ethLedger accounts before.executionEnv.codeOwner := by
          rw [show accounts = incrementNonce before.accountMap before.executionEnv.codeOwner from rfl,
            ledger, ethLedger_lookup]
          have enough := allowed.1
          change value.toNat ≤ (Option.option (⟨0⟩ : UInt256) (fun (x : Account) => x.balance)
            (before.accountMap.find? before.executionEnv.codeOwner)).toNat at enough
          cases found : before.accountMap.find? before.executionEnv.codeOwner <;>
            simpa [found, Option.option, UInt256.toNat] using enough
        have balances := creates nextDepth rfl before.executionEnv.blobVersionedHashes before.createdAccounts
          before.genesisBlockHeader before.blocks accounts before.σ₀ before.substate
          before.executionEnv.codeOwner before.executionEnv.sender
          (.ofNat (L (before.machineState.gasAvailable.subNat gasCost).toNat))
          (.ofNat before.executionEnv.gasPrice) value
          (before.machineState.memory.readWithPadding offset.toNat size.toNat) creationSalt
          before.executionEnv.header before.executionEnv.perm
          outcome.1 outcome.2.1 outcome.2.2.1 outcome.2.2.2.1 outcome.2.2.2.2.1
          outcome.2.2.2.2.2.1 outcome.2.2.2.2.2.2 foreign nonce funds next rfl
        simp [allowed] at run
        repeat' first | split at run | contradiction
        all_goals
          have same := Except.ok.inj run
          rw [← same]
          change EthFrame self before.accountMap outcome.2.2.1
          simpa only [EthFrame, worldEth, accounts, ledger] using balances
      · simp [allowed] at run
        repeat' first | split at run | contradiction
        all_goals
          have same := Except.ok.inj run
          rw [← same]
          exact EthFrame.refl self before.accountMap

end Rollup.EVM
