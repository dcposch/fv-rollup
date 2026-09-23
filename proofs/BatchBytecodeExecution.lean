import proofs.BatchBytecodeClassification

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
-- This syntax linter unfolds symbolic calldata guards. Kernel checks remain active.
set_option linter.constructorNameAsVariable false

namespace Rollup.EVM

/-- A valid batch header reaches the owner checks, unless gas runs out. -/
theorem batch_bytecode_prefix_execution {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (checks : BatchPrefixChecks σ I) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨516⟩
      (batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ ⟨1⟩) k C := by
  have four : 4 ≤ I.calldata.size := by have := checks.length; omega
  obtain ⟨_, _, dispatched⟩ := mutation_dispatch (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) .batch code four bounded selector
  obtain ⟨_, _, decoder⟩ := mutation_decoder .batch [⟨0x88af9950⟩] (by decide) checks.nonpayable dispatched
  obtain ⟨_, _, first⟩ := batch_decode_first ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩]
    checks.length checks.signedBound bounded (by decide) decoder
  obtain ⟨_, _, firstChecked⟩ := runtime_address_check (calldataWord I.calldata 100) ⟨1242⟩
    (batchFirstRest I ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩]) checks.depositCanonical
    (jumpScan_valid runtimeBytecode 1242 1270 (by decide +kernel))
    (by simp [batchFirstRest]) first
  obtain ⟨_, _, second⟩ := batch_decode_second ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩] (by decide) firstChecked
  obtain ⟨_, _, secondChecked⟩ := runtime_address_check (calldataWord I.calldata 164) ⟨1265⟩
    (batchSecondRest I ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩]) checks.withdrawalCanonical
    (jumpScan_valid runtimeBytecode 1265 1290 (by decide +kernel))
    (by simp [batchSecondRest]) second
  obtain ⟨_, _, decoded⟩ := batch_decode_tail ⟨221⟩ [⟨226⟩, ⟨0x88af9950⟩] (by decide)
    (jumpScan_valid runtimeBytecode 221 240 (by decide +kernel)) secondChecked
  dsimp only [batchDecodedStack] at decoded
  have entered := runtime_run decoded with [jumpdest, push2 ⟨441⟩,
    jump (jumpScan_valid runtimeBytecode 441 470 (by decide +kernel))]
  obtain ⟨_, _, locked⟩ := batch_bytecode_enter _ (by simp) writable checks.unlocked entered
  rcases batch_bytecode_authorization_cases _ (by simp) locked with
    ⟨_, invalid⟩ | ⟨_, _, _, authorized⟩
  · rw [solc_slot_store_other σ I ⟨0⟩ ⟨6⟩ ⟨1⟩ (by decide)] at invalid
    exact False.elim (invalid checks.authorized)
  · rcases batch_bytecode_header_cases _ (by decide) authorized with
      ⟨_, invalid⟩ | ⟨_, _, _, finished⟩
    · rw [solc_slot_store_other σ I ⟨2⟩ ⟨6⟩ ⟨1⟩ (by decide),
        solc_slot_store_other σ I ⟨1⟩ ⟨6⟩ ⟨1⟩ (by decide)] at invalid
      have number : calldataWord I.calldata 4 = solcSlotWord σ I ⟨2⟩ + ⟨1⟩ := by
        apply u256_inj
        rw [uadd_toNat]
        change (calldataWord I.calldata 4).toNat = ((solcSlotWord σ I ⟨2⟩).toNat + 1) % UInt256.size
        rw [Nat.mod_eq_of_lt checks.numberFits]
        exact checks.nextNumber
      exact False.elim (invalid ⟨checks.numberFits, number, checks.oldRoot⟩)
    · exact finished

/-- Valid owner and deposit checks reach the backing calculation, unless gas runs out. -/
theorem batch_bytecode_accounting_execution {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (checks : BatchAccountingChecks σ I) :
    let mem := twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ solcFreePtrMem
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1385⟩
      (solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩ :: calldataWord I.calldata 132 ::
        ⟨747⟩ :: ⟨0⟩ :: batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
      (twoWordHashMem (calldataWord I.calldata 100) ⟨4⟩ mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, batchAfterDeposit σ I) k C := by
  obtain ⟨_, _, entered⟩ := batch_bytecode_prefix_execution (cA := cA) (gh := gh) (bl := bl)
    (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector checks.toBatchPrefixChecks
  rcases batch_bytecode_deposit_owner_cases _ (by decide) checks.depositCanonical entered with
    ⟨_, invalid⟩ | ⟨_, _, _, afterDepositOwner⟩
  · exfalso
    apply invalid
    with_reducible exact checks.depositOwner
  · rcases batch_bytecode_withdrawal_owner_cases _ (by decide) checks.withdrawalCanonical afterDepositOwner with
      ⟨_, invalid⟩ | ⟨_, _, _, afterOwners⟩
    · exfalso
      apply invalid
      with_reducible exact checks.withdrawalOwner
    · obtain ⟨_, _, loaded⟩ := batch_bytecode_deposit_load _ (by decide) checks.depositCanonical
        solcFreePtrMem_size afterOwners
      rcases batch_bytecode_deposit_check_cases _ _ (by decide) loaded with
        ⟨_, invalid⟩ | ⟨_, _, _, checked⟩
      · exact False.elim (invalid checks.depositCovered)
      · obtain ⟨steps, cost, stored⟩ := batch_bytecode_deposit_store _ _ (by decide) writable
          checks.depositCanonical (twoWordHashMem_size_96 _ _ solcFreePtrMem_size) checked
        exact ⟨steps, cost, stored⟩

/-- A valid writable batch has the exact result, unless gas runs out. -/
theorem batch_bytecode_execution {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (checks : BatchBytecodeChecks σ I) :
    RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, batchOutputAccounts σ I) ByteArray.empty := by
  obtain ⟨_, _, addEntry⟩ := batch_bytecode_accounting_execution (cA := cA) (gh := gh) (bl := bl)
    (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector checks.toBatchAccountingChecks
  obtain ⟨_, _, added⟩ := runtime_checked_add (calldataWord I.calldata 132)
    (solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩) ⟨747⟩
    (⟨0⟩ :: batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
    (by simp [batchDecodedStack]) checks.backingFits
    (jumpScan_valid runtimeBytecode 747 775 (by decide +kernel)) addEntry
  rcases batch_bytecode_backing_check_cases (batchAvailableWord σ I) (batchInputCredit σ I)
      [⟨226⟩, ⟨0x88af9950⟩] (by decide) added with
    ⟨_, invalid⟩ | ⟨_, _, _, checked⟩
  · exact False.elim (invalid checks.withdrawalCovered)
  · have memorySize := twoWordHashMem_size_96 (calldataWord I.calldata 100) ⟨4⟩
      (twoWordHashMem_size_96 (calldataWord I.calldata 100) ⟨4⟩ solcFreePtrMem_size)
    obtain ⟨_, _, claimEntry⟩ := batch_bytecode_backing_store _ _ _ (by decide) writable
      checks.withdrawalCanonical memorySize checked
    obtain ⟨_, _, claimAdded⟩ := runtime_checked_add (calldataWord I.calldata 196)
      (solcSlotWord (batchAfterBacking σ I) I (batchClaimSlot I)) ⟨813⟩
      (⟨0⟩ :: batchClaimSlot I :: calldataWord I.calldata 196 :: batchAvailableWord σ I ::
        batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
      (by simp [batchDecodedStack]) checks.claimFits
      (jumpScan_valid runtimeBytecode 813 845 (by decide +kernel)) claimEntry
    obtain ⟨_, _, finished⟩ := batch_bytecode_final_store (batchNextClaim σ I)
      (batchClaimSlot I) (batchAvailableWord σ I) (batchInputCredit σ I) ⟨226⟩
      [⟨0x88af9950⟩] (by decide) writable
      (jumpScan_valid runtimeBytecode 226 240 (by decide +kernel)) claimAdded
    exact (runtime_run finished with [jumpdest]).stop (by decide +kernel) (by evm_ov)

/-- A valid batch cannot revert. It returns the specified accounts or runs out of gas. -/
theorem batch_xi_execution {cA gh bl σ σ₀ A I} {g : UInt256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) (checks : BatchBytecodeChecks σ I) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass ∨
      ∃ gas substate, Ξ cA gh bl σ σ₀ g A I =
        .ok (.success (cA, batchOutputAccounts σ I, gas, substate) ByteArray.empty) := by
  rcases batch_bytecode_execution (cA := cA) (gh := gh) (bl := bl)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) code writable bounded selector checks with
    failed | ⟨finalState, result, accounts⟩
  · exact Or.inl (Xi_error_of_X (g := g) (by
      rw [← code] at failed
      simpa [Sat256.ofUInt256] using failed))
  · have actual := Xi_success_of_X (g := g) (by
      rw [← code] at result
      simpa [Sat256.ofUInt256] using result)
    have created : finalState.createdAccounts = cA := congrArg Prod.fst accounts
    have stored : finalState.accountMap = batchOutputAccounts σ I := congrArg Prod.snd accounts
    rw [created, stored] at actual
    exact Or.inr ⟨_, _, actual⟩

end Rollup.EVM
