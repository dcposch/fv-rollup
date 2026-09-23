import proofs.BatchBytecodeAccountingEntry
import proofs.BatchBytecodeBacking
import proofs.BatchBytecodeFinish

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
-- This syntax linter unfolds symbolic calldata guards. Kernel checks remain active.
set_option linter.constructorNameAsVariable false

namespace Rollup.EVM

def batchInputCredit (accounts : AccountMap) (I : ExecutionEnv) : UInt256 :=
  batchDepositWord (sstoreAccountMap I.codeOwner accounts ⟨6⟩ ⟨1⟩) I

def batchAfterDeposit (accounts : AccountMap) (I : ExecutionEnv) : AccountMap :=
  batchDepositWrite (sstoreAccountMap I.codeOwner accounts ⟨6⟩ ⟨1⟩) I (batchInputCredit accounts I)

def batchAvailableWord (accounts : AccountMap) (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132 + solcSlotWord (batchAfterDeposit accounts I) I ⟨3⟩

def batchAfterBacking (accounts : AccountMap) (I : ExecutionEnv) : AccountMap :=
  batchBackingWrite (batchAfterDeposit accounts I) I (batchAvailableWord accounts I)

def batchNextClaim (accounts : AccountMap) (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 196 + solcSlotWord (batchAfterBacking accounts I) I (batchClaimSlot I)

def batchOutputAccounts (accounts : AccountMap) (I : ExecutionEnv) : AccountMap :=
  batchFinalWrite (batchAfterBacking accounts I) I (batchClaimSlot I) (batchNextClaim accounts I)

/-- All checks for a successful bytecode batch. Reads follow storage-write order. -/
structure BatchBytecodeChecks (accounts : AccountMap) (env : ExecutionEnv) : Prop
    extends BatchAccountingChecks accounts env where
  backingFits : (calldataWord env.calldata 132).toNat +
    (solcSlotWord (batchAfterDeposit accounts env) env ⟨3⟩).toNat < UInt256.size
  withdrawalCovered : (calldataWord env.calldata 196).toNat ≤ (batchAvailableWord accounts env).toNat
  claimFits : (calldataWord env.calldata 196).toNat +
    (solcSlotWord (batchAfterBacking accounts env) env (batchClaimSlot env)).toNat < UInt256.size

/-- Every writable batch rejects or returns with its exact account-map writes. -/
theorem batch_bytecode_classification {cA gh bl σ σ₀ A I} {g : Sat256}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) ∨
      (BatchBytecodeChecks σ I ∧
       RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
         (cA, batchOutputAccounts σ I) ByteArray.empty) := by
  rcases batch_bytecode_accounting_entry (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, _, _, addEntry⟩
  · exact Or.inl rejected
  · by_cases backingFits : (calldataWord I.calldata 132).toNat +
        (solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩).toNat < UInt256.size
    · obtain ⟨_, _, added⟩ := runtime_checked_add (calldataWord I.calldata 132)
        (solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩) ⟨747⟩
        (⟨0⟩ :: batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
        (by simp [batchDecodedStack]) backingFits
        (jumpScan_valid runtimeBytecode 747 775 (by decide +kernel)) addEntry
      rcases batch_bytecode_backing_check (batchAvailableWord σ I) (batchInputCredit σ I)
          [⟨226⟩, ⟨0x88af9950⟩] (by decide) added with
        rejected | ⟨covered, _, _, checked⟩
      · exact Or.inl rejected
      · have memorySize := twoWordHashMem_size_96 (calldataWord I.calldata 100) ⟨4⟩
          (twoWordHashMem_size_96 (calldataWord I.calldata 100) ⟨4⟩ solcFreePtrMem_size)
        obtain ⟨_, _, claimEntry⟩ := batch_bytecode_backing_store _ _ _ (by decide) writable
          checks.withdrawalCanonical memorySize checked
        by_cases claimFits : (calldataWord I.calldata 196).toNat +
            (solcSlotWord (batchAfterBacking σ I) I (batchClaimSlot I)).toNat < UInt256.size
        · obtain ⟨_, _, claimAdded⟩ := runtime_checked_add (calldataWord I.calldata 196)
            (solcSlotWord (batchAfterBacking σ I) I (batchClaimSlot I)) ⟨813⟩
            (⟨0⟩ :: batchClaimSlot I :: calldataWord I.calldata 196 :: batchAvailableWord σ I ::
              batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
            (by simp [batchDecodedStack]) claimFits
            (jumpScan_valid runtimeBytecode 813 845 (by decide +kernel)) claimEntry
          obtain ⟨_, _, finished⟩ := batch_bytecode_final_store (batchNextClaim σ I)
            (batchClaimSlot I) (batchAvailableWord σ I) (batchInputCredit σ I) ⟨226⟩
            [⟨0x88af9950⟩] (by decide) writable
            (jumpScan_valid runtimeBytecode 226 240 (by decide +kernel)) claimAdded
          have allChecks : BatchBytecodeChecks σ I := by
            constructor
            · with_reducible exact checks
            · with_reducible exact backingFits
            · with_reducible exact covered
            · with_reducible exact claimFits
          exact Or.inr ⟨allChecks,
            (runtime_run finished with [jumpdest]).stop (by decide +kernel) (by evm_ov)⟩
        · exact Or.inl (runtime_checked_add_overflow (calldataWord I.calldata 196)
            (solcSlotWord (batchAfterBacking σ I) I (batchClaimSlot I)) ⟨813⟩
            (⟨0⟩ :: batchClaimSlot I :: calldataWord I.calldata 196 :: batchAvailableWord σ I ::
              batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
            (by simp [batchDecodedStack]) (by omega) claimEntry)
    · exact Or.inl (runtime_checked_add_overflow (calldataWord I.calldata 132)
        (solcSlotWord (batchAfterDeposit σ I) I ⟨3⟩) ⟨747⟩
        (⟨0⟩ :: batchInputCredit σ I :: batchDecodedStack I [⟨226⟩, ⟨0x88af9950⟩])
        (by simp [batchDecodedStack]) (by omega) addEntry)

/-- An accepted batch passed all checks and has the exact stored result. -/
theorem batch_xi_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' σ' gas substate output} (code : I.code = runtimeBytecode)
    (writable : I.perm = true) (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA', σ', gas, substate) output)) :
    BatchBytecodeChecks σ I ∧ cA' = cA ∧ σ' = batchOutputAccounts σ I ∧ output = ByteArray.empty := by
  rcases batch_bytecode_classification (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (g := g) code writable bounded selector with
    rejected | ⟨checks, returned⟩
  · rcases rejected.xiResult code with failed | ⟨gas', data, actual⟩
    · rw [success] at failed
      cases failed
    · rw [success] at actual
      cases actual
  · rcases returned with failed | ⟨finalState, result, accounts⟩
    · have impossible := Xi_error_of_X (g := g.toUInt256) (by
        rw [← code] at failed
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using failed)
      rw [success] at impossible
      cases impossible
    · have actual := Xi_success_of_X (g := g.toUInt256) (by
        rw [← code] at result
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using result)
      rw [success] at actual
      cases actual
      exact ⟨checks, congrArg Prod.fst accounts, congrArg Prod.snd accounts, rfl⟩

end Rollup.EVM
