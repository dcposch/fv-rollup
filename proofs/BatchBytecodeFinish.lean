import proofs.BatchEntry

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def batchFinalWrite (accounts : AccountMap) (I : ExecutionEnv) (slot credit : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner accounts slot credit)
        ⟨1⟩ (calldataWord I.calldata 68)) ⟨2⟩ (calldataWord I.calldata 4)) ⟨6⟩ ⟨0⟩

/-- Store withdrawal credit, root, and number, then release the lock. -/
theorem batch_bytecode_final_store {I : ExecutionEnv} {g : Sat256} {s0 : Ethereum.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : Nat}
    (newCredit slot available credit ret : UInt256) (rest : List UInt256)
    (space : rest.length + 14 ≤ 1024) (writable : I.perm = true)
    (destination : (D_J runtimeBytecode 0).contains ret = true)
    (reached : RD runtimeBytecode I g s0 ⟨813⟩
      (newCredit :: ⟨0⟩ :: slot :: calldataWord I.calldata 196 :: available :: credit ::
        batchDecodedStack I (ret :: rest)) mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g s0 ret rest mem aw rdata
      (cA, batchFinalWrite σ I slot newCredit) k' C' := by
  dsimp only [batchDecodedStack] at reached
  have beforeCredit := runtime_run reached with [jumpdest, swap1, swap2]
  obtain ⟨_, _, claimed⟩ := beforeCredit.sstore writable (by decide +kernel) (by evm_ov)
  have beforeRoot := runtime_run claimed with [pop, pop, pop, push1 ⟨1⟩, swap6, swap1, swap6]
  obtain ⟨_, _, rooted⟩ := beforeRoot.sstore writable (by decide +kernel) (by evm_ov)
  have beforeNumber := runtime_run rooted with [pop, pop, pop, push1 ⟨2⟩, swap4, swap1, swap4]
  obtain ⟨_, _, numbered⟩ := beforeNumber.sstore writable (by decide +kernel) (by evm_ov)
  have beforeUnlock := runtime_run numbered with [pop, pop, push0, push1 ⟨6⟩]
  obtain ⟨_, _, unlocked⟩ := beforeUnlock.sstore writable (by decide +kernel) (by evm_ov)
  exact ⟨_, _, runtime_run unlocked with [pop, jump destination]⟩

end Rollup.EVM
