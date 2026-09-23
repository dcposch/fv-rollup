import proofs.WithdrawalCall
import proofs.WithdrawalExecution
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- The bytecode payment witness supplies the same call in the source semantics. -/
theorem withdrawal_payment_to_source (evm : Ethereum.State) (owner : Address) (amount : UInt256)
    (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (data : ByteArray)
    (writable : evm.executionEnv.perm = true)
    (payment : WithdrawalPaymentWitness evm evm.executionEnv evm.createdAccounts evm.accountMap
      (UInt256.ofNat owner.val) amount cA' σ' data) :
    ∃ outputSubstate, callViaEVM evm owner (Int.ofNat amount.toNat) ByteArray.empty
      (true, { evm with accountMap := σ', substate := outputSubstate, createdAccounts := cA' }, data) := by
  obtain ⟨balance, depth, inputSubstate, callGas, returnedGas, outputSubstate, call⟩ := payment
  rw [accountAddress_roundtrip, accountAddress_roundtrip, writable] at call
  refine ⟨outputSubstate, .callMade (wordOfInt_ofNat_toNat amount).symm
    ⟨callGas, inputSubstate, call⟩ rfl balance ?_⟩
  intro full
  rw [full] at depth
  exact (by decide : ¬ (1024 : Nat) < 1024) depth

end Rollup.EVM
