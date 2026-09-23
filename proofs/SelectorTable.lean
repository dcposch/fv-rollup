import semantics.Bindings
import Reasoning.Dispatch
import proofs.generated.KeccakDeposit
import proofs.generated.KeccakExecuteBatch
import proofs.generated.KeccakWithdraw
import proofs.generated.KeccakSequencer
import proofs.generated.KeccakStateRoot
import proofs.generated.KeccakBatchNumber
import proofs.generated.KeccakBacking
import proofs.generated.KeccakPendingDeposits
import proofs.generated.KeccakPendingWithdrawals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Rollup.EVM

def sourceSelectorBytes (index : Fin 9) : ByteArray :=
  ([⟨#[243, 64, 250, 1]⟩, ⟨#[136, 175, 153, 80]⟩, ⟨#[187, 62, 246, 130]⟩, ⟨#[92, 27, 186, 56]⟩, ⟨#[149, 136, 236, 162]⟩, ⟨#[186, 135, 48, 101]⟩, ⟨#[201, 80, 63, 226]⟩, ⟨#[235, 51, 73, 185]⟩, ⟨#[243, 244, 55, 3]⟩] : List ByteArray)[index.val]!

def sourceSelectorWord (index : Fin 9) : UInt256 :=
  ([⟨0xf340fa01⟩, ⟨0x88af9950⟩, ⟨0xbb3ef682⟩, ⟨0x5c1bba38⟩, ⟨0x9588eca2⟩, ⟨0xba873065⟩, ⟨0xc9503fe2⟩, ⟨0xeb3349b9⟩, ⟨0xf3f43703⟩] : List UInt256)[index.val]!

private theorem selector_bytes_deposit :
    selectorOf contract.transitions[0]! = ⟨#[243, 64, 250, 1]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[0]! = "deposit(address)" := by
    change printSignature ⟨"deposit", [.elem .address]⟩ = _
    simp only [printSignature, List.map_cons, List.map_nil, abiToSigStr, elemToSigStr]
    decide +kernel
  rw [signature, deposit_selector_hash]
  decide +kernel

private theorem selector_bytes_execute_batch :
    selectorOf contract.transitions[1]! = ⟨#[136, 175, 153, 80]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[1]! = "executeBatch(uint256,bytes32,bytes32,address,uint256,address,uint256)" := by
    change printSignature ⟨"executeBatch", [.elem (.int (.uint ⟨256, by decide⟩)), .elem (.bytes ⟨31, by decide⟩), .elem (.bytes ⟨31, by decide⟩), .elem .address, .elem (.int (.uint ⟨256, by decide⟩)), .elem .address, .elem (.int (.uint ⟨256, by decide⟩))]⟩ = _
    simp only [printSignature, List.map_cons, List.map_nil, abiToSigStr, elemToSigStr]
    decide +kernel
  rw [signature, HashCertificates.execute_batch_hash]
  decide +kernel

private theorem selector_bytes_withdraw :
    selectorOf contract.transitions[2]! = ⟨#[187, 62, 246, 130]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[2]! = "withdrawPendingBalance(address,uint256)" := by
    change printSignature ⟨"withdrawPendingBalance", [.elem .address, .elem (.int (.uint ⟨256, by decide⟩))]⟩ = _
    simp only [printSignature, List.map_cons, List.map_nil, abiToSigStr, elemToSigStr]
    decide +kernel
  rw [signature, HashCertificates.withdraw_hash]
  decide +kernel

private theorem selector_bytes_sequencer :
    selectorOf contract.transitions[3]! = ⟨#[92, 27, 186, 56]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[3]! = "sequencer()" := by
    change printSignature ⟨"sequencer", []⟩ = _
    simp only [printSignature, List.map_nil]
    decide +kernel
  rw [signature, HashCertificates.sequencer_hash]
  decide +kernel

private theorem selector_bytes_state_root :
    selectorOf contract.transitions[4]! = ⟨#[149, 136, 236, 162]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[4]! = "stateRoot()" := by
    change printSignature ⟨"stateRoot", []⟩ = _
    simp only [printSignature, List.map_nil]
    decide +kernel
  rw [signature, HashCertificates.state_root_hash]
  decide +kernel

private theorem selector_bytes_batch_number :
    selectorOf contract.transitions[5]! = ⟨#[186, 135, 48, 101]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[5]! = "batchNumber()" := by
    change printSignature ⟨"batchNumber", []⟩ = _
    simp only [printSignature, List.map_nil]
    decide +kernel
  rw [signature, HashCertificates.batch_number_hash]
  decide +kernel

private theorem selector_bytes_backing :
    selectorOf contract.transitions[6]! = ⟨#[201, 80, 63, 226]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[6]! = "backing()" := by
    change printSignature ⟨"backing", []⟩ = _
    simp only [printSignature, List.map_nil]
    decide +kernel
  rw [signature, HashCertificates.backing_hash]
  decide +kernel

private theorem selector_bytes_pending_deposits :
    selectorOf contract.transitions[7]! = ⟨#[235, 51, 73, 185]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[7]! = "pendingDeposits(address)" := by
    change printSignature ⟨"pendingDeposits", [.elem .address]⟩ = _
    simp only [printSignature, List.map_cons, List.map_nil, abiToSigStr, elemToSigStr]
    decide +kernel
  rw [signature, HashCertificates.pending_deposits_hash]
  decide +kernel

private theorem selector_bytes_pending_withdrawals :
    selectorOf contract.transitions[8]! = ⟨#[243, 244, 55, 3]⟩ := by
  unfold selectorOf
  have signature : transitionSigStr contract.transitions[8]! = "pendingWithdrawals(address)" := by
    change printSignature ⟨"pendingWithdrawals", [.elem .address]⟩ = _
    simp only [printSignature, List.map_cons, List.map_nil, abiToSigStr, elemToSigStr]
    decide +kernel
  rw [signature, HashCertificates.pending_withdrawals_hash]
  decide +kernel

/-- Each source signature hashes to the compiled selector. -/
theorem source_selector_bytes (index : Fin 9) :
    selectorOf contract.transitions[index.val]! = sourceSelectorBytes index := by
  fin_cases index
  · exact selector_bytes_deposit
  · exact selector_bytes_execute_batch
  · exact selector_bytes_withdraw
  · exact selector_bytes_sequencer
  · exact selector_bytes_state_root
  · exact selector_bytes_batch_number
  · exact selector_bytes_backing
  · exact selector_bytes_pending_deposits
  · exact selector_bytes_pending_withdrawals

theorem source_selector_comparison (I : ExecutionEnv) (index : Fin 9)
    (length : 4 ≤ I.calldata.size) : UInt256.eq (sourceSelectorWord index) (solcSelectorWord I) =
      (if sourceSelectorBytes index == I.calldata.extract 0 4 then ⟨1⟩ else ⟨0⟩) := by
  fin_cases index
  · exact evmSelectorDecode length 243 64 250 1 ⟨0xf340fa01⟩ (by decide +kernel)
  · exact evmSelectorDecode length 136 175 153 80 ⟨0x88af9950⟩ (by decide +kernel)
  · exact evmSelectorDecode length 187 62 246 130 ⟨0xbb3ef682⟩ (by decide +kernel)
  · exact evmSelectorDecode length 92 27 186 56 ⟨0x5c1bba38⟩ (by decide +kernel)
  · exact evmSelectorDecode length 149 136 236 162 ⟨0x9588eca2⟩ (by decide +kernel)
  · exact evmSelectorDecode length 186 135 48 101 ⟨0xba873065⟩ (by decide +kernel)
  · exact evmSelectorDecode length 201 80 63 226 ⟨0xc9503fe2⟩ (by decide +kernel)
  · exact evmSelectorDecode length 235 51 73 185 ⟨0xeb3349b9⟩ (by decide +kernel)
  · exact evmSelectorDecode length 243 244 55 3 ⟨0xf3f43703⟩ (by decide +kernel)

/-- A literal selector word fixes the first four calldata bytes. -/
theorem source_selector_calldata (I : ExecutionEnv) (index : Fin 9)
    (length : 4 ≤ I.calldata.size)
    (selector : solcSelectorWord I = sourceSelectorWord index) :
    I.calldata.extract 0 4 = sourceSelectorBytes index := by
  have comparison := source_selector_comparison I index length
  rw [selector, u256_eq_refl] at comparison
  have matched : (sourceSelectorBytes index == I.calldata.extract 0 4) = true := by
    by_contra mismatch
    rw [Bool.eq_false_of_not_eq_true mismatch] at comparison
    exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) comparison
  exact (byteArray_eq_of_beq matched).symm

/-- Source dispatch agrees with every compiled selector. -/
theorem source_selector_dispatch (I : ExecutionEnv) (index : Fin 9)
    (length : 4 ≤ I.calldata.size)
    (selector : solcSelectorWord I = sourceSelectorWord index) :
    dispatchMsg contract I.calldata = some contract.transitions[index.val]! := by
  have bytes := source_selector_calldata I index length selector
  rw [dispatchMsg_eq_dispatchList contract I.calldata rfl rfl]
  change dispatchList [contract.transitions[0]!, contract.transitions[1]!, contract.transitions[2]!, contract.transitions[3]!, contract.transitions[4]!, contract.transitions[5]!, contract.transitions[6]!, contract.transitions[7]!, contract.transitions[8]!] I.calldata = _
  simp only [dispatchList_cons, selector_bytes_deposit, selector_bytes_execute_batch, selector_bytes_withdraw, selector_bytes_sequencer, selector_bytes_state_root, selector_bytes_batch_number, selector_bytes_backing, selector_bytes_pending_deposits, selector_bytes_pending_withdrawals, bytes]
  fin_cases index <;> rfl

end Rollup.EVM
