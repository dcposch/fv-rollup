import proofs.WithdrawalSource
import proofs.SelectorTable
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

def withdrawalOwnerFromCalldata (I : ExecutionEnv) : Address :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

/-- Decode the owner and amount into the source parameter store. -/
theorem withdrawal_abi_decode (I : ExecutionEnv) (length : 68 ≤ I.calldata.size)
    (signedBound : I.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (contract.transitions[2]!.params.map Param.name)
      (transitionSignature contract.transitions[2]!).paramTypes I.calldata =
      some (withdrawalLocals (withdrawalOwnerFromCalldata I) (calldataWord I.calldata 36).toNat) :=
  decodeCalldata_addr_uint256_ok length signedBound canonical

/-- Invalid lengths or noncanonical owners cause ABI rejection. -/
theorem withdrawal_abi_rejected (I : ExecutionEnv)
    (invalid : ¬ (68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus)) :
    decodeCalldataWithMode config.abiDecodeMode (contract.transitions[2]!.params.map Param.name)
      (transitionSignature contract.transitions[2]!).paramTypes I.calldata = none := by
  change decodeCalldata ["owner", "amount"] [.elem .address, abiUInt256] I.calldata = none
  by_cases four : 4 ≤ I.calldata.size
  · by_cases length : 68 ≤ I.calldata.size
    · by_cases signedBound : I.calldata.size < 2 ^ 255 + 4
      · exact decodeCalldata_addr_uint256_none_noncanon length signedBound
          (fun canonical => invalid ⟨length, signedBound, canonical⟩)
      · exact decodeCalldata_addr_uint256_none_huge (by omega)
    · exact decodeCalldata_addr_uint256_none_short four (by omega)
  · have size : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    unfold decodeCalldata
    rw [if_pos (by rw [size]; omega : I.calldata.toList.length < 4)]

/-- Withdrawal calldata binds the caller, value, owner, and amount to the call label. -/
theorem withdrawal_call_bound (evm : Ethereum.State)
    (length : 68 ≤ evm.executionEnv.calldata.size)
    (signedBound : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord evm.executionEnv.calldata 4).toNat < _root_.EVM.addressModulus)
    (selector : solcSelectorWord evm.executionEnv = ⟨0xbb3ef682⟩) :
    CallBound evm
      (withdrawalLocals (withdrawalOwnerFromCalldata evm.executionEnv)
        (calldataWord evm.executionEnv.calldata 36).toNat)
      ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat,
        .withdrawPendingBalance (withdrawalOwnerFromCalldata evm.executionEnv)
          (calldataWord evm.executionEnv.calldata 36).toNat⟩ := by
  have dispatched := source_selector_dispatch evm.executionEnv ⟨2, by decide⟩ (by omega) selector
  refine ⟨rfl, rfl, ?_, withdrawal_abi_decode evm.executionEnv length signedBound canonical, ?_⟩
  · exact selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some (by rfl) (by rfl) dispatched
  · rfl

end Rollup.EVM
