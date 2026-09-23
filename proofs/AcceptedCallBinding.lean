import proofs.DepositEquivalence
import proofs.BatchAcceptedEquivalence
import proofs.WithdrawalABI
import proofs.WithdrawalBytecodeClassification

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- Deposit calldata binds the actual caller, value, and owner. -/
theorem deposit_call_bound (evm : Ethereum.State)
    (length : 36 ≤ evm.executionEnv.calldata.size)
    (signedBound : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (canonical : (calldataWord evm.executionEnv.calldata 4).toNat < _root_.EVM.addressModulus)
    (selector : solcSelectorWord evm.executionEnv = ⟨0xf340fa01⟩) :
    let owner := AccountAddress.ofNat (calldataWord evm.executionEnv.calldata 4).toNat
    CallBound evm (depositLocals owner)
      ⟨evm.executionEnv.source, evm.executionEnv.weiValue.toNat, .deposit owner⟩ := by
  have dispatched := source_selector_dispatch evm.executionEnv ⟨0, by decide⟩ (by omega) selector
  refine ⟨rfl, rfl, ?_, decodeCalldata_address_ok length signedBound canonical, ?_⟩
  · exact selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some (by rfl) (by rfl) dispatched
  · rfl

/-- Accepted deposit bytecode supplies its decoded call label. -/
theorem deposit_accepted_call_bound {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xf340fa01⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    let owner := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
    CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) (depositLocals owner)
      ⟨I.source, I.weiValue.toNat, .deposit owner⟩ := by
  obtain ⟨length, signedBound, canonical, _⟩ := deposit_xi_success code writable bounded selector success
  exact deposit_call_bound _ length signedBound canonical selector

/-- Accepted batch bytecode supplies its decoded call label. -/
theorem batch_accepted_call_bound {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0x88af9950⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I) (batchLocals (batchFromCalldata I))
      ⟨I.source, I.weiValue.toNat, .executeBatch (batchFromCalldata I)⟩ := by
  have checks := batch_xi_header (g := Sat256.ofUInt256 g) code writable bounded selector success
  exact batch_call_bound _ checks.length checks.signedBound checks.depositCanonical checks.withdrawalCanonical selector

/-- Accepted withdrawal bytecode supplies its decoded call label. -/
theorem withdrawal_accepted_call_bound {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' σ' gas substate output}
    (code : I.code = runtimeBytecode) (writable : I.perm = true)
    (bounded : I.calldata.size < UInt256.size)
    (selector : solcSelectorWord I = ⟨0xbb3ef682⟩)
    (success : Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA', σ', gas, substate) output)) :
    CallBound (initState cA gh bl σ σ₀ (.ofUInt256 g) A I)
      (withdrawalLocals (withdrawalOwnerFromCalldata I) (calldataWord I.calldata 36).toNat)
      ⟨I.source, I.weiValue.toNat,
        .withdrawPendingBalance (withdrawalOwnerFromCalldata I) (calldataWord I.calldata 36).toNat⟩ := by
  have checks := (withdrawal_xi_success (g := Sat256.ofUInt256 g) code writable bounded selector success).1
  exact withdrawal_call_bound _ checks.length checks.signedBound checks.canonical selector

end Rollup.EVM
