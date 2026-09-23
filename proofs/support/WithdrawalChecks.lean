import semantics.Bytecode
import Reasoning.Solc

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

def withdrawalClaimSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4)

def withdrawalClaimWord (accounts : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord accounts I (withdrawalClaimSlot I)

/-- These checks precede the withdrawal's external call. -/
structure WithdrawalBytecodeChecks (accounts : AccountMap) (I : ExecutionEnv) : Prop where
  nonpayable : I.weiValue = ⟨0⟩
  length : 68 ≤ I.calldata.size
  signedBound : I.calldata.size < 2 ^ 255 + 4
  canonical : (calldataWord I.calldata 4).toNat < _root_.EVM.addressModulus
  unlocked : solcSlotWord accounts I ⟨6⟩ = ⟨0⟩
  positive : calldataWord I.calldata 36 ≠ ⟨0⟩
  covered : (calldataWord I.calldata 36).toNat ≤
    (withdrawalClaimWord (sstoreAccountMap I.codeOwner accounts ⟨6⟩ ⟨1⟩) I).toNat

end Rollup.EVM
