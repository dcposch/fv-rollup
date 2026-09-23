import proofs.CallbackStorage

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

/-- A foreign storage context preserves the locked rollup at each opcode. -/
theorem foreign_step_storage {self : AccountAddress} {before after : Ethereum.State}
    {gasCost : Nat} {instr : Operation × Option (UInt256 × Nat)}
    (pinned : (before.accountMap.findD self default).code = runtimeBytecode)
    (locked : (before.accountMap.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (foreign : self ≠ before.executionEnv.codeOwner)
    (run : step gasCost instr before = .ok after) :
    CodeStorageFrame self before.accountMap after.accountMap := by
  apply locked_locality_chain pinned locked
  cases remaining : 1024 - before.executionEnv.depth.val with
  | zero =>
    apply account_changes_consistent_except_owner_of_step_max_depth gasCost instr
      before after _ run self foreign
    apply Fin.ext
    have bound := before.executionEnv.depth.isLt
    change before.executionEnv.depth.val = 1024
    omega
  | succ n =>
    apply account_changes_consistent_except_owner_of_step_succ_depth gasCost instr
      before after self remaining _ _ run foreign
    · intros blobs gh bl cA depth σ σ₀ A s o r c g p v v' d H w cA' σ' g' A' z output _ call different
      exact account_changes_consistent_weak_of_Theta c cA' σ' g' A' z output depth call self different
    · intros blobs gh bl cA depth σ σ₀ A s o g p v i salt H w a cA' σ' g' A' z output _ call
      exact account_changes_consistent_weak_of_Lambda a cA' σ' g' A' z output depth call self

/-- Foreign code can run in any other storage context. -/
theorem foreign_call_storage
    {blobs cA gh bl accounts original substate sender origin receiver code gas price value contextValue
      calldata depth header writable cA' after gas' substate' accepted output}
    (self : AccountAddress)
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (foreign : self ≠ receiver)
    (run : Θ blobs cA gh bl accounts original substate sender origin receiver code
      gas price value contextValue calldata depth header writable =
      (cA', after, gas', substate', accepted, output)) :
    CodeStorageFrame self accounts after := by
  exact locked_locality_chain pinned locked
    (account_changes_consistent_weak_of_Theta code cA' after gas' substate' accepted output depth
      run self foreign)

/-- A successful foreign execution preserves the locked rollup's code and storage. -/
theorem foreign_xi_storage
    {cA gh bl accounts original gas substate env cA' after gas' substate' output}
    (self : AccountAddress)
    (pinned : (accounts.findD self default).code = runtimeBytecode)
    (locked : (accounts.findD self default).storage.findD ⟨6⟩ ⟨0⟩ ≠ ⟨0⟩)
    (foreign : self ≠ env.codeOwner)
    (run : Ξ cA gh bl accounts original gas substate env =
      .ok (.success (cA', after, gas', substate') output)) :
    CodeStorageFrame self accounts after := by
  apply locked_locality_chain pinned locked
  cases remaining : 1024 - env.depth.val with
  | zero =>
    apply account_changes_consistent_except_owner_of_Xi_max_depth cA' after gas' substate' output
      _ run self foreign
    apply Fin.ext
    have bound := env.depth.isLt
    change env.depth.val = 1024
    omega
  | succ n =>
    apply account_changes_consistent_except_owner_of_Xi_succ_depth cA' after gas' substate' output
      n self remaining _ _ run foreign
    · intros blobs gh bl cA depth σ σ₀ A s o r c g p v v' d H w cA' σ' g' A' z output _ call different
      exact account_changes_consistent_weak_of_Theta c cA' σ' g' A' z output depth call self different
    · intros blobs gh bl cA depth σ σ₀ A s o g p v i salt H w a cA' σ' g' A' z output _ call
      exact account_changes_consistent_weak_of_Lambda a cA' σ' g' A' z output depth call self

end Rollup.EVM
