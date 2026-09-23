import proofs.WorldTransfers

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Rollup.EVM

def destructionAccounts (accounts : AccountMap) (sender receiver : Address) (created : Bool) : AccountMap :=
  match accounts.find? sender with
  | none => accounts
  | some owner =>
    match accounts.find? receiver with
    | none => if owner.balance == (⟨0⟩ : UInt256) then accounts else
        (accounts.insert receiver { (default : Account) with balance := owner.balance }).insert sender
          { owner with balance := ⟨0⟩ }
    | some target => if receiver ≠ sender then
        (accounts.insert receiver { target with balance := target.balance + owner.balance }).insert sender
          { owner with balance := ⟨0⟩ }
      else if created then
        (accounts.insert receiver { target with balance := ⟨0⟩ }).insert sender { owner with balance := ⟨0⟩ }
      else accounts

/-- The opcode uses the specified transfer or burn account map. -/
theorem selfdestruct_accounts {before after : Ethereum.State} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)}
    (run : step gasCost (.System .SELFDESTRUCT, arg) before = .ok after) :
    ∃ receiver, after.accountMap = destructionAccounts before.accountMap before.executionEnv.codeOwner
      receiver (before.createdAccounts.contains before.executionEnv.codeOwner) := by
  cases popped : before.machineState.stack.pop with
  | none => simp [step, popped] at run
  | some pair =>
    obtain ⟨stack, target⟩ := pair
    refine ⟨AccountAddress.ofUInt256 target, ?_⟩
    by_cases created : before.executionEnv.codeOwner ∈ before.createdAccounts
    · simp [step, popped, created] at run
      rw [← run]
      simp [destructionAccounts, created, Ethereum.State.lookupAccount, dbgTrace,
        Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
      rfl
    · simp [step, popped, created] at run
      rw [← run]
      simp [destructionAccounts, created, Ethereum.State.lookupAccount, dbgTrace,
        Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
      rfl

/-- Sending self-destruct proceeds to another account has the exact transfer ledger. -/
theorem destruction_ledger_ne (accounts : AccountMap) (sender receiver : Address) (created : Bool)
    (different : receiver ≠ sender) (world : worldEth accounts < wordLimit) :
    ethLedger (destructionAccounts accounts sender receiver created) =
      debit (credit (ethLedger accounts) receiver (ethLedger accounts sender)) sender (ethLedger accounts sender) := by
  cases ownerFound : accounts.find? sender with
  | none =>
    have old : ethLedger accounts sender = 0 := by rw [ethLedger_lookup, ownerFound]; rfl
    simp [destructionAccounts, ownerFound, old, credit, debit]
  | some owner =>
    have ownerBalance : ethLedger accounts sender = owner.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, ownerFound]
    cases targetFound : accounts.find? receiver with
    | none =>
      have targetBalance : ethLedger accounts receiver = 0 := by rw [ethLedger_lookup, targetFound]; rfl
      by_cases zero : owner.balance = (⟨0⟩ : UInt256)
      · have amount : ethLedger accounts sender = 0 := by rw [ownerBalance, zero]; rfl
        simp [destructionAccounts, ownerFound, targetFound, zero, amount, credit, debit]
      · simp [destructionAccounts, ownerFound, targetFound, zero, ethLedger_insert,
          credit, debit, Function.update_of_ne (Ne.symm different), ownerBalance,
          targetBalance, UInt256.toNat]
    | some target =>
      have targetBalance : ethLedger accounts receiver = target.balance.toNat := by
        simp [ethLedger, Batteries.RBMap.findD, targetFound]
      have add : (target.balance + owner.balance).toNat = target.balance.toNat + owner.balance.toNat := by
        rw [uadd_toNat]
        apply Nat.mod_eq_of_lt
        have bounded := funded_recipient_bound accounts receiver sender owner.balance different
          (by rw [ownerBalance]) world
        simpa only [targetBalance] using bounded
      simp [destructionAccounts, ownerFound, targetFound, different, ethLedger_insert,
        credit, debit, Function.update_of_ne (Ne.symm different), ownerBalance,
        targetBalance, add, show (⟨0⟩ : UInt256).toNat = 0 from rfl]

/-- Self-destruction to the same address burns only a newly created account's ETH. -/
theorem destruction_ledger_self (accounts : AccountMap) (sender : Address) (created : Bool) :
    ethLedger (destructionAccounts accounts sender sender created) =
      if created then debit (ethLedger accounts) sender (ethLedger accounts sender) else ethLedger accounts := by
  cases found : accounts.find? sender with
  | none =>
    have old : ethLedger accounts sender = 0 := by rw [ethLedger_lookup, found]; rfl
    cases created <;> simp [destructionAccounts, found, old, debit]
  | some owner =>
    have old : ethLedger accounts sender = owner.balance.toNat := by
      simp [ethLedger, Batteries.RBMap.findD, found]
    cases created <;> simp [destructionAccounts, found, ethLedger_insert, debit, old, UInt256.toNat]

/-- Self-destruct cannot create ETH or debit an account other than its owner. -/
theorem destruction_balances (accounts : AccountMap) (sender receiver self : Address) (created : Bool)
    (different : self ≠ sender) (world : worldEth accounts < wordLimit) :
    worldEth (destructionAccounts accounts sender receiver created) ≤ worldEth accounts ∧
    ethLedger accounts self ≤ ethLedger (destructionAccounts accounts sender receiver created) self := by
  by_cases same : receiver = sender
  · subst receiver
    unfold worldEth
    rw [destruction_ledger_self]
    cases created with
    | false => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    | true =>
      simp only [if_true]
      have debitTotal := total_debit (ethLedger accounts) sender (ethLedger accounts sender) (Nat.le_refl _)
      refine ⟨by omega, ?_⟩
      simp [debit, Function.update_of_ne different]
  · let senderWord := (accounts.findD sender default).balance
    have ledger : ethLedger (destructionAccounts accounts sender receiver created) =
        ethLedger (sendEth receiver sender senderWord true accounts) := by
      rw [destruction_ledger_ne accounts sender receiver created same world,
        sendEth_ledger_ne accounts receiver sender senderWord same (Nat.le_refl _) world]
      rfl
    constructor
    · unfold worldEth
      rw [ledger]
      exact Nat.le_of_eq (sendEth_world accounts receiver sender senderWord true (Nat.le_refl _) world)
    · rw [ledger]
      exact sendEth_other_balance accounts receiver sender self senderWord true different (Nat.le_refl _) world

/-- The actual opcode preserves the ETH bound and protects every other account's balance. -/
theorem selfdestruct_step_balances {before after : Ethereum.State} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} (self : Address)
    (different : self ≠ before.executionEnv.codeOwner)
    (world : worldEth before.accountMap < wordLimit)
    (run : step gasCost (.System .SELFDESTRUCT, arg) before = .ok after) :
    worldEth after.accountMap ≤ worldEth before.accountMap ∧
    ethLedger before.accountMap self ≤ ethLedger after.accountMap self := by
  obtain ⟨receiver, accounts⟩ := selfdestruct_accounts run
  rw [accounts]
  exact destruction_balances _ _ _ _ _ different world

end Rollup.EVM
