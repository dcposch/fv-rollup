import proofs.WorldExecution
import proofs.WorldCreationTransfers
import proofs.WorldStorage

open Ethereum Ethereum.EVM

set_option maxRecDepth 2048

namespace Rollup.EVM

/-- Creation starts with the sender's incremented nonce. -/
def ProtectedCreationBalances (self : Address) (depth : Fin 1025) : Prop :=
  ∀ blobs cA gh bl accounts original substate sender origin gas price value init salt header writable
    address cA' after gas' substate' accepted output,
    self ≠ sender → (accounts.findD sender default).nonce ≠ ⟨0⟩ →
    value.toNat ≤ ethLedger accounts sender → LockedWorld self accounts →
    Lambda blobs cA gh bl accounts original substate sender origin gas price value init depth salt
      header writable = (address, cA', after, gas', substate', accepted, output) →
    EthFrame self accounts after

/-- Creation preserves balances if its code execution preserves balances. -/
theorem protected_creation_balances_of_steps {self : Address} {depth : Fin 1025}
    (steps : ForeignStepBalances self depth) : ProtectedCreationBalances self depth := by
  intro blobs cA gh bl accounts original substate sender origin gas price value init salt header writable
    address cA' after gas' substate' accepted output foreignSender nonce funds initial run
  have pinned := LockedWorld.pinned initial
  have world := LockedWorld.bounded initial
  unfold Lambda at run
  simp at run
  split at run <;> rename_i execute
  · simp at run
    rcases run with ⟨_, _, same, _, _, _, _⟩
    rw [← same]
    exact EthFrame.refl self accounts
  · simp at run
    rcases run with ⟨_, _, same, _, _, _, _⟩
    rw [← same]
    exact EthFrame.refl self accounts
  · rename_i _ finalCreated finalAccounts finalGas finalSubstate returnedData
    simp at run
    rcases run with ⟨computed, _, same, _, _, _, _⟩
    split_ifs at same with rejected
    · rw [← same]
      exact EthFrame.refl self accounts
    · simp only [computed] at rejected execute same
      have newSender : address ≠ sender := by
        intro collision
        have rejected' := rejected
        rw [collision] at rejected'
        cases found : accounts.find? sender with
        | none =>
          simp only [Batteries.RBMap.findD, found, Option.getD_none] at nonce
          exact nonce rfl
        | some account =>
          have nonzero : account.nonce ≠ ⟨0⟩ := by
            simpa [Batteries.RBMap.findD, found] using nonce
          simp [found, nonzero] at rejected'
      have foreign : self ≠ address := by
        intro collision
        have rejected' := rejected
        rw [← collision] at rejected'
        obtain ⟨account, found, code⟩ := pinned_account_present pinned
        have nonempty : runtimeBytecode ≠ ByteArray.empty := by decide +kernel
        simp [found, code, nonempty] at rejected'
      have transfer : EthFrame self accounts (sendEthCreate address sender value true accounts) :=
        ⟨(sendEthCreate_world_ne accounts address sender value true newSender funds world).le,
          sendEthCreate_other_balance accounts address sender self value true newSender
            foreignSender funds world⟩
      have storage : CodeStorageFrame self accounts (sendEthCreate address sender value true accounts) :=
        sendEthCreate_static_state address sender value true accounts self
      have transferred := initial.next storage transfer
      let existent := accounts.findD address default
      let collision : Bool := existent.nonce ≠ ⟨0⟩ || existent.code.size ≠ 0 || existent.storage != default
      let environment : ExecutionEnv := {
        codeOwner := address, sender := origin, source := sender, weiValue := value,
        calldata := default, code := if collision then ⟨#[0xfe]⟩ else init,
        gasPrice := price.toNat, header := header, depth := depth, perm := writable,
        blobVersionedHashes := blobs }
      have execution : EthFrame self (sendEthCreate address sender value true accounts) finalAccounts := by
        apply foreign_xi_balances (env := environment)
          (cA := if collision then cA else cA.insert address) (gh := gh) (bl := bl)
          (original := original) (gas := gas) (substate := substate.addAccessedAccount address)
          (cA' := finalCreated) (gas' := finalGas) (substate' := finalSubstate)
          (output := returnedData) steps foreign transferred
        simpa [sendEthCreate, environment, collision, existent, apply_ite] using execute
      have installed := ethLedger_insert_same_balance finalAccounts address
        { (finalAccounts.findD address default) with code := returnedData } rfl
      rw [← same]
      simpa only [EthFrame, worldEth, installed] using transfer.trans execution

end Rollup.EVM
