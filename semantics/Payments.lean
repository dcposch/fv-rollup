import semantics.Bindings

namespace Rollup.EVM

def withdrawalPrelude : List Solm.Stmt := contract.transitions[2]!.body.take 6
def withdrawalPostlude : List Solm.Stmt := contract.transitions[2]!.body.drop 7

/-- Record the actual successful EVM call between the withdrawal's two source blocks. -/
def WithdrawalPayment (evm out : Ethereum.State) (locals : Solm.Store) (frame : Solm.Frame)
    (owner : Address) (amount : Nat) : Prop :=
  ∃ middle before after data,
    Solm.ExecBlock config ⟨contract, locals⟩ evm withdrawalPrelude (.ok middle before) ∧
    Solm.evalExpr? config middle before (.var "owner") = .ok (.address owner) ∧
    Solm.evalExpr? config middle before (.var "amount") = .ok (.int amount) ∧
    Solm.callViaEVM before owner amount ByteArray.empty (true, after, data) ∧
    Solm.ExecBlock config
      { middle with locals := (middle.locals.insert "success" (.bool true)).insert "_data" (.bytes data) }
      after withdrawalPostlude (.ok frame out)

def PaymentBound (evm out : Ethereum.State) (locals : Solm.Store) (frame : Solm.Frame)
    (entry : Entry) : Prop :=
  match entry with
  | .withdrawPendingBalance owner amount => WithdrawalPayment evm out locals frame owner amount
  | _ => True

end Rollup.EVM
