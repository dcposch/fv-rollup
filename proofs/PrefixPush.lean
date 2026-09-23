import proofs.PrefixGuard

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- PUSH0 advances the exact prefix cursor and cannot hide an earlier gas failure. -/
theorem prefix_cursor_push0 {environment : ExecutionEnv} {target child : Ethereum.State}
    {cursor : Cursor} (reached : PrefixCursor environment target child cursor)
    (decoded : decode environment.code cursor.pc = some (.PUSH0, none))
    (space : cursor.stack.length + 1 ≤ 1024) :
    PrefixCursor environment target child
      { cursor with pc := cursor.pc + ⟨1⟩, stack := ⟨0⟩ :: cursor.stack } := by
  apply prefix_cursor_guarded (op := .PUSH0) (arg := none) reached
    (by simp only [decoded, Option.getD_some]) (by decide)
    (fun state => state.machineState.gasAvailable.toNat < 2) stPush0
  · intro state matched
    exact push0_xstep (by rw [matched.1]) matched.2.1 decoded matched.2.2.1 space
  · intro state matched
    rcases matched with ⟨environmentEq, pc, stack, memory, words, data, accounts⟩
    exact ⟨environmentEq, congrArg (fun x => x + ⟨1⟩) pc,
      congrArg (List.cons (⟨0⟩ : UInt256)) stack, memory, words, data, accounts⟩

/-- PUSH1 carries its immediate value on the exact prefix stack. -/
theorem prefix_cursor_push1 {environment : ExecutionEnv} {target child : Ethereum.State}
    {cursor : Cursor} (value : UInt256) (reached : PrefixCursor environment target child cursor)
    (decoded : decode environment.code cursor.pc = some (.Push .PUSH1, some (value, 1)))
    (space : cursor.stack.length + 1 ≤ 1024) :
    PrefixCursor environment target child
      { cursor with pc := cursor.pc + ⟨2⟩, stack := value :: cursor.stack } := by
  apply prefix_cursor_guarded (op := .Push .PUSH1) (arg := some (value, 1)) reached
    (by simp only [decoded, Option.getD_some]) (by decide)
    (fun state => state.machineState.gasAvailable.toNat < 3) (fun state => stPush1 state value)
  · intro state matched
    exact push1_xstep (by rw [matched.1]) matched.2.1 decoded matched.2.2.1 space
  · intro state matched
    rcases matched with ⟨environmentEq, pc, stack, memory, words, data, accounts⟩
    exact ⟨environmentEq, congrArg (fun x => x + ⟨2⟩) pc,
      congrArg (List.cons value) stack, memory, words, data, accounts⟩

end Rollup.EVM
