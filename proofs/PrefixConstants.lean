import proofs.PrefixReach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Rollup.EVM

/-- PUSH0 carries zero on the exact prefix stack. -/
theorem PCR.push0 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc)
    (decoded : decode code pc = some (.PUSH0, none)) (space : stack.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) (⟨0⟩ :: stack) mem aw rdata acc :=
  ⟨reached.1, prefix_cursor_push0 reached.2 (by simpa only [reached.1] using decoded) space⟩

/-- An immediate PUSH preserves the exact value and instruction width. -/
theorem PCR.pushConst {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (value : UInt256) (width : Nat) (kind : Operation.POp) (nonzero : kind ≠ .PUSH0)
    (reached : PCR code ee target child pc stack mem aw rdata acc)
    (decoded : decode code pc = some (.Push kind, some (value, width))) (space : stack.length + 1 ≤ 1024) :
    PCR code ee target child (pc + UInt256.ofNat (width + 1)) (value :: stack) mem aw rdata acc := by
  refine ⟨reached.1, ?_⟩
  apply prefix_cursor_guarded (op := .Push kind) (arg := some (value, width)) reached.2
    (by simp only [reached.1, decoded, Option.getD_some]) (by simp)
    (fun state => state.machineState.gasAvailable.toNat < 3) (fun state => stPushConst state value width)
  · intro state matched
    rw [reached.1]
    exact pushConst_xstep ((congrArg ExecutionEnv.code matched.1).trans reached.1)
      matched.2.1 nonzero decoded matched.2.2.1 space
  · intro state matched
    exact ⟨matched.1, congrArg (fun pc => pc + UInt256.ofNat (width + 1)) matched.2.1,
      congrArg (List.cons value) matched.2.2.1, matched.2.2.2⟩

/-- JUMPDEST advances the prefix without changing its values. -/
theorem PCR.jumpdest {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc)
    (decoded : decode code pc = some (.JUMPDEST, none)) (space : stack.length ≤ 1024) :
    PCR code ee target child (pc + ⟨1⟩) stack mem aw rdata acc := by
  refine ⟨reached.1, ?_⟩
  apply prefix_cursor_guarded (op := .JUMPDEST) (arg := none) reached.2
    (by simp only [reached.1, decoded, Option.getD_some]) (by decide)
    (fun state => state.machineState.gasAvailable.toNat < 1) stJumpdest
  · intro state matched
    rw [reached.1]
    exact jumpdest_xstep ((congrArg ExecutionEnv.code matched.1).trans reached.1) matched.2.1 decoded
      (by rwa [matched.2.2.1])
  · intro state matched
    exact ⟨matched.1, congrArg (fun pc => pc + ⟨1⟩) matched.2.1, matched.2.2⟩

/-- PUSH1 carries its immediate word along the actual prefix. -/
theorem PCR.push1 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc) (value : UInt256)
    (decoded : decode code pc = some (.Push .PUSH1, some (value, 1))) (space : stack.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨2⟩) (value :: stack) mem aw rdata acc :=
  PCR.pushConst value 1 .PUSH1 (by decide) reached decoded space

/-- PUSH2 carries its immediate word along the actual prefix. -/
theorem PCR.push2 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc) (value : UInt256)
    (decoded : decode code pc = some (.Push .PUSH2, some (value, 2))) (space : stack.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨3⟩) (value :: stack) mem aw rdata acc :=
  PCR.pushConst value 2 .PUSH2 (by decide) reached decoded space

/-- PUSH4 carries its immediate word along the actual prefix. -/
theorem PCR.push4 {code : ByteArray} {ee : ExecutionEnv} {target child : Ethereum.State}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (reached : PCR code ee target child pc stack mem aw rdata acc) (value : UInt256)
    (decoded : decode code pc = some (.Push .PUSH4, some (value, 4))) (space : stack.length + 1 ≤ 1024) :
    PCR code ee target child (pc + ⟨5⟩) (value :: stack) mem aw rdata acc :=
  PCR.pushConst value 4 .PUSH4 (by decide) reached decoded space

end Rollup.EVM
