import proofs.support.AbstractWord

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A program counter and stack description for one instruction boundary. -/
structure AbstractCursor where
  pc : UInt256
  stack : Stack AbstractWord
  deriving DecidableEq

namespace AbstractCursor

def denotes (cursor : AbstractCursor) (state : Ethereum.State) : Prop :=
  state.machineState.pc = cursor.pc ∧ AbstractStackDenotes cursor.stack state.machineState.stack

def advance (cursor : AbstractCursor) (stack : List AbstractWord) (width : Nat := 1) : AbstractCursor :=
  ⟨cursor.pc + UInt256.ofNat width, stack⟩

def push (cursor : AbstractCursor) (value : AbstractWord) (width : Nat := 1) : AbstractCursor :=
  cursor.advance (value :: cursor.stack) width

def unary (cursor : AbstractCursor) (operation : AbstractWord → AbstractWord) : Option AbstractCursor := do
  let (rest, value) ← cursor.stack.pop
  pure (cursor.advance (operation value :: rest))

def binary (cursor : AbstractCursor) (operation : AbstractWord → AbstractWord → AbstractWord) : Option AbstractCursor := do
  let (rest, left, right) ← cursor.stack.pop2
  pure (cursor.advance (operation left right :: rest))

def drop (cursor : AbstractCursor) (count : Nat) : Option AbstractCursor :=
  if count ≤ cursor.stack.length then some (cursor.advance (cursor.stack.drop count)) else none

def duplicate (cursor : AbstractCursor) (index : Nat) : Option AbstractCursor := do
  let value ← cursor.stack[index]?
  pure (cursor.push value)

def exchange (cursor : AbstractCursor) (index : Nat) : Option AbstractCursor := do
  let first ← cursor.stack[0]?
  let other ← cursor.stack[index]?
  pure (cursor.advance ((cursor.stack.set 0 other).set index first))

def jump (cursor : AbstractCursor) : Option AbstractCursor := do
  let (rest, .exact destination) ← cursor.stack.pop | none
  pure ⟨destination, rest⟩

def jumpIf (cursor : AbstractCursor) : Option (List AbstractCursor) := do
  let (rest, .exact destination, condition) ← cursor.stack.pop2 | none
  let taken : AbstractCursor := ⟨destination, rest⟩
  let fallthrough := cursor.advance rest
  pure <| match condition with
    | .exact value => if value = ⟨0⟩ then [fallthrough] else [taken]
    | .nonzero => [taken]
    | .any => [taken, fallthrough]

/-- Unsupported instructions return none. A halting instruction has no successors. -/
def successors (cursor : AbstractCursor) (op : Operation) (arg : Option (UInt256 × Nat)) :
    Option (List AbstractCursor) :=
  match op with
  | .STOP | .RETURN | .REVERT | .INVALID => some []
  | .PUSH0 => some [cursor.push (.exact ⟨0⟩)]
  | .Push _ => do
    let (value, width) ← arg
    pure [cursor.push (.exact value) (width + 1)]
  | .ADD => (cursor.binary (AbstractWord.binary UInt256.add)).map List.singleton
  | .SUB => (cursor.binary (AbstractWord.binary UInt256.sub)).map List.singleton
  | .LT => (cursor.binary (AbstractWord.binary UInt256.lt)).map List.singleton
  | .GT => (cursor.binary (AbstractWord.binary UInt256.gt)).map List.singleton
  | .SLT => (cursor.binary (AbstractWord.binary UInt256.slt)).map List.singleton
  | .EQ => (cursor.binary (AbstractWord.binary UInt256.eq)).map List.singleton
  | .AND => (cursor.binary (AbstractWord.binary UInt256.land)).map List.singleton
  | .SHL => (cursor.binary (AbstractWord.binary (flip UInt256.shiftLeft))).map List.singleton
  | .SHR => (cursor.binary (AbstractWord.binary (flip UInt256.shiftRight))).map List.singleton
  | .ISZERO => (cursor.unary AbstractWord.isZero).map List.singleton
  | .CALLVALUE | .CALLDATASIZE => some [cursor.push .any]
  | .CALLDATALOAD | .MLOAD => (cursor.unary (fun _ => .any)).map List.singleton
  | .KECCAK256 => (cursor.binary (fun _ _ => .any)).map List.singleton
  | .SLOAD => (cursor.unary AbstractWord.lockedLoad).map List.singleton
  | .MSTORE => (cursor.drop 2).map List.singleton
  | .POP => (cursor.drop 1).map List.singleton
  | .JUMP => cursor.jump.map List.singleton
  | .JUMPI => cursor.jumpIf
  | .JUMPDEST => some [cursor.advance cursor.stack]
  | .DUP1 => (cursor.duplicate 0).map List.singleton
  | .DUP2 => (cursor.duplicate 1).map List.singleton
  | .DUP3 => (cursor.duplicate 2).map List.singleton
  | .DUP4 => (cursor.duplicate 3).map List.singleton
  | .DUP5 => (cursor.duplicate 4).map List.singleton
  | .DUP6 => (cursor.duplicate 5).map List.singleton
  | .DUP7 => (cursor.duplicate 6).map List.singleton
  | .DUP8 => (cursor.duplicate 7).map List.singleton
  | .DUP9 => (cursor.duplicate 8).map List.singleton
  | .DUP10 => (cursor.duplicate 9).map List.singleton
  | .DUP11 => (cursor.duplicate 10).map List.singleton
  | .DUP12 => (cursor.duplicate 11).map List.singleton
  | .DUP13 => (cursor.duplicate 12).map List.singleton
  | .DUP14 => (cursor.duplicate 13).map List.singleton
  | .DUP15 => (cursor.duplicate 14).map List.singleton
  | .DUP16 => (cursor.duplicate 15).map List.singleton
  | .SWAP1 => (cursor.exchange 1).map List.singleton
  | .SWAP2 => (cursor.exchange 2).map List.singleton
  | .SWAP3 => (cursor.exchange 3).map List.singleton
  | .SWAP4 => (cursor.exchange 4).map List.singleton
  | .SWAP5 => (cursor.exchange 5).map List.singleton
  | .SWAP6 => (cursor.exchange 6).map List.singleton
  | .SWAP7 => (cursor.exchange 7).map List.singleton
  | .SWAP8 => (cursor.exchange 8).map List.singleton
  | .SWAP9 => (cursor.exchange 9).map List.singleton
  | .SWAP10 => (cursor.exchange 10).map List.singleton
  | .SWAP11 => (cursor.exchange 11).map List.singleton
  | .SWAP12 => (cursor.exchange 12).map List.singleton
  | .SWAP13 => (cursor.exchange 13).map List.singleton
  | .SWAP14 => (cursor.exchange 14).map List.singleton
  | .SWAP15 => (cursor.exchange 15).map List.singleton
  | .SWAP16 => (cursor.exchange 16).map List.singleton
  | _ => none

end AbstractCursor
end Rollup.EVM
