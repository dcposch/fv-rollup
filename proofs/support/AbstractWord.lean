import semantics.Semantics

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- A stack value can be fixed, known to be nonzero, or unrestricted. -/
inductive AbstractWord where
  | exact (value : UInt256)
  | nonzero
  | any
  deriving DecidableEq

namespace AbstractWord

def denotes : AbstractWord → UInt256 → Prop
  | .exact value, actual => actual = value
  | .nonzero, actual => actual ≠ ⟨0⟩
  | .any, _ => True

def unary (operation : UInt256 → UInt256) : AbstractWord → AbstractWord
  | .exact value => .exact (operation value)
  | _ => .any

def binary (operation : UInt256 → UInt256 → UInt256) : AbstractWord → AbstractWord → AbstractWord
  | .exact left, .exact right => .exact (operation left right)
  | _, _ => .any

def isZero : AbstractWord → AbstractWord
  | .exact value => .exact (UInt256.isZero value)
  | .nonzero => .exact ⟨0⟩
  | .any => .any

def lockedLoad : AbstractWord → AbstractWord
  | .exact slot => if slot = ⟨6⟩ then .nonzero else .any
  | _ => .any

end AbstractWord

/-- Match a complete abstract stack to the concrete stack. -/
def AbstractStackDenotes (abstract : List AbstractWord) (actual : Stack UInt256) : Prop :=
  List.Forall₂ AbstractWord.denotes abstract actual

end Rollup.EVM
