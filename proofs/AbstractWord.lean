import proofs.support.AbstractWord
import Reasoning.Stepping

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Exact unary evaluation and unrestricted output both include the EVM result. -/
theorem abstract_unary_sound (operation : UInt256 → UInt256)
    {abstract : AbstractWord} {actual : UInt256} (known : abstract.denotes actual) :
    (AbstractWord.unary operation abstract).denotes (operation actual) := by
  cases abstract <;> simp_all [AbstractWord.unary, AbstractWord.denotes]

/-- Exact binary evaluation includes the EVM result for all represented inputs. -/
theorem abstract_binary_sound (operation : UInt256 → UInt256 → UInt256)
    {left right : AbstractWord} {actualLeft actualRight : UInt256}
    (knownLeft : left.denotes actualLeft) (knownRight : right.denotes actualRight) :
    (AbstractWord.binary operation left right).denotes (operation actualLeft actualRight) := by
  cases left <;> cases right <;> simp_all [AbstractWord.binary, AbstractWord.denotes]

/-- A nonzero value makes ISZERO return zero. -/
theorem abstract_isZero_sound {abstract : AbstractWord} {actual : UInt256}
    (known : abstract.denotes actual) :
    abstract.isZero.denotes (UInt256.isZero actual) := by
  cases abstract with
  | exact value => exact congrArg UInt256.isZero known
  | nonzero => exact Reasoning.Theory.isZero_eq_zero_of_ne known
  | any => trivial

/-- A read of the lock slot is nonzero while the lock is set. -/
theorem abstract_lockedLoad_sound {abstract : AbstractWord} {slot value : UInt256}
    (known : abstract.denotes slot) (locked : slot = ⟨6⟩ → value ≠ ⟨0⟩) :
    abstract.lockedLoad.denotes value := by
  cases abstract with
  | exact expected =>
    change slot = expected at known
    subst slot
    by_cases same : expected = ⟨6⟩
    · simpa [AbstractWord.lockedLoad, same, AbstractWord.denotes] using locked same
    · simp [AbstractWord.lockedLoad, same, AbstractWord.denotes]
  | nonzero => trivial
  | any => trivial

end Rollup.EVM
