import proofs.support.AbstractCursor
import proofs.AbstractWord

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Abstract binary evaluation includes the concrete EVM stack result. -/
theorem abstract_execBinOp {cursor next : AbstractCursor} {before after : Ethereum.State}
    (operation : UInt256 → UInt256 → UInt256) (represented : cursor.denotes before)
    (advance : cursor.binary (AbstractWord.binary operation) = some next)
    (run : execBinOp operation before = .ok after) : next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.binary, Stack.pop2] at advance
  | @cons left actualLeft rest actualRest leftKnown tail =>
    cases tail with
    | nil => simp [AbstractCursor.binary, Stack.pop2] at advance
    | @cons right actualRight rest actualRest rightKnown tail =>
      simp only [AbstractCursor.binary, Stack.pop2, bind, Option.bind, pure] at advance
      cases Option.some.inj advance
      simp only [execBinOp, stackEq, Stack.pop2, Id.run] at run
      cases Except.ok.inj run
      constructor
      · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
          AbstractCursor.advance] using congrArg (fun value => value + UInt256.ofNat 1) counter
      · exact List.Forall₂.cons (abstract_binary_sound operation leftKnown rightKnown) tail

/-- Abstract unary evaluation includes the concrete EVM stack result. -/
theorem abstract_execUnOp {cursor next : AbstractCursor} {before after : Ethereum.State}
    (operation : UInt256 → UInt256) (abstractOperation : AbstractWord → AbstractWord)
    (sound : ∀ abstract actual, abstract.denotes actual → (abstractOperation abstract).denotes (operation actual))
    (represented : cursor.denotes before) (advance : cursor.unary abstractOperation = some next)
    (run : execUnOp operation before = .ok after) : next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.unary, Stack.pop] at advance
  | @cons value actualValue rest actualRest known tail =>
    simp only [AbstractCursor.unary, Stack.pop, bind, Option.bind, pure] at advance
    cases Option.some.inj advance
    simp only [execUnOp, stackEq, Stack.pop, Id.run] at run
    cases Except.ok.inj run
    constructor
    · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        AbstractCursor.advance] using congrArg (fun value => value + UInt256.ofNat 1) counter
    · exact List.Forall₂.cons (sound value actualValue known) tail

/-- The concrete lock read agrees with the abstract nonzero result. -/
theorem abstract_execSload {cursor next : AbstractCursor} {before after : Ethereum.State}
    (represented : cursor.denotes before) (locked : (before.sload ⟨6⟩).2 ≠ ⟨0⟩)
    (advance : cursor.unary AbstractWord.lockedLoad = some next)
    (run : unaryStateOp Ethereum.State.sload before = .ok after) : next.denotes after := by
  rcases cursor with ⟨pc, abstract⟩
  rcases represented with ⟨counter, relation⟩
  change List.Forall₂ AbstractWord.denotes abstract before.machineState.stack at relation
  generalize stackEq : before.machineState.stack = actual at relation
  cases relation with
  | nil => simp [AbstractCursor.unary, Stack.pop] at advance
  | @cons value actualValue rest actualRest known tail =>
    simp only [AbstractCursor.unary, Stack.pop, bind, Option.bind, pure] at advance
    cases Option.some.inj advance
    simp only [unaryStateOp, stackEq, Stack.pop, Id.run] at run
    cases Except.ok.inj run
    constructor
    · simpa only [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
        Ethereum.State.sload, Ethereum.State.addAccessedStorageKey, AbstractCursor.advance]
        using congrArg (fun value => value + UInt256.ofNat 1) counter
    · exact List.Forall₂.cons (abstract_lockedLoad_sound known (by
        intro same
        rw [same]
        exact locked)) tail

end Rollup.EVM
