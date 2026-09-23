import proofs.support.FrameCertificate
import proofs.AccountOperations

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- The frame invariant holds at each continuing instruction boundary. -/
theorem frame_certificate_continuing {jumps : Array UInt256}
    (certificate : AccountFrameCertificate jumps) {start current : Ethereum.State}
    (initial : certificate.accepts start) (trace : ContinuingPrefix jumps start current) :
    certificate.accepts current ∧ current.accountMap = start.accountMap := by
  induction trace with
  | initial => exact ⟨initial, rfl⟩
  | @next before after earlier run ih =>
    have fixed := account_preserving_instruction (certificate.operation before ih.1) rfl run
    exact ⟨certificate.continues before after ih.1 run, fixed.trans ih.2⟩

/-- A certified frame preserves accounts even after its last instruction. -/
theorem frame_certificate_instruction {jumps : Array UInt256}
    (certificate : AccountFrameCertificate jumps) {start current : Ethereum.State}
    (initial : certificate.accepts start) (trace : InstructionPrefix jumps start current) :
    current.accountMap = start.accountMap := by
  cases trace with
  | current earlier => exact (frame_certificate_continuing certificate initial earlier).2
  | afterStep earlier run =>
    have ih := frame_certificate_continuing certificate initial earlier
    exact (account_preserving_instruction (certificate.operation _ ih.1) rfl run).trans ih.2

/-- A certified instruction cannot enter a child call or creation. -/
theorem frame_certificate_no_child {jumps : Array UInt256}
    (certificate : AccountFrameCertificate jumps) {before child : Ethereum.State}
    (accepted : certificate.accepts before) :
    ¬ ChildCallEntry jumps before child ∧ ¬ ChildCreationEntry jumps before child := by
  constructor
  · intro entered
    cases entered with
    | @entered op arg checked cost site code instruction precheck arguments enabled selected =>
      have neutral := certificate.operation before accepted
      rw [instruction] at neutral
      have absent := (account_preserving_no_child
        { checked with executionEnv.depth := before.executionEnv.depth } cost op neutral).1
      rw [absent] at arguments
      cases arguments
  · intro entered
    cases entered with
    | @entered op arg checked cost site instruction precheck arguments nonce allowed =>
      have neutral := certificate.operation before accepted
      rw [instruction] at neutral
      have absent := (account_preserving_no_child
        { checked with executionEnv.depth := before.executionEnv.depth } 0 op neutral).2
      rw [absent] at arguments
      cases arguments

/-- All active prefixes of a certified frame preserve its incoming accounts. -/
theorem frame_certificate_active (start current : Ethereum.State)
    (certificate : AccountFrameCertificate (D_J start.executionEnv.code 0))
    (initial : certificate.accepts start) (trace : ActivePrefix start current) :
    current.accountMap = start.accountMap := by
  cases trace with
  | within earlier => exact frame_certificate_instruction certificate initial earlier
  | call earlier entered childTrace =>
    exact ((frame_certificate_no_child certificate
      (frame_certificate_continuing certificate initial earlier).1).1 entered).elim
  | creation earlier entered childTrace =>
    exact ((frame_certificate_no_child certificate
      (frame_certificate_continuing certificate initial earlier).1).2 entered).elim

end Rollup.EVM
