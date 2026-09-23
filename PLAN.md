# Complete the rollup proofs

Keep the current ETH contract and EquiVM. Prove the eight README claims for the
pinned bytecode. Keep L2 validity as an external trust condition. ZK verification,
queues, upgrades, emergency exits, and deployment monitoring remain out of scope.

## Status

Steps 1–6 are complete. `deployed_contract_correct` proves the final deployment,
transaction, call-label, and active-payment target. `contract_verification_complete`
requires the source, constructor, bytecode, and trace results at their exact types.
The full check passed: seven dependency tests, compiler output, 16 Solidity tests,
all Lean modules, ABI comparisons, and 1,031 named theorem audits. The audits use
only the three allowed logical axioms. The trust review is in `invariants/README.md`.
Older checkpoints below record the prior open obligations.

## README review

Keep the opening goal: a toy formally-verified rollup. Describe the intended
invariants upfront. State the current proof status in the TODO section below.
Complete the proofs as planned.

The remaining factual corrections are:

| Location | Correction |
| --- | --- |
| Contract checklist | Replace "withdrawal queue" with "withdrawal balances". Neither deposits nor withdrawals use a queue. |
| ZK checklist | Use a scope statement: "No ZK verifier. Trust the sequencer to submit valid L2 transitions." This is not a task in this plan. |
| Deposit and batch descriptions | Use "deposit credit". A batch consumes credit from at most one account and adds withdrawal credit to at most one account. Credit can combine several deposits. |
| Custody | State that the boundary equation holds between calls. During a callback, add ETH in flight. Forced ETH is surplus. |
| Isolation | Say "Change only the specified account credits." Batches also change shared backing, the root, and the batch number. |
| Tool versions | Say "Lean, library dependencies, solc, and compiler settings are pinned." Foundry and Python are not pinned. |

`source_refines_model` now proves `SourceRefinesModel` for all runtime entries.
`source_custody` uses that proof directly. The final EVM trace theorem and its
completion gate now pass. The review covers theorem hypotheses and dependency lists.

## 1. Fix the proof statements

Change `semantics/Model.lean`, `invariants/Invariants.lean`, and `invariants/Obligations.lean` first.

- Define call labels with the caller, value, selected function, and arguments.
  Define success, rejection, and exceptional outcomes.
- Replace arbitrary model reachability in `SourceRefinesModel` with a relation
  for the actual call. Include exact credit changes, return values, and permitted
  writes. Bind batch authorization to the actual caller.
- Record the ETH payment target and amount. A recipient can forward ETH during
  its callback, so its final balance alone does not identify the payment.
- Replace global `NoStorageCollision` with explicit non-alias conditions for the
  finite set of storage accesses in a trace. Include fixed slots, both mappings,
  and zero-address accesses made by empty batches. Extend the set on new accesses.
- Change the storage relation with this assumption. Track logical credit support
  and prove that untracked accounts have zero logical credit. Do not sum a raw
  physical-storage projection over all addresses under a finite-slot assumption.
- State the EVM world conditions needed for ETH balance bounds, code ownership,
  and fresh deployment. Prove preservation of those conditions where applicable.
- State the final trace theorem now. Separate mathematical premises from imported
  semantic trust. Do not assume callback isolation or either refinement theorem.

Done when the statements compile, current model proofs still pass, and a review
can match each README claim to a named theorem target. No proof may obtain its
conclusion by assuming the security property it is meant to establish.

## 2. Complete the first implementation proof

Start with deployment and `deposit`. Add separate proof files for the constructor,
deposit, storage operations, and shared bytecode routines.

- Prove `ConstructorInitializes` from fresh storage. Include a nonzero sequencer,
  the supplied root, zero credit and backing, an unlocked state, and pre-funded ETH.
- Prove creation-bytecode refinement and installation of the pinned runtime code.
- Prove the exact source-level deposit effect and its rejection paths.
- Prove deposit-bytecode refinement, including argument decoding, call value,
  owner checks, checked addition, storage writes, and lock release.
- Prove preservation for account maps related by EquiVM's equivalence relation.

Done when a constructor-and-deposit theorem connects actual EVM execution to
custody and account-credit effects. Include a checked successful execution
witness so this milestone cannot consist only of failure paths.

## 3. Prove batches, getters, and dispatch

Add source and bytecode proofs for `executeBatch` and the six public getters.

- Cover sequencer checks, root continuity, the next batch number, canonical empty
  effects, credit consumption, backing limits, withdrawal credit, and overflow.
- Prove exact writes and unchanged account credits. Include coincident deposit
  and withdrawal owners. Prove that an accepted batch cannot be replayed after
  later accepted calls.
- Cover getter return values and storage preservation.
- Cover unknown selectors, short or malformed arguments, invalid address words,
  unexpected ETH on nonpayable functions, and failed checks after earlier writes.
- Use per-entry proofs to assemble the runtime dispatcher proof.

Done when these functions have complete source-to-model and bytecode-to-source
proofs, with no open correctness premises for their bodies.

## 4. Prove withdrawal and arbitrary callbacks

This is the main semantic proof task. Reuse the existing guard lemmas and EVMLean
account-locality and static-storage results where their hypotheses apply.

- Prove from the runtime bytecode that, while the lock is set, all mutating entry
  points reject. Getters preserve storage. Include arbitrary calldata, callers,
  call chains, and static calls.
- Prove that arbitrary receiver execution can affect rollup storage only through
  execution in the rollup's storage context. Show that its code cannot be replaced
  or destroyed through the available entry points.
- Connect this result to the actual EVM external-call semantics. Use a justified
  induction over execution or calls. Do not assume that callbacks are harmless,
  and do not use withdrawal correctness to prove itself.
- Show that a successful callback preserves protected storage and permits only
  surplus ETH changes at the rollup. Derive the abstract `Callback` relation.
- Prove the payment target, payment amount, credit bounds, transfer-before-debit
  order, final debit, and lock release.
- Cover receiver revert, insufficient balance, depth limits, exceptional halts,
  and out-of-gas. Restore rollup funds and storage, and reverted subtree effects,
  at the correct call boundary. Transaction gas charges are not rolled back.
- Prove withdrawal-bytecode refinement using the actual external-call result.

Done when withdrawal correctness holds for arbitrary receiver code under the
stated EVM assumptions. Callback isolation must be a proved lemma, not a premise
supplied by the user of the final theorem.

## 5. Compose the full result

Replace the conditional result in `proofs/Composition.lean` with final theorems.

- Discharge `BytecodeCorrect`, `ConstructorInitializes`, and the revised source
  refinement obligations with actual proofs.
- Connect EVM call and transaction boundaries to the labeled model. Account for
  incoming call value once, forced ETH, failed calls, and transaction rollback.
- Check static-call handling and relevant substate effects separately where the
  EquiVM equivalence relation does not cover them. Its out-of-gas branch alone
  does not establish rollback or successful execution.
- Prove all eight README claims over arbitrary finite traces from deployment.
  Export custody at completed-call boundaries and the reservation invariant
  during payment. Export authorization and exact effects using the call labels.
- Keep L2 ownership, root validity, and availability outside the theorem. Do not
  assume an honest sequencer merely to prove aggregate custody accounting.

Done when the final theorem refers to the pinned creation and runtime bytecode
and has no open implementation-correctness or callback-correctness premise.
Explicit finite-trace non-alias and EVM environment conditions remain visible.

## 6. Make completion enforceable

Update `proofs/Audit.lean` and `scripts/check.py` after composition.

- Require the final theorem at its exact intended type. A declared proposition
  or a theorem with an extra refinement premise must not satisfy this check.
- Audit every exported security theorem and its dependency axioms. Inspect theorem
  hypotheses as well as axiom lists.
- Scan proof files recursively. Use expected theorem names, not a fixed count of
  audit messages. Reject missing proofs and unreviewed trust additions.
- Inspect EquiVM's selector, hash, precompile, and native-evaluation dependencies
  before approving them. Do not add a general axiom allowlist to make a build pass.
- Give Keccak an executable Lean definition in a pinned dependency patch.
  The current EVMLean definition is opaque. EquiVM uses it to compute source
  selectors, so the kernel cannot yet check those selectors against the bytecode.
  Prove the fixed selector values without adding native-evaluation trust.
  Evaluate [Nethermind's LeanCrypto implementation](https://github.com/NethermindEth/LeanCrypto/blob/cc4937cdcab1229fa375964fbcfae82b95576ed8/LeanCrypto/Primitives/HashFunctions/Keccak256.lean).
  Check its Lean version, hash test vectors, and kernel reduction before use.
- Keep compiler-output checks and the existing Solidity tests. Add focused tests
  only for behavior gaps found during the proof work.
- Update the README status and remove its proof TODOs only after this check passes.

Done when one command verifies the completed contract proof and its explicit
trust boundary. Passing model tests or model proofs alone must not pass that gate.

## Order and checkpoints

Run 1, then 2. Use the completed deployment-and-deposit proof to validate the
approach before extending it. Then run 3 and 4, followed by 5 and 6. Parts of the
source and bytecode work can proceed independently after the statements are fixed.

If the pinned EVM semantics or proof libraries lack a required result, record the
exact lemma and prove it locally or upstream. Do not close a TODO with a new
correctness assumption. The largest uncertainty is the arbitrary-callback proof;
a reliable effort estimate requires completion of the first implementation proof.

## 7. Commit and push

Make a minimal initial commit and push to `origin:master`.

## Work checkpoint

- Added call labels and exact model effects in `semantics/Calls.lean`.
  `semantics/Bindings.lean` binds them to decoded calldata, sender, and value.
- Replaced global slot injectivity with finite access scopes. Proved that scope
  extension cannot create credit. Source refinement now requires exact call effects.
- Proved `constructor_initializes` from the EquiVM source semantics. It preserves
  pre-funded ETH.
- Proved the exact source deposit effect and all source rejection paths.
  `deposit_source_refines` derives checks from an accepted call and proves the
  full source result, including storage scope, code, and ETH bounds.
- Proved `deposit_equivalence_for` at EquiVM's runtime-equivalence type when
  both dispatchers select deposit. It covers all calldata, successful calls,
  reverts, out-of-gas, and equivalent account maps. Source execution now reads
  credit after the lock write, so this implementation proof also covers slot
  aliases. The accounting model still requires its finite non-alias condition.
  `deposit_correct` now proves source dispatch from the literal bytecode selector.
  Its selector hash is checked by Lean's kernel. Static calls remain separate.
- Proved `deposit_evm_custody` from accepted EVM execution. It connects bytecode
  execution, the source deposit effect, and model solvency. It uses the stated
  calldata, account, funding, and finite-storage conditions, without assuming
  `SourceRefinesModel`. `deposit_evm_effect` proves the exact model state change.
  Equivalent account maps preserve the logical projection, storage conditions,
  ETH bound, and code ownership.
- Proved `deposit_bytecode_classification` for the pinned runtime. It covers
  short and malformed calldata, noncanonical addresses, the lock, invalid owners,
  zero ETH, and credit overflow. Valid calls have the exact credit and lock writes.
  Both result branches permit out-of-gas.
- Proved `deposit_xi_success` from an accepted EVM `Ξ` call. It derives every
  deposit check, the exact account-map writes, and empty return data. It assumes
  the literal deposit selector and a writable call, but no body-correctness premise.
  `deposit_success_witness` now proves a successful one-wei execution, its credit,
  its ETH balance, and lock release. Its 188 instruction steps are kernel-checked.
- Proved `constructor_correct` at the full EquiVM `constructorEquivalence` type.
  This covers every argument list accepted by `config.selfDeployment`, packed
  address writes in arbitrary initial storage, and equivalent account maps.
  Both source parameter-store representations are covered. Nonpayable and zero
  sequencer rejection paths are included.
- Proved `deployment_success_code` from the actual EVM `Lambda` creation call.
  Fresh deployment installs the pinned runtime bytes on success. The code-deposit
  gas failure and constructor out-of-gas paths restore the input account map.
- Proved `creation_success_witness` for actual EVM `Ξ` execution. It returns the
  pinned runtime, writes sequencer and root, and leaves enough gas for code
  deposit. Its 118 instruction steps are checked by Lean's kernel.
  The constructor-to-message-call composition remains open.
- Added a proved jump-table scan checker. Bytecode proofs use kernel-checked
  computation. The generated creation bytes share the runtime array to keep
  reduction costs small; compiler-output checks still cover both byte strings.
- Proved `source_payment_bound`: an accepted source withdrawal contains a
  successful EVM call to the decoded owner with the specified value expression.
  The witness includes the source blocks before and after the call. The runtime
  bytecode witness is now proved by `withdrawal_xi_success` below.
- Proved `withdrawal_source_exact`. An accepted source withdrawal passes its
  entry checks, saves credit after the lock write, makes the specified EVM
  payment, debits the saved credit, and unlocks. The prelude and postlude have
  exact execution proofs. Failed entry checks or a failed payment cause source
  rejection. `withdrawal_body_payment` constructs the full source result from
  an actual EVM call result. It does not assume callback isolation.
- Proved the withdrawal bytecode path from dispatch to payment setup. Accepted
  writable calls pass the amount and credit checks. The CALL stack has the
  decoded owner and amount, with empty calldata and a zero output buffer length.
  These path proofs permit out-of-gas. Source and bytecode prelude checks now
  correspond for bound arguments and equivalent account maps. Reads follow
  storage-write order, without a slot-separation premise.
- Proved the withdrawal CALL and return-data paths. Return-data handling permits
  arbitrary returned bytes and tracks memory expansion. Failed payments reject.
  The bytecode debits saved credit and releases the lock after a successful call.
  `withdrawal_xi_success` derives a successful EVM payment witness and the exact
  final account writes from accepted execution. It covers insufficient balance,
  the call-depth limit, and out-of-gas in the path classification.
  `withdrawal_payment_to_source` supplies the same call in the source semantics.
  ABI decoding now binds the owner and amount; invalid lengths and noncanonical
  owners reject. Full source-to-bytecode equivalence is now proved below.
  Callback ETH, code, and storage preservation are proved below from the actual
  call semantics. Source withdrawal model refinement is now proved below.
- The CALL audit exposed precompile-output-size assumptions in EquiVM's generic
  helper. Added `runtime_call_value_made_empty`, a local proof of the same call
  transition without a return-data size conclusion. The withdrawal path does not
  need that conclusion. The full audit passes with the three-axiom gate unchanged.
- Proved `withdrawal_correct` at EquiVM's runtime-equivalence type for writable
  calls. Keep successful and failed EVM call witnesses, including calls not made
  for insufficient balance or depth limits. Transport the call across equivalent
  account maps, then compose the source prelude, payment, debit, and unlock.
  The result covers failed entry checks, malformed calldata, and out-of-gas.
- Proved `runtime_correct` for all nine entry points, short calldata, and unknown
  selectors. `bytecode_correct` combines it with `constructor_correct` and
  discharges `BytecodeCorrect` without an implementation-correctness premise.
  EquiVM's runtime relation covers writable calls. Static-call handling, source
  withdrawal model refinement, and final EVM trace composition remain
  separate obligations. The relation permits out-of-gas and does not prove gas
  sufficiency. The constructor and deposit success witnesses remain in the gate.
- Proved `static_call_preserves_rollup` from EVMLean's static-call semantics.
  Arbitrary static call chains preserve the deployed account's code, persistent
  storage, and transient storage. Writable callback code and storage preservation
  are now proved below. `AccountLocality` permits arbitrary transfer operands,
  so its relation does not establish that callback ETH can only increase. Prove
  that balance property from actual call operands and storage contexts, together
  with preservation of the total ETH bound. The stronger locked-entry proofs
  below no longer require a nested calldata-size bound.
- Proved `getter_source_preserves_state` for all six getters. Accepted source
  calls preserve the full EVM state and local frame. `getter_source_refines`
  proves all six exact model return values and state effects.
- Proved the six getter paths in the pinned runtime. The proofs cover dispatch,
  nonpayable checks, packed address masking, mapping address decoding and hashing,
  exact return bytes, and account preservation. Credit getters reject malformed
  arguments. `getter_xi_preserves_accounts` covers accepted writable and static
  calls, including calls while the lock is set. The shared return routines also
  have bytecode proofs. `getters_correct` now proves full source-to-bytecode
  equivalence for all six getters, including selector correspondence and
  malformed arguments. It covers static and writable calls and equivalent
  account maps. It has no getter-body or source-dispatch correctness premise.
- Proved `runtime_unknown_selector` and `runtime_success_selector`. Unknown
  selectors reject or run out of gas. Every accepted runtime call has one of
  the nine known selectors. Short calldata rejection is also covered.
- Proved `source_selector_bytes` and `source_selector_dispatch` for all nine
  source signatures. Each hash certificate is kernel-checked. Source and
  bytecode rejection also agree for short calldata and unknown selectors.
- Added a pinned EquiVM ABI signature patch. Use total decimal formatting in
  place of the opaque pretty-printer. All contract selectors are proved from
  this model. Runtime comparisons with the upstream printer cover all valid
  integer, fixed-point, and fixed-byte widths, plus representative array lengths.
  The dependency gate checks both package revisions and all managed files before
  any write. Seven gate tests pass. Build hash certificates in pairs and stage
  the large bytecode proof chains to limit memory use. Run the named audit once
  after building the proof modules.
- Proved batch and withdrawal dispatch and argument decoding. The proofs cover
  short calldata, signed length checks, noncanonical addresses, and nonpayable
  rejection. A local `SWAP9` proof closes a missing library step.
  `batch_locked_reject`, `withdrawal_locked_reject`, and `deposit_locked_reject`
  cover all calldata below the EVM word-size bound, for writable and static calls.
  `locked_runtime_xi_preserves_accounts` proves that an accepted call while locked
  has zero context value and preserves all accounts. It has no body-correctness
  or selector premise.
- Proved `locked_message_call_accepted` and `locked_message_call_static_state`
  from EVM message-call semantics. An accepted call into locked runtime code
  changes accounts only through the incoming ETH transfer. All such calls
  preserve code and both storage maps, including failed calls. The stronger
  results below connect these entry points to arbitrary receiver call chains.
- Proved `runtime_dispatch_any` and all three argument-decoder classifications
  directly from the word-sized bytecode guards. They need no calldata-size
  premise. `locked_runtime_xi_preserves_accounts_any` and
  `locked_message_call_static_state_any` extend locked execution and call
  preservation to all calldata. Stage these modules before the full build.
- Proved `callback_preserves_rollup_storage` from actual EVM message calls and
  the account-locality relation. Arbitrary receiver code and call chains preserve
  the locked rollup's code, persistent storage, and transient storage. The initial
  account must contain the pinned runtime and have a nonzero lock. The precompile
  case now uses its actual call semantics, so this storage result needs no address
  exclusion. No callback-safety premise is used. Code presence
  excludes account replacement through the relation's empty-account cases.
- Proved `withdrawal_callback_storage` for the actual source payment call.
  `withdrawal_final_storage_ready` preserves pinned code and the storage scope.
  `withdrawal_final_storage_values` proves the exact credit debit and lock clear
  after arbitrary callbacks, under the existing finite non-alias conditions.
  `CodeStorageFrame.project` fixes all model fields except ETH. The balance
  results below establish the ETH payment bound and callback surplus.
- Added `ethLedger` and `worldEth`, with a proved link to `WorldBounded`.
  Funded transfers to distinct accounts cannot overflow the recipient. `sendEth_world`
  proves total ETH conservation for every message-call transfer outcome, including
  self-transfers. Zero-value transfers preserve every balance. Transfers cannot
  debit an account other than their sender.
- Proved the corresponding creation-transfer ledger and total ETH results when
  the new address differs from the sender. This is the creation prelude, not the
  full CREATE or CREATE2 proof. The results below now connect this prelude to
  both opcodes. Address separation follows from the nonce and final collision
  checks. The opcode increments a nonce only below its 64-bit limit; the passed
  sender nonce is then nonzero.
- Proved `precompiled_call_accounts` from actual precompile calls. Such calls
  either roll back or keep only the incoming transfer. Funded calls conserve ETH.
  `locked_own_call_accounts` gives the same two outcomes for all calls into locked
  rollup code, including precompile addresses. `locked_own_call_balances` proves
  total ETH conservation and nondecrease of the rollup balance for these calls.
- Proved `selfdestruct_step_balances` for the actual SELFDESTRUCT opcode. It cannot
  create ETH or debit an account other than its owner. The proof covers forced
  transfers and the same-address burn rule for newly created accounts.
  `sstore_ethLedger` and `tstore_ethLedger` preserve every ETH balance.
  `local_step_ethLedger` covers all opcodes except calls, creation, and SELFDESTRUCT.
  `precheck_accounts` proves that validation and gas charging preserve accounts.
- Proved `foreign_step_storage`, `foreign_call_storage`, and `foreign_xi_storage`.
  They carry pinned code and the nonzero lock through foreign storage contexts,
  including foreign code selected by CALLCODE and DELEGATECALL.
- Proved `foreign_xstep_balances`, `foreign_x_balances`, and `foreign_xi_balances`.
  These composition lemmas lift an opcode balance result through validation,
  environment restoration, and finite EVM execution. The recursive opcode premise
  is discharged by `foreign_step_balances` below.
- Proved `call_step_balances` for CALL, CALLCODE, DELEGATECALL, and STATICCALL.
  Bind the actual source, receiver, selected code, and funds check. DELEGATECALL
  may name another source account, but transfers zero ETH.
- Proved `creation_step_balances` for CREATE and CREATE2. The nonce update keeps
  all balances, code, and storage. Its checked bound prevents nonce wraparound.
  The final creation check excludes the sender and the pinned rollup as the new
  address. Rollback restores accounts; code installation preserves balances.
- Proved `foreign_step_balances` by induction on remaining call depth. The base
  case proves that calls and creation at depth 1024 preserve balances. Recursive
  calls and creation use the lower-depth result. No callback-correctness premise
  remains. `foreign_execution_balances`, `callback_call_balances`, and
  `callback_creation_balances` establish total ETH nonincrease and nondecrease
  of the locked rollup balance in foreign execution.
- Proved `payment_call_balances` for the rollup's outgoing payment. It covers
  self-payments, precompiles, arbitrary receiver code, and call chains. The total
  ETH bound is preserved; the rollup loses at most the specified amount.
  `source_payment_balances` connects this result to the actual source payment.
  `withdrawal_payment_balances` proves `WorldBounded` after payment and the ETH
  lower bound for a word-sized withdrawal amount.
- Proved `withdrawal_lock_projection` and `withdrawal_credit_model` under the
  finite storage conditions. Lock acquisition preserves the logical accounting
  state. `withdrawal_final_projection` proves the exact credit debit and retains
  the callback's final ETH balance.
- Proved `withdrawal_callback_model`: the actual payment and balance bounds imply
  the abstract `Callback` relation. This closes the callback completeness gap
  used by the source withdrawal proof; it is not a supplied correctness premise.
- Proved `withdrawal_source_refines` and `source_refines_model`. All accepted source
  entries now have their exact labeled model effects. Withdrawal includes the
  actual payment witness, callback surplus, final debit, lock release, and all
  source world conditions. `source_custody` no longer takes a refinement premise.
- Proved `runtime_accepted_source`, `runtime_refines_model`, and
  `runtime_preserves_safe`. Accepted writable execution of the pinned bytecode
  has the matching source execution, labeled model effect, and encoded return
  value. Account-map equivalence carries the storage scope, lock, code, and total
  ETH bound to the actual EVM output. These results use bound calldata and the
  stated initial conditions; they assume no implementation-correctness theorem.
- The full check passed with 470 named theorem audits, including the source and
  runtime composition results above.
- Proved the message-call boundary results in `proofs/MessageRefinement.lean`.
  Actual `toExecute` selection uses the stored runtime outside the precompile
  address set. Incoming ETH is counted once. Successful writable calls preserve
  the boundary conditions and have the exact model effect and return data.
  Rejected calls restore accounts and substate. The results below now extend
  this proof to classified calls in either permission mode.
- Proved finite boundary-scope extension with no new credit. Proved the exact
  deployed account map in `proofs/DeploymentResult.lean`, including both
  constructor writes and code installation. `proofs/DeploymentInitial.lean`
  proves account presence and zero storage at fresh constructor entry.
  These results now feed the deployment model proof below.
- The full check passed with 490 named theorem audits, including the boundary
  and deployment results above.
- Proved `deployment_refines_initial` and `deployment_refines_scope`. Actual
  successful deployment establishes the initial model, storage scope, unlocked
  guard, pinned code, total ETH bound, and model safety. It preserves all ETH
  balances, including pre-funded ETH at the deployment address. The premises
  include fresh storage, a present sender, a nonzero sequencer, and bounded
  total ETH. Finite scope extension requires distinct slots.
- Proved `deployed_message_refines_model`. The first accepted writable message
  starts from that deployed initial state and has the exact labeled model effect.
  It takes no source, bytecode, callback, or initial-safety correctness premise.
  Its calldata binding and finite access-scope premises remain explicit.
- Proved calldata bindings from accepted deposit, batch, and withdrawal bytecode
  in `proofs/AcceptedCallBinding.lean`. These results take the matching selector
  and derive the actual caller, value, and decoded arguments.
- The full check passed with 506 named theorem audits, including deployment
  composition and the three mutating entry bindings above.
- Proved getter bindings and complete accepted-call classification. Actual
  successful bytecode supplies a decoded label; no label-binding premise is
  needed in `message_accepted_refines_model`. `CalldataCovered` states the finite
  scope condition for each decoded entry. Nested-call scope extraction remains
  part of the final trace work.
- Proved that no static mutation can succeed. Its first storage write fails the
  EVM precheck. The proof covers all three entry decoders and both lock states.
  Every successful static call is a getter and preserves all accounts.
- Extended `runtime_accepted_source`, `runtime_refines_model`,
  `message_refines_model`, and deployment-to-message composition to both static
  and writable calls. `runtime_success_equivalence_for` derives source
  correspondence for either mode from actual accepted bytecode execution.
- The full check passed with 529 named theorem audits, including classification
  and static-call composition.
- Added `ExecutionTrace`, `CompletedTraceCorrect`, and
  `DeployedBoundaryTraceCorrect`. Proved both boundary trace targets. Trace steps
  record actual selected EVM message results and funded `sendEth` transfers to
  the rollup. The proof covers static and writable messages, rejected calls,
  exact accepted effects and return data, and preservation of all boundary
  conditions. Custody and word bounds follow over the completed trace.
  The audit checks both targets at their exact types.
- Added `calldataScope` and proved that accepted bytecode has exactly those
  mapping keys. `executionScope` collects the finite set from recorded root
  messages, including rejected messages. `deployed_trace_from_calldata` uses
  that set with an explicit non-alias condition. It needs no supplied decoded
  labels, access-coverage proofs, or implementation-correctness premises.
- These are completed rollup-call traces, not the final full execution-tree
  result. Next, include nested getter reads in the collected scope and connect
  surrounding contract execution, ancestor rollback, and forced-ETH opcodes to
  the boundary trace. Prove the in-flight reservation claims over actual
  execution prefixes. Export all eight claims and require the complete result
  at its exact type in the final gate.
- The full check passed with 542 named theorem audits, including the boundary
  traces and derived root-call scopes.
- Proved instruction-prefix safety for foreign callback frames. The actual
  withdrawal transfer establishes the payment reservation. Storage and ETH
  frame proofs preserve it before and after each completed instruction.
  Nested funded call and creation transfers preserve the same reservation.
- Bound all four call opcodes to their decoded helper arguments and results.
  Proved that their transfer source is the current account, or their transfer
  value is zero. `ChildCallEntry` records instruction decoding, the EVM precheck,
  helper arguments, the call guard, and actual code selection. Its foreign child
  prefixes preserve the payment reservation without a supplied transfer-state
  equality or source-correctness premise.
  This does not yet cover prefixes in the protected rollup's own frame, active
  creation frames, or the full execution tree. Connect those cases and include
  nested getter keys before closing the final trace obligation.
- The full check passed with all 562 named audits, including the 20 prefix and
  child-entry results above.
- Proved `selfdestruct_instruction_refines` from actual instruction decoding,
  validation, and opcode execution. The opcode keeps code and storage and can
  only add rollup surplus. This includes transfers to other beneficiaries and
  the self-beneficiary burn case. Transaction-final account deletion is separate.
- Proved `theta_rejected_checkpoint` for any selected code or precompile. A
  rejected message restores all input accounts and substate, even if descendant
  calls changed them. Added actual self-destruct instructions and rejected
  surrounding messages to `ExecutionTrace`. The expanded deployment-to-boundary
  theorem compiles. Accepted surrounding calls and the full active call tree
  remain open. Gas fees and transaction-final effects still need their boundary.
- The seven new environment lemmas passed a focused axiom audit using only the
  three allowed logical axioms. Added them to the named audit, now 569 results.
- Proved that all local opcodes in a foreign storage context leave the rollup
  account and model unchanged. This covers persistent and transient writes
  without requiring the rollup lock. Instruction validation preserves the same
  boundary conditions.
- Proved `call_instruction_rollup_refines` for actual call instructions from a
  foreign frame into the rollup. Stack decoding supplies the caller, value,
  storage context, and code target. The memory-read semantics supplies the
  calldata bound. The funds and depth guard either enters the proved message
  or leaves accounts unchanged. Success and rejection both refine the model.
  The proof needs only boundary safety, the ordinary-address condition, and
  coverage of the actual child calldata in the finite storage scope.
- Added these 15 results to the audit. The 584-audit run stopped during compilation
  when it picked up the new creation model before its annotation fix below.
  Next, compose calls through other foreign frames and creation frames. Record
  all nested calldata accesses, including getters, and finish protected-frame
  prefixes and transaction-final effects before the final claim bundle.
- Added `CreationCall` with the actual address calculation, collision check,
  endowment, initialization environment, and EVM creation call. Its executable
  fields are marked noncomputable where they depend on the modeled Keccak call.
  Proved that initialization errors and reverts restore the input accounts, and
  that accepted creation has successful initialization and no address collision.
- Proved collision-stub failure and prefix confinement. Initialization cannot
  pass its first invalid instruction. A fresh creation cannot use the pinned
  rollup address or the caller's nonzero nonce account. Fresh initialization
  prefixes preserve a withdrawal reservation after a funded endowment transfer.
  Bind the nonce and funds conditions to CREATE and CREATE2 next. Colliding
  entry-state safety and the full active call tree remain separate obligations.
- The full 599-audit check passed. Compiler output, dependency checks, all 16
  Solidity tests, Lean builds, ABI comparisons, and the axiom audit pass.
- Bound CREATE and CREATE2 to the modeled creation call. The actual opcode guard
  supplies the endowment funds, depth limit, and nonce condition. Both fresh and
  colliding initialization entries preserve the payment reservation. A colliding
  entry cannot execute an instruction or enter another frame.
- Added `ActivePrefix` and the open `CallbackActivePrefixCorrect` target. This
  relation includes nested calls into the locked rollup itself. Completed-call
  results alone do not prove safety at each intermediate instruction.
- Proved that account-preserving opcodes cannot enter a child frame. A generic
  frame certificate now proves account preservation for all active prefixes.
  The concrete locked-rollup certificate is now constructed below.
- Added an abstract stack interpreter and a generated table of 632 locked-state
  candidates at 476 instruction positions. The kernel proved table closure
  against the pinned runtime bytecode. The generator is not trusted. Concrete
  unary, binary, storage-read, jump, duplicate, swap, push, pop, calldata-read,
  memory-load, memory-store, and hash-result simulation lemmas compile. Exact
  instruction-state extraction also compiles. The first 37 new compiled lemmas passed
  separate axiom audits with only the allowed logical axioms. All 57 new results
  are in the exact-name audit list. The full 656-audit check passed, including compiler output, dependency
  gates, Solidity tests, Lean builds, ABI comparisons, and axiom checks.
- Proved `abstract_step_sound` and `abstract_instruction_sound`. These bind every
  supported nonhalting opcode and its instruction checks to the abstract table.
  Constructed `lockedFrameCertificate` from the checked runtime table. Proved
  `locked_active_accounts`: a fresh frame of the locked runtime preserves the
  full account map at every active prefix. It cannot enter another call or
  creation. This proof does not assume a frame certificate or a runtime safety
  result. Its premises are the pinned runtime, initial counter and empty stack,
  the nonzero lock, and the actual active-prefix relation.
  The six new results passed a separate axiom audit and raise the
  current exact-name list to 662. The full 656-name check passed; these six additions also passed their
  separate audit. The protected-frame result is now composed with foreign callback
  entries and fresh or colliding creation entries. The exact
  `CallbackActivePrefixCorrect` target is proved and checked by the audit.
  All seven entry and callback results passed their axiom audits. Added
  withdrawal reservation and custody results for the full active call tree.
  Surrounding accepted-call composition, nested
  access scopes, transaction-final effects, and the final claim bundle remain
  open. Keep the commit and push pending.
- Added `FrameRun` and `InstructionChildren`. They record actual EVM instructions
  and all guarded code children. Failed instructions and reverted frames retain
  their nested records. `frame_run_sound` proves the exact EVM result.
  `frame_run_complete` proves that every finite EVM run has such a tree, by
  induction on the remaining call depth and instruction fuel. No trace shape is
  assumed. Actual call and creation guards prove the depth decrease.
- The tree collects calldata keys from every root-context frame, including
  nested getters. `frame_run_scope_covered` proves coverage of the complete tree.
  `execution_has_covered_tree` combines actual execution, a complete record, and
  its finite scope with the fixed slots. This discharges scope collection for
  raw EVM frames. Connect the records to accepted message and creation results,
  surrounding execution, and transaction-final effects before the final gate.
- Added the open `TreeBoundaryCorrect` target for complete surrounding EVM frames.
  Proved boundary preservation for funded call transfers, fresh creation
  transfers, and nonce updates. Proved that an accepted message commits its
  recorded frame's accounts. `message_tree_refines` composes that frame result
  with the transfer, or proves checkpoint restoration on rejection. Its frame
  refinement premise is an induction obligation, not a completed security claim.
  Actual call and creation entries are unique and mutually exclusive, so a tree
  cannot substitute a different child or omit a creation in favor of a call.
  The full 691-name check passed: compiler output, dependency gates, Solidity
  tests, Lean builds, ABI comparisons, and allowed logical axioms.
- Proved creation rollback for initialization errors, reverts, and failed code
  checks. Accepted creation installs the exact initialization output. Code
  installation at another address preserves rollup storage and ETH. The call
  and creation wrappers now compose their recorded frame results with funded
  transfers, nonce updates, and code installation.
- Proved `tree_boundary_correct : TreeBoundaryCorrect`. The proof covers every
  local, call, creation, and self-destruct instruction. It binds recorded child
  entries to the actual instruction arguments and guards. Induction over the
  complete tree discharges child refinement. The result does not assume child
  correctness. All 18 new wrapper, instruction, and tree results passed their
  separate logical-axiom audit.
- `foreign_execution_refines`, `foreign_selected_message_refines`, and
  `foreign_creation_refines` now connect actual execution to these proofs.
  Their scopes come from complete execution records. They include nested root
  entries under reverted ancestors. All five record and wrapper results passed
  their separate logical-axiom audit.
- Proved `selected_message_refines` for external messages to the rollup, foreign
  contracts, or precompiles. Proved `deployed_message_sequence_correct` from
  actual deployment and a sequence of complete external messages. Its finite
  scope includes all nested root calldata keys. The non-alias condition and
  funded external-message conditions remain explicit. No message or child
  correctness premise remains. These five message-sequence results passed a
  separate logical-axiom audit. The 719-name full check passed. Transaction-final deletion and fees, root
  payment-prefix binding, the final eight-claim bundle, and its exact completion
  gate remain open. Top-level creation wrappers are proved separately; compose
  them with transaction execution as well. Keep the commit and push pending.
- For transaction finalization, bind the result to EVMLean `Υ`: the upfront
  sender debit, refund, beneficiary fee, self-destruct and dead-account deletion,
  and transient-storage reset. `Theta_gas_le` and `Xi_gas_le` supply gas bounds.
  Track the prepaid fee outside the account map when proving refund bounds.
  Prove that deletion bookkeeping cannot include the rollup; endpoint code
  preservation alone does not establish this. The pinned runtime has no byte
  `0xff`. `runtime_no_selfdestruct_byte` and `runtime_no_selfdestruct` now prove
  this fact and exclude self-destruct at every decoded program counter.
  `precheck_destruct_set` and `local_step_destruct_set` preserve the deletion
  set. `selfdestruct_step_set` adds only the executing account, when needed.
  These facts still need composition over nested calls and transaction results.
- Proved bounds on gas returned by actual selected messages and creation calls,
  plus the one-fifth refund bound. All three passed a separate logical-axiom
  audit. Nine new static-code, deletion-set, and gas lemmas compile. They raise
  the exact-name audit list to 728. Their combined separate audit passed with
  only the three allowed logical axioms. All 37 additions since the 691-name
  checkpoint compile and passed separate audits. The full 719-name check passed
  compiler output, dependency gates, Solidity tests, Lean builds, ABI comparison,
  and the allowed logical-axiom audit.
- Proved the transaction cleanup tail: self-destruct deletion, dead-account
  deletion, and transient-storage reset. The account-map proofs cover the exact
  erase folds and value map used by `Υ`. The dead-account test uses the account
  map before deletion, as in the pinned semantics. The 28 added exports passed
  their separate audit with only the allowed logical axioms. The exact-name list
  now has 756 entries. `transaction_cleanup_refines` still requires the rollup
  to be absent from the pending deletion set. Derive that condition over nested
  execution before using it in the final transaction theorem. The full 719-name
  check remains the last complete check; the later additions have separate audits.
- Proved exact checkpoint fee debits, refund and beneficiary credits, and the
  word-level one-fifth refund bound. The fee-credit total fits within prepaid
  gas when execution preserves its world budget. `transaction_execution_eq`
  binds the helpers to EVMLean `Υ`, including its message and creation branches.
  `transaction_finalization_refines` composes fee credits and cleanup. It still
  needs execution-world nonincrease and absence from the deletion set; neither
  premise is discharged by this helper. The actual provisional execution gas
  bound is proved. These 21 exports passed their separate logical-axiom audit.
  The 777-name full check passed: compiler output, dependency gates, Solidity
  tests, Lean builds, ABI comparison, and the allowed logical-axiom audit.
- Proved `source_world_nonincrease`, `runtime_world_nonincrease`, and
  `rollup_message_world_nonincrease`. Complete foreign execution now preserves
  total ETH through every nested code frame, precompile, creation, and rollback.
  `transaction_provisional_preserves` binds this budget and boundary refinement
  to the message or creation selected by `Υ`. Nonce, fee-price, and remaining
  value bounds are derived from upfront conditions.
  `transaction_boundary_of_no_deletion` now composes the full `Υ` result. Its
  only open execution-property premise is the rollup's absence from the final
  self-destruct set. This is a conditional composition helper, not the final
  transaction claim. All 30 exports passed their separate logical-axiom audit;
  the exact-name list has 807 entries. The 777-name check is the last full check.
- For deletion exclusion, prove an existing account survives arbitrary EVM code:
  its stored code persists, it stays outside the current-transaction creation
  set, and it stays outside the pending deletion set. The pinned EVM permits
  self-destruct to schedule only an account in the creation set. A creation at
  the rollup address fails its code-collision check. This route avoids a new
  runtime-dispatch alignment proof. Local code and lifecycle lemmas are in work;
  call, creation, precompile, and full execution-tree composition still remain.
- Account survival now compiles for local instructions, self-destruct, message
  results, creation results, and precompiles. The conditions track pinned code
  and absence from both lifecycle sets. Creation includes failed postchecks.
  These 24 exports raise the exact-name audit list to 831. The full check is
  running at this checkpoint. Compose the call and creation opcode metadata,
  then the full execution tree, to discharge transaction deletion exclusion.
  Keep root payment-prefix binding and the final eight-claim gate open.
  The pinned precompile wrapper returns an empty created-account set; the
  helper proves that exact behavior. Review this imported-semantic detail in
  the final trust audit. Account survival itself requires only that the rollup
  remains absent from the returned set.
- The full 831-name check passed: compiler output, dependency checks, Solidity
  tests, Lean builds, ABI comparison, and the allowed logical-axiom audit.
- Proved account survival through actual CALL, CALLCODE, DELEGATECALL, STATICCALL,
  CREATE, and CREATE2 instructions. Full execution-tree induction now discharges
  all child-survival premises. `transaction_provisional_no_deletion` derives
  absence from pending deletion from the pinned code at transaction entry.
  `transaction_boundary` composes the complete EVM transaction without the old
  deletion-exclusion premise. Its upfront nonce, fee, funds, calldata, world,
  and finite non-alias conditions remain explicit.
- `deployed_transaction_sequence_correct` now composes actual deployment and
  complete transactions, including fees, nested execution, rollback, and final
  cleanup. Its access scope comes from actual execution records. These 22 new
  exports passed their separate logical-axiom audit.
- Account survival also holds at every active instruction and nested-frame
  prefix, including frames that later revert. These six exports passed their
  separate logical-axiom audit.
- Added `RootCallPrefixBound` in `proofs/support/PaymentPrefix.lean` as the explicit
  open payment-prefix target. Every outgoing code call must reach the checked
  withdrawal cursor: correct selector, prelude checks, lock write, and exact
  payment stack. Prove this from `ContinuingPrefix` and the pinned bytecode.
  The existing `RD` lemmas record final-result equality or out-of-gas; those
  conclusions alone do not certify intermediate states in failing executions.
- The checked-cursor composition now binds the actual child CALL to its stack
  target and amount, derives funded credit from prelude checks, and proves
  safety throughout the receiver's active tree. It includes the rollup itself
  as receiver. These helpers do not require final success, but they still need
  the open root-prefix target above. Do not treat them as the final in-flight
  proof. All five payment-composition exports passed their separate logical-axiom
  audit. The runtime cannot enter a creation frame at any prefix; five new
  bytecode and decoding exports prove this fact and passed their separate
  logical-axiom audit. The exact-name audit list now
  has 869 entries. The full check passed for this checkpoint.
  The final EVM trace obligations remain open.
- Added exact prefix execution with `PrefixCursor` and `PCR`. These relations
  carry actual EVM states to a known child entry. They have no final-success or
  out-of-gas alternative. Stack, calldata, branches, memory, storage, permission,
  and gas rules compile. The dispatcher, address checks, and payment setup also
  compile. The withdrawal decoder, entry, credit load, and prelude checks passed. `root_call_prefix_bound` is written but has not passed its build yet.
- Added a general runtime control table and a closed region that excludes the
  payment CALL. The opcode simulation and certificate soundness proofs compile.
  Both table-closure certificates passed. Their kernel computation uses
  32-row chunks to bound memory use. Call-location and post-call checks are
  still running. Run the large checks in sequence.
- `continuing_prefix_boundary` proves safety and model refinement at each
  instruction boundary in a foreign frame, even if it later reverts. Its finite
  scope comes from actual child execution records. `child_call_entry_boundary`
  carries this result across a funded child entry.
  The 88 new prefix and control exports passed their separate logical-axiom
  audit. The child-entry and chunk-composition helpers also passed their audits.
  The seven withdrawal-prefix exports also passed their audits.
  The two table-closure certificates passed their audits.
  The exact-name list has 968 entries. The last full check remains
  the 869-name check. Keep the final claim bundle and completion gate open.
- Remaining work: prove the root payment-prefix target, compose the full
  eight-claim result with actual transaction traces, enforce its exact type in
  the completion gate, and complete the trust review. Keep the initial commit
  and push pending until those checks pass.
- Proved `batch_xi_authorized` from accepted writable EVM execution. It binds the
  actual caller to the sequencer address in slot zero. The lock write preserves
  that slot.
- Proved `batch_bytecode_classification` and `batch_xi_success` for the pinned
  runtime. Accepted writable batches pass all header, owner, credit, backing,
  and overflow checks. They have the exact seven storage writes and empty
  return data. Reads follow storage-write order, including possible slot aliases.
  The proof covers malformed calldata and failed checks through the dispatcher.
  Rejection and return segments permit out-of-gas; `batch_xi_success` requires
  actual accepted execution. Full writable batch correspondence is proved below.
- Proved `batch_bytecode_execution` and `batch_xi_execution`. When all bytecode
  checks hold, a writable batch returns the exact accounts and empty output, or
  runs out of gas. The proof starts at runtime dispatch. The guard lemmas now
  retain the failed check on each rejection path. No gas bound is proved here.
- Proved `batch_checks_equiv` and `batch_output_accounts_equiv`. Equivalent
  account maps give the same checks and equivalent results through all seven
  writes. The proofs follow read order and do not require slot separation.
  These checks and writes now match source execution, including ABI binding.
- Proved `batch_body_success`: the source checks construct a full batch execution
  with the exact seven writes and no return value. `batch_source_checks` proves
  those checks are necessary. `batch_source_success_iff` combines both directions.
  These proofs include both owner branches and read credit in storage-write order.
  They do not require slot separation. `batch_source_total` now constructs either
  the exact successful execution or a revert. `batch_source_rejected` constructs
  a revert whenever a source check fails.
- Stage the large batch proof modules before the full build to limit memory use.
  Two batch composition files use restricted unfolding when matching guard
  proofs. They disable the constructor-name syntax linter, which tries to
  evaluate symbolic calldata. Kernel checks and axiom audits remain active.
- Proved `batch_accepted_equivalence` and `batch_checked_equivalence`. Accepted
  writable batches now have full source-to-bytecode correspondence, including
  selector dispatch, ABI decoding, exact writes, and equivalent account maps.
  Valid batches also cover out-of-gas.
  External argument stores now use the ABI decoder's declaration order. Internal
  parameter binding uses a different insertion order and is not the external
  call model. Constructor binding remains separate.
- Proved `batch_correct` at the full runtime-equivalence type for writable batch
  calls. It covers success, failed source checks, malformed ABI arguments, and
  out-of-gas. It derives source dispatch from the literal bytecode selector.
  `batch_abi_rejected` covers short or signed-oversized argument data and either
  noncanonical address word. Writable dispatch composition is now proved above.
  Static mutation paths remain separate.
- Proved `batch_evm_effect` and `batch_evm_custody` from accepted EVM execution.
  They derive the caller, arguments, authorization, and exact model effect from
  calldata and the executed bytecode. Custody uses the finite storage conditions
  and initial safety. Neither theorem assumes source or bytecode correctness.
- Proved message-call success and rollback rules from EVM `Θ` and `Ξ`. Revert
  and exceptional halt restore the original accounts and substate, including
  the incoming value transfer. Accepted calls have matching successful `Ξ`
  execution with a nonempty account map. `message_call_rejected` also proves
  account and substate rollback for every rejected message call. Transaction gas
  fees remain separate.
- Proved `batch_source_authorized` and `batch_source_call_authorized`. Accepted
  source batches require zero call value and bind the actual caller to the model
  sequencer. `batch_source_continuity` proves the next batch number, its word
  bound, and the old-root check. `batch_source_after_owners` proves canonical
  empty effects and valid nonzero owners. `batch_source_after_deposit` and
  `batch_source_after_backing` derive credit bounds and exact intermediate
  writes from accepted source execution. These physical-state proofs follow
  the storage order, including possible aliases. The model refinement still
  needs its finite non-alias condition.
  `batch_source_exact` now derives all seven writes, the final local frame, and
  the empty return from accepted execution. `batch_projection` maps the writes
  to the model, including coincident owners. `batch_source_refines` proves the
  full labeled source result, including code, storage scope, ETH bounds, and
  lock release. It assumes no body-correctness premise. Source withdrawal
  refinement remains open.
- Added finite storage-write lemmas for tracked reads, sparse storage, account
  presence, execution environment, code, and ETH balance preservation.
- Added named theorem audits and recursive proof-file checks.
- The full check passes with both semantic patches: seven dependency-gate tests,
  pinned compiler output, 16 Solidity tests, Lean builds, ABI printer comparisons,
  and 656 named theorem audits. The audits use only the three allowed logical
  axioms. This check
  validates completed results; the final contract proof gate remains open.
- The LeanCrypto port has kernel-checked deposit-selector and owner-one mapping
  hashes. The model is installed through `patches/keccak` and
  `scripts/dependencies.py`. Seven gate tests pass. Both patches keep their
  upstream package revisions and reject other local changes.
  `DepositWitness.executes` and `deposit_success_witness` compile. Rewriting the
  checked mapping slot before kernel reduction avoids a costly elaborator
  comparison. `BytecodeCorrect` is now discharged by `bytecode_correct` above.
- The completed-boundary EVM trace statements are now proved. Step 1 still needs
  the full execution-tree and in-flight claim bundle. Bytecode payment witnesses are
  now proved for accepted withdrawals.
  The trace scope must include mapping keys read in nested calls, including getters.
  Derive this scope from actual EVM execution. Do not assume callback isolation.
  Bind calls to `toExecute` as well as stored code. EVMLean chooses a precompile
  for addresses in `π`, even if their account has code. State the rollup-address
  exclusion in the deployment environment conditions.
  The callback storage proofs now discharge the precompile case with
  `accountStaticStateEq_of_precompiled_Theta`. They add no address restriction
  to `SourceRefinesModel`. Root bytecode execution still needs correct code selection.
  Source withdrawal refinement, accepted EVM refinement in either permission
  mode, and deployment-to-boundary-trace composition are now proved above.
  Full surrounding-execution composition and the final theorem gate remain open.
- Do not commit or push until steps 1–6 are complete.
