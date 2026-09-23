import invariants.Callbacks
import proofs.Completion
import proofs.generated.ControlIndexedPaths
import proofs.WithdrawalPrefixChecks
import proofs.ChildPrefixBoundary
import proofs.ControlStorage
import proofs.ControlCall
import proofs.ControlMemory
import proofs.ControlSimulation
import proofs.ControlInstruction
import proofs.ControlCertificate
import proofs.IndexedControl
import proofs.ControlTable
import proofs.PrefixHead
import proofs.PrefixCursor
import proofs.PrefixGuard
import proofs.PrefixPush
import proofs.PrefixReach
import proofs.PrefixStack
import proofs.PrefixSimple
import proofs.PrefixConstants
import proofs.PrefixMemory
import proofs.PrefixStorage
import proofs.PrefixGas
import proofs.PrefixPermission
import proofs.RuntimePrefixDispatch
import proofs.RuntimePrefixAddress
import proofs.WithdrawalPrefixPayment
import proofs.PrefixBoundary
import proofs.RuntimeCreationExclusion
import proofs.ChildSurvival
import proofs.CallLifecycle
import proofs.CreationLifecycle
import proofs.CreationLifecycleCases
import proofs.CallInstructionSurvival
import proofs.CreationInstructionSurvival
import proofs.InstructionSurvival
import proofs.TreeSurvival
import proofs.ExecutionSurvival
import proofs.TransactionSurvival
import proofs.TransactionSequence
import proofs.PrefixSurvival
import proofs.WithdrawalSelectedPrefix
import proofs.CallChildBinding
import proofs.WithdrawalPrefixBinding
import proofs.PaymentPrefixComposition
import proofs.SurvivalCreation
import proofs.SurvivalPrecompile
import proofs.SurvivalMessage
import proofs.PrecompileSubstate
import proofs.SurvivalEntry
import proofs.SurvivalLocal
import proofs.CreationSetLocal
import proofs.LocalCode
import proofs.TransactionBoundary
import proofs.TransactionPreconditions
import proofs.TransactionProvisional
import proofs.TransactionCalls
import proofs.SurroundingBudget
import proofs.TreeBudget
import proofs.InstructionBudget
import proofs.CreationInstructionBudget
import proofs.CallInstructionBudget
import proofs.RollupCallBudget
import proofs.ChildBudget
import proofs.ExecutionBudgetWrappers
import proofs.RuntimeWorld
import proofs.SourceWorld
import proofs.TransactionEntry
import proofs.TransactionFinalization
import proofs.TransactionFeeBounds
import proofs.TransactionFees
import proofs.BoundaryCredit
import proofs.TransactionCleanup
import proofs.TransientReset
import proofs.AccountMapValues
import proofs.DeadAccounts
import proofs.BoundaryErase
import proofs.AccountErase
import proofs.TreeErase
import proofs.DestructionInstruction
import proofs.AddressOrder
import proofs.DestructionLocal
import proofs.TransactionGas
import proofs.RuntimeDestruction
import proofs.RuntimeBytes
import proofs.MessageSequence
import proofs.SurroundingCreation
import proofs.SurroundingMessage
import proofs.RecordedExecution
import proofs.TreeBoundary
import proofs.InstructionTree
import proofs.CreationInstructionTree
import proofs.CreationOpcodeCases
import proofs.CallInstructionTree
import proofs.CallTree
import proofs.ChildBoundary
import proofs.ChildTreeCoverage
import proofs.CreationTree
import proofs.CreationPostcheck
import proofs.ExecutionTree
import semantics.recording.ChildDepth
import semantics.recording.ExecutionTreeComplete
import proofs.TreeCoverage
import proofs.RecordedScope
import proofs.BoundaryTransfer
import proofs.MessageTree
import proofs.ChildEntryUnique
import proofs.WithdrawalActive
import proofs.ActiveCallEntry
import proofs.ActiveCreationEntry
import proofs.ActiveCallback
import proofs.InstructionContinue
import proofs.AbstractSimulation
import proofs.AbstractInstruction
import proofs.LockedFrame
import proofs.AbstractStack
import proofs.AbstractPush
import proofs.AbstractMemory
import proofs.AbstractSwap
import proofs.AbstractDrop
import proofs.InstructionState
import proofs.LockedPaths
import proofs.LockedPathRows
import proofs.PathCertificate
import proofs.AbstractJump
import proofs.CreationSite
import proofs.CreationOpcode
import proofs.CreationTransfer
import proofs.ChildCreation
import proofs.ActiveFailure
import proofs.AccountOperations
import proofs.FrameCertificate
import proofs.PrecheckCursor
import proofs.AbstractWord
import proofs.AbstractCursor
import proofs.AbstractExecution
import proofs.CreationPrefix
import proofs.LocalBoundary
import proofs.RollupCallInstruction
import proofs.ChildCall
import proofs.WithdrawalPrefix
import proofs.DeployedTrace
import proofs.MessageClassification
import proofs.DeployedMessage
import proofs.AcceptedCallBinding
import proofs.MessageRefinement
import proofs.DeploymentInitial
import proofs.RuntimeRefinement
import proofs.RuntimeSource
import proofs.SourceRefinement
import proofs.WithdrawalRefinement
import proofs.WithdrawalCallbackModel
import proofs.WithdrawalProjection
import proofs.WithdrawalBalances
import proofs.CallbackPaymentBalances
import proofs.CallbackBalances
import proofs.WorldCreationSteps
import proofs.WorldDepthLimit
import proofs.WorldNonce
import proofs.WorldCreation
import proofs.WorldCallSteps
import proofs.WorldMessageCalls
import proofs.WorldExecution
import proofs.CallbackExecutionStorage
import proofs.Transitions
import proofs.SolmGuards
import proofs.Composition
import proofs.Constructor
import proofs.Payments
import proofs.Deposit
import proofs.DepositRefinement
import proofs.CreationBody
import proofs.CreationExecution
import proofs.CreationRefinement
import proofs.Deployment
import proofs.CreationSuccess
import proofs.DepositBytecodeSuccess
import proofs.DepositDispatch
import proofs.generated.KeccakMappingOne
import proofs.DepositCustody
import proofs.StaticCalls
import proofs.BatchRefinement
import proofs.MessageCall
import proofs.GetterRefinement
import proofs.DepositSuccess
import proofs.RuntimeGetters
import proofs.RuntimeUnknownSelector
import proofs.GetterEquivalence
import proofs.DispatchRejection
import proofs.RuntimeMutationLocks

import proofs.LockedMessageCall
import proofs.BatchBytecodeAuthorization

import proofs.BatchBytecodeClassification
import proofs.BatchBytecodeExecution
import proofs.BatchBytecodeMaps
import proofs.BatchSourceChecks
import proofs.BatchAcceptedEquivalence
import proofs.BatchEquivalence
import proofs.BatchCustody
import proofs.WithdrawalExecution
import proofs.WithdrawalPaymentSetup
import proofs.WithdrawalCheckCorrespondence
import proofs.WithdrawalBytecodeClassification
import proofs.WithdrawalPaymentBridge
import proofs.WithdrawalABI
import proofs.RuntimeEquivalence
import proofs.WithdrawalStorageEffects
import proofs.WorldBalances
import proofs.WorldTransfers
import proofs.WorldCreationTransfers
import proofs.WorldPrecompiles
import proofs.LockedCallBalances
import proofs.WorldSelfdestruct
import proofs.WorldStorage
import proofs.WorldLocalSteps
import proofs.WorldPrecheck

#print axioms Rollup.EVM.withdrawal_call_result
#print axioms Rollup.EVM.withdrawal_locked_state
#print axioms Rollup.EVM.withdrawal_input_credit_equiv
#print axioms Rollup.EVM.withdrawal_output_accounts_equiv
#print axioms Rollup.EVM.withdrawal_accounts_correspondence
#print axioms Rollup.EVM.withdrawal_bytecode_checked_setup
#print axioms Rollup.EVM.withdrawal_bytecode_checked_call
#print axioms Rollup.EVM.withdrawal_checked_equivalence
#print axioms Rollup.EVM.withdrawal_decoded_equivalence
#print axioms Rollup.EVM.withdrawal_correct
#print axioms Rollup.EVM.runtime_equivalence_for
#print axioms Rollup.EVM.runtime_correct
#print axioms Rollup.EVM.bytecode_correct

#print axioms Rollup.EVM.withdrawal_bytecode_return_data
#print axioms Rollup.EVM.runtime_call_value_made_empty
#print axioms Rollup.EVM.withdrawal_bytecode_payment_check
#print axioms Rollup.EVM.withdrawal_bytecode_debit
#print axioms Rollup.EVM.withdrawal_bytecode_call
#print axioms Rollup.EVM.withdrawal_bytecode_classification
#print axioms Rollup.EVM.withdrawal_xi_success
#print axioms Rollup.EVM.withdrawal_payment_to_source
#print axioms Rollup.EVM.withdrawal_abi_decode
#print axioms Rollup.EVM.withdrawal_abi_rejected
#print axioms Rollup.EVM.withdrawal_call_bound

#print axioms Rollup.EVM.withdrawal_prelude_exact
#print axioms Rollup.EVM.withdrawal_prelude_checks
#print axioms Rollup.EVM.withdrawal_prelude_result
#print axioms Rollup.EVM.withdrawal_prelude_rejected
#print axioms Rollup.EVM.withdrawal_postlude_exact
#print axioms Rollup.EVM.withdrawal_postlude_rejected
#print axioms Rollup.EVM.withdrawal_body_rejected_checks
#print axioms Rollup.EVM.withdrawal_body_payment
#print axioms Rollup.EVM.withdrawal_source_exact
#print axioms Rollup.EVM.withdrawal_bytecode_amount
#print axioms Rollup.EVM.withdrawal_bytecode_credit_load
#print axioms Rollup.EVM.withdrawal_bytecode_credit_check
#print axioms Rollup.EVM.withdrawal_bytecode_prelude
#print axioms Rollup.EVM.withdrawal_xi_prelude_checks
#print axioms Rollup.EVM.withdrawal_bytecode_payment_setup
#print axioms Rollup.EVM.withdrawal_claim_slot_binding
#print axioms Rollup.EVM.withdrawal_credit_correspondence
#print axioms Rollup.EVM.withdrawal_checks_to_source
#print axioms Rollup.EVM.withdrawal_checks_to_bytecode
#print axioms Rollup.EVM.withdrawal_checks_equiv

#print axioms Rollup.EVM.batch_evm_effect
#print axioms Rollup.EVM.batch_evm_custody

#print axioms Rollup.EVM.optional_owner_total
#print axioms Rollup.EVM.batch_source_total
#print axioms Rollup.EVM.batch_source_rejected
#print axioms Rollup.EVM.batch_abi_bad_owner
#print axioms Rollup.EVM.batch_abi_rejected
#print axioms Rollup.EVM.batch_decoded_equivalence
#print axioms Rollup.EVM.batch_correct

#print axioms Rollup.EVM.batch_word_binding
#print axioms Rollup.EVM.batch_deposit_slot_binding
#print axioms Rollup.EVM.batch_claim_slot_binding
#print axioms Rollup.EVM.batch_credit_correspondence
#print axioms Rollup.EVM.batch_debit_correspondence
#print axioms Rollup.EVM.batch_available_correspondence
#print axioms Rollup.EVM.batch_available_word_correspondence
#print axioms Rollup.EVM.batch_backing_correspondence
#print axioms Rollup.EVM.batch_claim_correspondence
#print axioms Rollup.EVM.batch_accounts_correspondence
#print axioms Rollup.EVM.batch_optional_owner_binding
#print axioms Rollup.EVM.batch_authorization_correspondence
#print axioms Rollup.EVM.batch_checks_to_source
#print axioms Rollup.EVM.batch_checks_to_bytecode
#print axioms Rollup.EVM.batch_success_correspondence
#print axioms Rollup.EVM.batch_accepted_source
#print axioms Rollup.EVM.batch_abi_values
#print axioms Rollup.EVM.batch_abi_decode
#print axioms Rollup.EVM.batch_call_bound
#print axioms Rollup.EVM.batch_accepted_equivalence
#print axioms Rollup.EVM.batch_checked_equivalence

#print axioms Rollup.EVM.eval_batch_sequencer
#print axioms Rollup.EVM.eval_batch_number
#print axioms Rollup.EVM.eval_batch_root
#print axioms Rollup.EVM.batch_header_success
#print axioms Rollup.EVM.optional_owner_success
#print axioms Rollup.EVM.batch_owners_success
#print axioms Rollup.EVM.batch_deposit_success
#print axioms Rollup.EVM.batch_backing_success
#print axioms Rollup.EVM.batch_claims_success
#print axioms Rollup.EVM.batch_final_success
#print axioms Rollup.EVM.batch_body_success
#print axioms Rollup.EVM.batch_source_checks
#print axioms Rollup.EVM.batch_source_success_iff

#print axioms Rollup.EVM.batch_xi_execution
#print axioms Rollup.EVM.batch_input_credit_equiv
#print axioms Rollup.EVM.batch_deposit_accounts_equiv
#print axioms Rollup.EVM.batch_available_equiv
#print axioms Rollup.EVM.batch_backing_accounts_equiv
#print axioms Rollup.EVM.batch_claim_equiv
#print axioms Rollup.EVM.batch_output_accounts_equiv
#print axioms Rollup.EVM.batch_checks_equiv

#print axioms Rollup.EVM.batch_bytecode_authorization_cases
#print axioms Rollup.EVM.batch_bytecode_header_cases
#print axioms Rollup.EVM.batch_bytecode_deposit_owner_cases
#print axioms Rollup.EVM.batch_bytecode_withdrawal_owner_cases
#print axioms Rollup.EVM.batch_bytecode_deposit_check_cases
#print axioms Rollup.EVM.batch_bytecode_backing_check_cases
#print axioms Rollup.EVM.batch_bytecode_prefix_execution
#print axioms Rollup.EVM.batch_bytecode_accounting_execution
#print axioms Rollup.EVM.batch_bytecode_execution

#print axioms Rollup.EVM.batch_bytecode_header
#print axioms Rollup.EVM.batch_bytecode_prefix
#print axioms Rollup.EVM.batch_xi_header
#print axioms Rollup.EVM.batch_bytecode_deposit_owner
#print axioms Rollup.EVM.batch_bytecode_withdrawal_owner
#print axioms Rollup.EVM.runtime_checked_subtract
#print axioms Rollup.EVM.batch_bytecode_deposit_load
#print axioms Rollup.EVM.batch_bytecode_deposit_check
#print axioms Rollup.EVM.batch_bytecode_deposit_store
#print axioms Rollup.EVM.batch_bytecode_accounting_entry
#print axioms Rollup.EVM.batch_xi_accounting_checks
#print axioms Rollup.EVM.batch_bytecode_backing_check
#print axioms Rollup.EVM.batch_bytecode_backing_store
#print axioms Rollup.EVM.batch_bytecode_final_store
#print axioms Rollup.EVM.batch_bytecode_classification
#print axioms Rollup.EVM.batch_xi_success

#print axioms Rollup.EVM.mutation_dispatch
#print axioms Rollup.EVM.mutation_nonpayable
#print axioms Rollup.EVM.mutation_decoder
#print axioms Rollup.EVM.withdrawal_decode
#print axioms Rollup.EVM.withdrawal_decode_bad_length
#print axioms Rollup.EVM.withdrawal_decode_bad_owner
#print axioms Rollup.EVM.withdrawal_entry_classification
#print axioms Rollup.EVM.withdrawal_locked_reject
#print axioms Rollup.EVM.withdrawal_xi_entry_checks
#print axioms Rollup.EVM.batch_decode_first
#print axioms Rollup.EVM.batch_decode_second
#print axioms Rollup.EVM.batch_decode_tail
#print axioms Rollup.EVM.batch_decode_bad_length
#print axioms Rollup.EVM.batch_decode_classification
#print axioms Rollup.EVM.batch_entry_classification
#print axioms Rollup.EVM.batch_locked_reject
#print axioms Rollup.EVM.batch_xi_entry_checks
#print axioms Rollup.EVM.deposit_locked_reject
#print axioms Rollup.EVM.locked_runtime_xi_preserves_accounts
#print axioms Rollup.EVM.message_call_initial_static_state
#print axioms Rollup.EVM.solc_slot_default
#print axioms Rollup.EVM.locked_message_call_accepted
#print axioms Rollup.EVM.locked_message_call_static_state
#print axioms Rollup.EVM.solc_slot_store_other
#print axioms Rollup.EVM.batch_bytecode_authorization
#print axioms Rollup.EVM.batch_xi_authorized
#print axioms Reasoning.Theory.swap9_xstep
#print axioms Reasoning.Reach.RD.swap9
#print axioms Rollup.EVM.message_call_rejected

#print axioms Rollup.EVM.batch_bytecode_locked
#print axioms Rollup.EVM.batch_bytecode_enter
#print axioms Rollup.EVM.withdrawal_bytecode_locked
#print axioms Rollup.EVM.withdrawal_bytecode_enter

#print axioms Rollup.EVM.HashCertificates.sequencer_hash
#print axioms Rollup.EVM.HashCertificates.state_root_hash
#print axioms Rollup.EVM.HashCertificates.batch_number_hash
#print axioms Rollup.EVM.HashCertificates.backing_hash
#print axioms Rollup.EVM.HashCertificates.pending_deposits_hash
#print axioms Rollup.EVM.HashCertificates.pending_withdrawals_hash
#print axioms Rollup.EVM.HashCertificates.execute_batch_hash
#print axioms Rollup.EVM.HashCertificates.withdraw_hash
#print axioms Rollup.EVM.root_return_encoding
#print axioms Rollup.EVM.scalar_getter_encoding
#print axioms Rollup.EVM.scalar_getter_value_init
#print axioms Rollup.EVM.scalar_getter_equivalence_for
#print axioms Rollup.EVM.sequencer_getter_equivalence_for
#print axioms Rollup.EVM.mapping_getter_value_init
#print axioms Rollup.EVM.mapping_getter_decoded_equivalence
#print axioms Rollup.EVM.mapping_getter_equivalence_for
#print axioms Rollup.EVM.source_selector_bytes
#print axioms Rollup.EVM.source_selector_comparison
#print axioms Rollup.EVM.source_selector_calldata
#print axioms Rollup.EVM.source_selector_dispatch
#print axioms Rollup.EVM.scalar_getter_correct
#print axioms Rollup.EVM.sequencer_getter_correct
#print axioms Rollup.EVM.mapping_getter_correct
#print axioms Rollup.EVM.getters_correct
#print axioms Rollup.EVM.source_short_calldata
#print axioms Rollup.EVM.source_unknown_selector
#print axioms Rollup.EVM.short_calldata_correct
#print axioms Rollup.EVM.unknown_selector_correct

#print axioms Rollup.EVM.runtime_unknown_selector
#print axioms Rollup.EVM.runtime_success_selector

#print axioms Rollup.EVM.runtime_return_tail
#print axioms Rollup.EVM.runtime_return_word
#print axioms Rollup.EVM.scalar_getter_nonpayable
#print axioms Rollup.EVM.scalar_getter_return
#print axioms Rollup.EVM.scalar_getter_dispatch
#print axioms Rollup.EVM.scalar_getter_xi_success
#print axioms Rollup.EVM.sequencer_getter_dispatch
#print axioms Rollup.EVM.sequencer_getter_nonpayable
#print axioms Rollup.EVM.sequencer_getter_return
#print axioms Rollup.EVM.sequencer_getter_xi_success
#print axioms Rollup.EVM.mapping_return_pointer
#print axioms Rollup.EVM.mapping_return_read128
#print axioms Rollup.EVM.mapping_body_destination
#print axioms Rollup.EVM.mapping_getter_nonpayable
#print axioms Rollup.EVM.mapping_getter_decoder
#print axioms Rollup.EVM.mapping_getter_return
#print axioms Rollup.EVM.mapping_getter_dispatch
#print axioms Rollup.EVM.mapping_getter_classification
#print axioms Rollup.EVM.mapping_getter_xi_success
#print axioms Rollup.EVM.getter_xi_preserves_accounts

#print axioms Rollup.EVM.eval_batch_claims
#print axioms Rollup.EVM.assign_batch_claims
#print axioms Rollup.EVM.batch_source_after_claims
#print axioms Rollup.EVM.assign_batch_root
#print axioms Rollup.EVM.assign_batch_number
#print axioms Rollup.EVM.batch_source_exact
#print axioms Rollup.EVM.storeKeys_present
#print axioms Rollup.EVM.read_storeKeys
#print axioms Rollup.EVM.storeKeys_ready
#print axioms Rollup.EVM.storeKeys_environment
#print axioms Rollup.EVM.storeKeys_balance
#print axioms Rollup.EVM.storeKeys_ownCode
#print axioms Rollup.EVM.storeKeys_worldBounded
#print axioms Rollup.EVM.batch_execution_writes
#print axioms Rollup.EVM.batch_writes_tracked
#print axioms Rollup.EVM.batch_read_values
#print axioms Rollup.EVM.batch_storage
#print axioms Rollup.EVM.batch_projection
#print axioms Rollup.EVM.batch_source_refines
#print axioms Rollup.EVM.accepted_require
#print axioms Rollup.EVM.accepted_assign
#print axioms Rollup.EVM.accepted_exact
#print axioms Rollup.EVM.accepted_require_branch
#print axioms Rollup.EVM.batch_source_header
#print axioms Rollup.EVM.batch_source_continuity
#print axioms Rollup.EVM.accepted_optional_owner
#print axioms Rollup.EVM.batch_source_after_owners
#print axioms Rollup.EVM.eval_batch_pending
#print axioms Rollup.EVM.assign_batch_pending
#print axioms Rollup.EVM.eval_batch_backing
#print axioms Rollup.EVM.assign_batch_backing
#print axioms Rollup.EVM.batch_source_after_deposit
#print axioms Rollup.EVM.batch_source_after_backing
#print axioms Rollup.EVM.batch_source_authorized
#print axioms Rollup.EVM.batch_source_call_authorized
#print axioms Rollup.EVM.message_call_revert
#print axioms Rollup.EVM.message_call_error
#print axioms Rollup.EVM.message_call_success
#print axioms Rollup.EVM.message_call_empty
#print axioms Rollup.EVM.message_call_accepted
#print axioms Rollup.EVM.deposit_mapping_slot_one
#print axioms Rollup.EVM.deposit_success_witness
#print axioms Rollup.EVM.getter_eval
#print axioms Rollup.EVM.getter_source_exact
#print axioms Rollup.EVM.getter_source_nonpayable
#print axioms Rollup.EVM.getter_model_return
#print axioms Rollup.EVM.getter_source_refines
#print axioms Rollup.EVM.DepositWitness.executes
#print axioms Rollup.EVM.getter_source_preserves_state
#print axioms Rollup.EVM.static_call_preserves_rollup
#print axioms Rollup.EVM.HashCertificates.deposit_mapping_one
#print axioms Rollup.EVM.readWord_equiv
#print axioms Rollup.EVM.account_balance_equiv
#print axioms Rollup.EVM.project_equiv
#print axioms Rollup.EVM.storageReady_equiv
#print axioms Rollup.EVM.worldBounded_equiv
#print axioms Rollup.EVM.account_code_equiv
#print axioms Rollup.EVM.ownCode_equiv
#print axioms Rollup.EVM.deposit_evm_effect
#print axioms Rollup.EVM.deposit_evm_custody

#print axioms Rollup.reachable_safe
#print axioms Rollup.batch_conserves_liabilities
#print axioms Rollup.custody
#print axioms Rollup.batch_cannot_replay
#print axioms Rollup.failed_withdrawal_restores_state
#print axioms Rollup.successful_withdrawal_exact
#print axioms Rollup.EVM.locked_deposit_reverts
#print axioms Rollup.EVM.locked_batch_reverts
#print axioms Rollup.EVM.locked_withdrawal_reverts
#print axioms Rollup.EVM.source_custody
#print axioms Rollup.callTrace_safe
#print axioms Rollup.callTrace_custody
#print axioms Rollup.successful_deposit_exact
#print axioms Rollup.successful_batch_exact
#print axioms Rollup.successful_batch_authorized
#print axioms Rollup.successful_withdrawal_payment
#print axioms Rollup.reverted_call_unchanged
#print axioms Rollup.exceptional_call_unchanged
#print axioms Rollup.batch_cannot_replay_after_trace
#print axioms Rollup.EVM.project_extend
#print axioms Rollup.EVM.read_store_key
#print axioms Rollup.EVM.constructor_initializes
#print axioms Rollup.EVM.constructor_source_exact
#print axioms Rollup.EVM.withdrawal_payment_witness
#print axioms Rollup.EVM.source_payment_bound
#print axioms Rollup.EVM.deposit_source_exact
#print axioms Rollup.EVM.deposit_projection
#print axioms Rollup.EVM.deposit_storage_ready
#print axioms Rollup.EVM.deposit_source_success
#print axioms Rollup.EVM.deposit_rejection_exact
#print axioms Rollup.EVM.deposit_source_classification
#print axioms Rollup.EVM.deposit_success_checks
#print axioms Rollup.EVM.deposit_source_refines
#print axioms Rollup.EVM.jumpScan_valid
#print axioms Rollup.EVM.creation_nonpayable
#print axioms Rollup.EVM.creation_zero_value
#print axioms Rollup.EVM.creation_return
#print axioms Rollup.EVM.creation_zero_sequencer
#print axioms Rollup.EVM.creation_body
#print axioms Rollup.EVM.creation_load_args
#print axioms Rollup.EVM.creation_execution
#print axioms Rollup.EVM.creation_execution_zero
#print axioms Rollup.EVM.creation_xi_result
#print axioms Rollup.EVM.store_address_packed
#print axioms Rollup.EVM.constructor_source_packed
#print axioms Rollup.EVM.creation_body_packed
#print axioms Rollup.EVM.creation_execution_packed
#print axioms Rollup.EVM.creation_xi_packed
#print axioms Rollup.EVM.constructor_solm_success
#print axioms Rollup.EVM.constructor_solm_nonpayable
#print axioms Rollup.EVM.constructor_solm_zero
#print axioms Rollup.EVM.creation_deployment
#print axioms Rollup.EVM.creation_deployment_shape
#print axioms Rollup.EVM.constructor_equivalence_for
#print axioms Rollup.EVM.constructor_correct
#print axioms Rollup.EVM.deployment_install_result
#print axioms Rollup.EVM.deployment_outOfGas
#print axioms Rollup.EVM.deployment_success_code
#print axioms Rollup.EVM.CreationWitness.executes
#print axioms Rollup.EVM.creation_success_witness
#print axioms Rollup.EVM.runtime_prologue
#print axioms Rollup.EVM.runtime_short_calldata
#print axioms Rollup.EVM.runtime_selector
#print axioms Rollup.EVM.runtime_deposit_dispatch
#print axioms Rollup.EVM.runtime_address_check
#print axioms Rollup.EVM.runtime_address_check_reject
#print axioms Rollup.EVM.runtime_address_decode
#print axioms Rollup.EVM.runtime_address_bad_length
#print axioms Rollup.EVM.runtime_address_bad_word
#print axioms Rollup.EVM.deposit_bytecode_locked
#print axioms Rollup.EVM.deposit_bytecode_enter
#print axioms Rollup.EVM.deposit_bytecode_owner_ok
#print axioms Rollup.EVM.deposit_bytecode_value_ok
#print axioms Rollup.EVM.deposit_bytecode_zero_value
#print axioms Rollup.EVM.deposit_bytecode_load
#print axioms Rollup.EVM.runtime_checked_add
#print axioms Rollup.EVM.deposit_bytecode_store
#print axioms Rollup.EVM.deposit_bytecode_zero_owner
#print axioms Rollup.EVM.deposit_bytecode_self_owner
#print axioms Rollup.EVM.runtime_checked_add_overflow
#print axioms Rollup.EVM.deposit_bytecode_execution
#print axioms Rollup.EVM.deposit_bytecode_classification
#print axioms Rollup.EVM.deposit_xi_success
#print axioms Rollup.EVM.deposit_body_exact
#print axioms Rollup.EVM.deposit_execution_credit
#print axioms Rollup.EVM.deposit_slot
#print axioms Rollup.EVM.deposit_execution_credit_init
#print axioms Rollup.EVM.deposit_success_correspondence
#print axioms Rollup.EVM.deposit_execution_next_eval
#print axioms Rollup.EVM.deposit_body_rejection
#print axioms Rollup.EVM.deposit_address_word_inj
#print axioms Rollup.EVM.deposit_checks_init
#print axioms Rollup.EVM.deposit_decoded_equivalence
#print axioms Rollup.EVM.deposit_equivalence_for
#print axioms Rollup.EVM.KeccakDeposit.deposit_hash
#print axioms Rollup.EVM.deposit_selector_hash
#print axioms Rollup.EVM.deposit_selector_bytes
#print axioms Rollup.EVM.deposit_selector_match
#print axioms Rollup.EVM.deposit_selector_dispatch
#print axioms Rollup.EVM.deposit_correct

#print axioms Rollup.EVM.runtime_address_decode_any
#print axioms Rollup.EVM.withdrawal_decode_any
#print axioms Rollup.EVM.batch_decode_any
#print axioms Rollup.EVM.runtime_dispatch_any
#print axioms Rollup.EVM.locked_runtime_any_entry
#print axioms Rollup.EVM.locked_runtime_xi_preserves_accounts_any
#print axioms Rollup.EVM.locked_message_call_accepted_any
#print axioms Rollup.EVM.locked_message_call_static_state_any
#print axioms Rollup.EVM.CodeStorageFrame.refl
#print axioms Rollup.EVM.CodeStorageFrame.symm
#print axioms Rollup.EVM.CodeStorageFrame.trans
#print axioms Rollup.EVM.sendEthCreate_static_state
#print axioms Rollup.EVM.pinned_account_present
#print axioms Rollup.EVM.pinned_toExecute
#print axioms Rollup.EVM.pinned_unchanged_frame
#print axioms Rollup.EVM.pinned_account_not_dead
#print axioms Rollup.EVM.locked_own_call_frame
#print axioms Rollup.EVM.locked_locality_step
#print axioms Rollup.EVM.locked_locality_chain
#print axioms Rollup.EVM.callback_preserves_rollup_storage
#print axioms Rollup.EVM.source_callback_storage
#print axioms Rollup.EVM.readWord_default
#print axioms Rollup.EVM.ownCode_default
#print axioms Rollup.EVM.withdrawal_callback_storage

#print axioms Rollup.EVM.CodeStorageFrame.readWord
#print axioms Rollup.EVM.CodeStorageFrame.storageReady
#print axioms Rollup.EVM.CodeStorageFrame.ownCode
#print axioms Rollup.EVM.CodeStorageFrame.project

#print axioms Rollup.EVM.source_callback_environment
#print axioms Rollup.EVM.withdrawal_final_writes
#print axioms Rollup.EVM.withdrawal_final_storage_ready
#print axioms Rollup.EVM.withdrawal_final_storage_values

#print axioms Rollup.EVM.ethLedger_lookup
#print axioms Rollup.EVM.worldBounded_iff_worldEth
#print axioms Rollup.EVM.ethLedger_insert
#print axioms Rollup.EVM.worldEth_insert
#print axioms Rollup.EVM.eth_pair_le_world
#print axioms Rollup.EVM.funded_recipient_bound
#print axioms Rollup.EVM.sendEth_split
#print axioms Rollup.EVM.ethLedger_credit
#print axioms Rollup.EVM.ethLedger_debit
#print axioms Rollup.EVM.sendEth_ledger_ne
#print axioms Rollup.EVM.sendEth_world_ne
#print axioms Rollup.EVM.sendEth_self_ledger
#print axioms Rollup.EVM.sendEth_world
#print axioms Rollup.EVM.sendEth_other_balance
#print axioms Rollup.EVM.sendEthCreate_ledger_ne
#print axioms Rollup.EVM.sendEthCreate_world_ne
#print axioms Rollup.EVM.sendEthCreate_other_balance
#print axioms Rollup.EVM.precompiled_call_accounts
#print axioms Rollup.EVM.precompiled_call_world
#print axioms Rollup.EVM.precompiled_call_other_balance
#print axioms Rollup.EVM.locked_own_call_accounts
#print axioms Rollup.EVM.locked_own_call_balances
#print axioms Rollup.EVM.selfdestruct_accounts
#print axioms Rollup.EVM.destruction_ledger_ne
#print axioms Rollup.EVM.destruction_ledger_self
#print axioms Rollup.EVM.destruction_balances
#print axioms Rollup.EVM.selfdestruct_step_balances
#print axioms Rollup.EVM.ethLedger_insert_same_balance
#print axioms Rollup.EVM.sstore_ethLedger
#print axioms Rollup.EVM.tstore_ethLedger

#print axioms Rollup.EVM.sendEth_zero_ledger
#print axioms Rollup.EVM.sendEth_protected_balance
#print axioms Rollup.EVM.local_step_ethLedger
#print axioms Rollup.EVM.precheck_accounts

#print axioms Rollup.EVM.foreign_step_storage
#print axioms Rollup.EVM.foreign_call_storage
#print axioms Rollup.EVM.foreign_xi_storage
#print axioms Rollup.EVM.EthFrame.refl
#print axioms Rollup.EVM.EthFrame.trans
#print axioms Rollup.EVM.LockedWorld.next
#print axioms Rollup.EVM.foreign_xstep_balances
#print axioms Rollup.EVM.foreign_x_balances
#print axioms Rollup.EVM.foreign_xi_balances
#print axioms Rollup.EVM.protected_call_balances_of_steps
#print axioms Rollup.EVM.call_helper_balances
#print axioms Rollup.EVM.call_step_balances
#print axioms Rollup.EVM.protected_creation_balances_of_steps
#print axioms Rollup.EVM.incrementNonce_ethLedger
#print axioms Rollup.EVM.incrementNonce_storage
#print axioms Rollup.EVM.incrementNonce_nonzero
#print axioms Rollup.EVM.incrementNonce_lockedWorld
#print axioms Rollup.EVM.call_creation_depth_limit_ledger
#print axioms Rollup.EVM.foreign_step_balances_at_limit
#print axioms Rollup.EVM.creation_step_balances
#print axioms Rollup.EVM.foreign_step_balances
#print axioms Rollup.EVM.foreign_execution_balances
#print axioms Rollup.EVM.callback_call_balances
#print axioms Rollup.EVM.callback_creation_balances
#print axioms Rollup.EVM.payment_call_balances
#print axioms Rollup.EVM.project_ethLedger
#print axioms Rollup.EVM.source_payment_balances
#print axioms Rollup.EVM.withdrawal_locked_world
#print axioms Rollup.EVM.withdrawal_payment_balances
#print axioms Rollup.EVM.sendEth_sender_lower_bound

#print axioms Rollup.EVM.source_store_ethLedger
#print axioms Rollup.EVM.withdrawal_lock_projection
#print axioms Rollup.EVM.withdrawal_credit_model
#print axioms Rollup.EVM.withdrawal_final_projection
#print axioms Rollup.callback_of_surplus
#print axioms Rollup.EVM.withdrawal_callback_model
#print axioms Rollup.EVM.withdrawal_source_refines
#print axioms Rollup.EVM.source_refines_model
#print axioms Rollup.EVM.runtime_accepted_source
#print axioms Rollup.EVM.runtime_refines_model
#print axioms Rollup.EVM.runtime_preserves_safe

#print axioms Rollup.EVM.project_boundary
#print axioms Rollup.EVM.boundary_ready_of_state
#print axioms Rollup.EVM.BoundaryReady.pinned
#print axioms Rollup.EVM.BoundaryReady.world
#print axioms Rollup.EVM.boundary_balance_bound
#print axioms Rollup.EVM.boundary_model_extend
#print axioms Rollup.EVM.boundary_ready_extend
#print axioms Rollup.EVM.message_initial_accounts
#print axioms Rollup.EVM.message_initial_balance
#print axioms Rollup.EVM.message_initial_projection
#print axioms Rollup.EVM.message_before_model
#print axioms Rollup.EVM.message_entry_ready
#print axioms Rollup.EVM.message_selected_runtime
#print axioms Rollup.EVM.message_refines_model
#print axioms Rollup.EVM.message_preserves_safe
#print axioms Rollup.EVM.message_rejected_boundary
#print axioms Rollup.EVM.deployment_success_accounts
#print axioms Rollup.EVM.deployment_initial_storage
#print axioms Rollup.EVM.deployment_initial_present
#print axioms Rollup.EVM.deployment_initial_read

#print axioms Rollup.EVM.installRuntime_ethLedger
#print axioms Rollup.EVM.installRuntime_read
#print axioms Rollup.EVM.installRuntime_project
#print axioms Rollup.EVM.installRuntime_ready
#print axioms Rollup.EVM.deployment_initial_ethLedger
#print axioms Rollup.EVM.deployment_written_state
#print axioms Rollup.EVM.deployment_written_ethLedger
#print axioms Rollup.EVM.deployment_written_projection
#print axioms Rollup.EVM.deployment_written_ready
#print axioms Rollup.EVM.deployment_refines_initial
#print axioms Rollup.EVM.deployment_refines_scope
#print axioms Rollup.EVM.deployed_message_refines_model
#print axioms Rollup.EVM.deposit_call_bound
#print axioms Rollup.EVM.deposit_accepted_call_bound
#print axioms Rollup.EVM.batch_accepted_call_bound
#print axioms Rollup.EVM.withdrawal_accepted_call_bound

#print axioms Rollup.EVM.runtime_success_length
#print axioms Rollup.EVM.scalar_getter_call_bound
#print axioms Rollup.EVM.sequencer_getter_call_bound
#print axioms Rollup.EVM.mapping_getter_call_bound
#print axioms Rollup.EVM.runtime_accepted_call_bound
#print axioms Rollup.EVM.message_accepted_call_bound
#print axioms Rollup.EVM.message_accepted_refines_model
#print axioms Rollup.EVM.rd_revert_no_success
#print axioms Rollup.EVM.xi_success_execution
#print axioms Rollup.EVM.static_sstore_precheck
#print axioms Rollup.EVM.static_sstore_no_success
#print axioms Rollup.EVM.rd_sstore_static_no_success
#print axioms Rollup.EVM.batch_static_guard
#print axioms Rollup.EVM.withdrawal_static_guard
#print axioms Rollup.EVM.deposit_static_guard
#print axioms Rollup.EVM.batch_static_no_success
#print axioms Rollup.EVM.withdrawal_static_no_success
#print axioms Rollup.EVM.deposit_static_no_success
#print axioms Rollup.EVM.runtime_static_success_getter
#print axioms Rollup.EVM.runtime_static_preserves_accounts
#print axioms Rollup.EVM.getter_accepted_call_bound
#print axioms Rollup.EVM.runtime_success_equivalence_for
#print axioms Rollup.EVM.runtime_success_call_bound

example : Rollup.EVM.CompletedTraceCorrect := Rollup.EVM.completed_trace_correct
example : Rollup.EVM.DeployedBoundaryTraceCorrect := Rollup.EVM.deployed_boundary_trace_correct

#print axioms Rollup.EVM.boundary_donation
#print axioms Rollup.callTrace_trans
#print axioms Rollup.EVM.execution_step_refines
#print axioms Rollup.EVM.completed_trace_correct
#print axioms Rollup.EVM.completed_trace_custody
#print axioms Rollup.EVM.completed_trace_word_bounds
#print axioms Rollup.EVM.deployed_boundary_trace_correct
#print axioms Rollup.EVM.deployed_trace_from_calldata
#print axioms Rollup.EVM.runtime_success_scoped_binding
#print axioms Rollup.EVM.message_accepted_scoped_binding
#print axioms Rollup.EVM.event_covered_iff_keys
#print axioms Rollup.EVM.execution_scope_fixed
#print axioms Rollup.EVM.execution_scope_covered
#print axioms Rollup.EVM.continuing_prefix_environment
#print axioms Rollup.EVM.continuing_callback_prefix
#print axioms Rollup.EVM.callback_instruction_prefix
#print axioms Rollup.EVM.inFlight_frame_callback
#print axioms Rollup.EVM.callback_prefix_safe
#print axioms Rollup.EVM.withdrawal_transfer_safe
#print axioms Rollup.EVM.withdrawal_callback_prefix_safe
#print axioms Rollup.EVM.withdrawal_callback_prefix_custody
#print axioms Rollup.EVM.callback_transfer_safe
#print axioms Rollup.EVM.callback_creation_transfer_safe
#print axioms Rollup.EVM.message_execute_entry
#print axioms Rollup.EVM.call_site_funded
#print axioms Rollup.EVM.call_site_outcome
#print axioms Rollup.EVM.call_site_code
#print axioms Rollup.EVM.call_site_prefix_safe
#print axioms Rollup.EVM.call_opcode_helper
#print axioms Rollup.EVM.call_opcode_source
#print axioms Rollup.EVM.call_opcode_target
#print axioms Rollup.EVM.call_opcode_prefix_safe
#print axioms Rollup.EVM.child_call_prefix_safe
#print axioms Rollup.EVM.destruction_static_state
#print axioms Rollup.EVM.selfdestruct_step_static
#print axioms Rollup.EVM.boundary_surplus_frame
#print axioms Rollup.EVM.selfdestruct_boundary_refines
#print axioms Rollup.EVM.selfdestruct_instruction_refines
#print axioms Rollup.EVM.instruction_account_step
#print axioms Rollup.EVM.theta_rejected_checkpoint
#print axioms Rollup.EVM.sstore_other_account
#print axioms Rollup.EVM.tstore_other_account
#print axioms Rollup.EVM.local_step_other_account
#print axioms Rollup.EVM.local_step_boundary
#print axioms Rollup.EVM.local_instruction_boundary
#print axioms Rollup.EVM.call_opcode_rollup_context
#print axioms Rollup.EVM.call_site_calldata_bound
#print axioms Rollup.EVM.call_opcode_rollup_selected
#print axioms Rollup.EVM.call_opcode_rollup_environment
#print axioms Rollup.EVM.call_helper_rollup_refines
#print axioms Rollup.EVM.call_opcode_kind
#print axioms Rollup.EVM.call_site_disabled_accounts
#print axioms Rollup.EVM.call_helper_rollup_total
#print axioms Rollup.EVM.call_opcode_rollup_refines
#print axioms Rollup.EVM.call_instruction_rollup_refines
#print axioms Rollup.EVM.creation_execute_entry
#print axioms Rollup.EVM.creation_pinned_collision
#print axioms Rollup.EVM.creation_fresh_foreign
#print axioms Rollup.EVM.creation_collision_entry_error
#print axioms Rollup.EVM.creation_collision_prefix
#print axioms Rollup.EVM.creation_collision_execute
#print axioms Rollup.EVM.creation_call_error
#print axioms Rollup.EVM.creation_call_revert
#print axioms Rollup.EVM.creation_call_accepted
#print axioms Rollup.EVM.creation_accepted_fresh
#print axioms Rollup.EVM.creation_fresh_not_sender
#print axioms Rollup.EVM.continuing_prefix_entry_error
#print axioms Rollup.EVM.instruction_prefix_entry_error
#print axioms Rollup.EVM.invalid_entry_error
#print axioms Rollup.EVM.creation_fresh_prefix_safe
#print axioms Rollup.EVM.creation_opcode_kind
#print axioms Rollup.EVM.creation_site_accounts
#print axioms Rollup.EVM.creation_site_funded
#print axioms Rollup.EVM.creation_site_nonce
#print axioms Rollup.EVM.creation_site_reservation
#print axioms Rollup.EVM.creation_site_fresh_prefix
#print axioms Rollup.EVM.creation_opcode_accounts
#print axioms Rollup.EVM.sendEthCreate_same_other_balance
#print axioms Rollup.EVM.sendEthCreate_protected_balance
#print axioms Rollup.EVM.creation_transfer_safe
#print axioms Rollup.EVM.creation_prefix_safe
#print axioms Rollup.EVM.creation_site_prefix_safe
#print axioms Rollup.EVM.child_creation_prefix_safe
#print axioms Rollup.EVM.active_prefix_invalid_entry
#print axioms Rollup.EVM.creation_collision_active_prefix
#print axioms Rollup.EVM.creation_collision_active_safe
#print axioms Rollup.EVM.account_preserving_step
#print axioms Rollup.EVM.account_preserving_instruction
#print axioms Rollup.EVM.account_preserving_no_child
#print axioms Rollup.EVM.frame_certificate_continuing
#print axioms Rollup.EVM.frame_certificate_instruction
#print axioms Rollup.EVM.frame_certificate_no_child
#print axioms Rollup.EVM.frame_certificate_active
#print axioms Rollup.EVM.precheck_cursor
#print axioms Rollup.EVM.abstract_unary_sound
#print axioms Rollup.EVM.abstract_binary_sound
#print axioms Rollup.EVM.abstract_isZero_sound
#print axioms Rollup.EVM.abstract_lockedLoad_sound
#print axioms Rollup.EVM.abstract_successors_neutral
#print axioms Rollup.EVM.abstract_cursor_precheck
#print axioms Rollup.EVM.abstract_execBinOp
#print axioms Rollup.EVM.abstract_execUnOp
#print axioms Rollup.EVM.abstract_execSload
#print axioms Rollup.EVM.path_certificate_row
#print axioms Rollup.EVM.path_certificate_neutral
#print axioms Rollup.EVM.abstract_jump_step
#print axioms Rollup.EVM.abstract_jumpIf_step
#print axioms Rollup.EVM.abstract_stack_get
#print axioms Rollup.EVM.abstract_stack_set
#print axioms Rollup.EVM.abstract_duplicate
#print axioms Rollup.EVM.abstract_push
#print axioms Rollup.EVM.abstract_executionEnvOp
#print axioms Rollup.EVM.abstract_push0_step
#print axioms Rollup.EVM.abstract_push_step
#print axioms Rollup.EVM.abstract_jumpdest_step
#print axioms Rollup.EVM.abstract_unary_read
#print axioms Rollup.EVM.abstract_mload_step
#print axioms Rollup.EVM.abstract_keccak_step
#print axioms Rollup.EVM.swap_stack_shape
#print axioms Rollup.EVM.abstract_exchange
#print axioms Rollup.EVM.abstract_pop_step
#print axioms Rollup.EVM.abstract_mstore_step
#print axioms Rollup.EVM.instruction_state_step
#print axioms Rollup.EVM.locked_paths_initial
#print axioms Rollup.EVM.locked_paths_closed
#print axioms Rollup.EVM.locked_paths_row
#print axioms Rollup.EVM.locked_cursor_neutral
#print axioms Rollup.EVM.continuing_instruction_kind
#print axioms Rollup.EVM.abstract_step_sound
#print axioms Rollup.EVM.abstract_instruction_sound
#print axioms Rollup.EVM.lockedFrameCertificate
#print axioms Rollup.EVM.locked_frame_initial
#print axioms Rollup.EVM.locked_active_accounts
#print axioms Rollup.EVM.call_site_entry_safe
#print axioms Rollup.EVM.child_call_entry_safe
#print axioms Rollup.EVM.selected_pinned_code
#print axioms Rollup.EVM.child_call_locked_active_accounts
#print axioms Rollup.EVM.child_creation_active_cases
#print axioms Rollup.EVM.callback_active_prefix_safe
#print axioms Rollup.EVM.callback_active_prefix_correct

example : Rollup.EVM.CallbackActivePrefixCorrect := Rollup.EVM.callback_active_prefix_correct
#print axioms Rollup.EVM.withdrawal_callback_active_safe
#print axioms Rollup.EVM.withdrawal_callback_active_custody
#print axioms Rollup.EVM.frame_run_sound
#print axioms Rollup.EVM.frame_run_entry_covered
#print axioms Rollup.EVM.child_call_remaining
#print axioms Rollup.EVM.child_creation_remaining
#print axioms Rollup.EVM.frame_run_complete
#print axioms Rollup.EVM.frame_calldata_covered
#print axioms Rollup.EVM.frame_run_covered_of_scope
#print axioms Rollup.EVM.frame_run_scope_covered
#print axioms Rollup.EVM.execution_has_tree
#print axioms Rollup.EVM.execution_has_covered_tree
#print axioms Rollup.EVM.boundary_refines_trans
#print axioms Rollup.EVM.boundary_frame_refines
#print axioms Rollup.EVM.boundary_transfer_refines
#print axioms Rollup.EVM.boundary_creation_transfer_refines
#print axioms Rollup.EVM.boundary_nonce_refines
#print axioms Rollup.EVM.message_tree_accepted_state
#print axioms Rollup.EVM.message_tree_refines
#print axioms Rollup.EVM.child_call_entry_unique
#print axioms Rollup.EVM.child_creation_entry_unique
#print axioms Rollup.EVM.child_entries_exclusive
#print axioms Rollup.EVM.creation_call_rejected
#print axioms Rollup.EVM.creation_call_installed
#print axioms Rollup.EVM.boundary_foreign_code_refines
#print axioms Rollup.EVM.creation_tree_accepted_state
#print axioms Rollup.EVM.creation_tree_refines
#print axioms Rollup.EVM.creation_execution_refines
#print axioms Rollup.EVM.child_call_calldata_covered
#print axioms Rollup.EVM.child_creation_calldata_covered
#print axioms Rollup.EVM.recorded_child_frames_refine
#print axioms Rollup.EVM.message_execution_refines
#print axioms Rollup.EVM.call_site_tree_refines
#print axioms Rollup.EVM.call_instruction_tree_refines
#print axioms Rollup.EVM.creation_opcode_cases
#print axioms Rollup.EVM.creation_instruction_tree_refines
#print axioms Rollup.EVM.nonlocal_operation_cases
#print axioms Rollup.EVM.instruction_tree_refines
#print axioms Rollup.EVM.frame_run_boundary
#print axioms Rollup.EVM.tree_boundary_correct
#print axioms Rollup.EVM.execution_record_covered
#print axioms Rollup.EVM.foreign_execution_refines
#print axioms Rollup.EVM.foreign_message_refines
#print axioms Rollup.EVM.foreign_selected_message_refines
#print axioms Rollup.EVM.foreign_creation_refines

example : Rollup.EVM.TreeBoundaryCorrect := Rollup.EVM.tree_boundary_correct
#print axioms Rollup.EVM.selected_message_refines
#print axioms Rollup.EVM.message_sequence_scope_fixed
#print axioms Rollup.EVM.message_sequence_scope_covered
#print axioms Rollup.EVM.message_sequence_refines
#print axioms Rollup.EVM.deployed_message_sequence_correct
#print axioms Rollup.EVM.runtime_no_selfdestruct_byte
#print axioms Rollup.EVM.parse_selfdestruct_byte
#print axioms Rollup.EVM.runtime_no_selfdestruct
#print axioms Rollup.EVM.selected_message_gas_bound
#print axioms Rollup.EVM.creation_gas_bound
#print axioms Rollup.EVM.refund_gas_bound
#print axioms Rollup.EVM.precheck_destruct_set
#print axioms Rollup.EVM.local_step_destruct_set
#print axioms Rollup.EVM.selfdestruct_step_set
#print axioms Rollup.EVM.addressTransCmp
#print axioms Rollup.EVM.local_instruction_destruct_set
#print axioms Rollup.EVM.selfdestruct_instruction_set
#print axioms Rollup.EVM.foreign_selfdestruct_excludes_rollup
#print axioms Rollup.EVM.runtime_instruction_not_selfdestruct
#print axioms Rollup.EVM.rbNode_erase_toList_filter
#print axioms Rollup.EVM.account_erase_toList_filter
#print axioms Rollup.EVM.account_find?_erase_eq
#print axioms Rollup.EVM.account_find?_erase_ne
#print axioms Rollup.EVM.account_find?_erase
#print axioms Rollup.EVM.account_erase_other
#print axioms Rollup.EVM.ethLedger_erase_le
#print axioms Rollup.EVM.worldEth_erase_le
#print axioms Rollup.EVM.boundary_erase_refines
#print axioms Rollup.EVM.boundary_erase_list_refines
#print axioms Rollup.EVM.boundary_erase_set_refines
#print axioms Rollup.EVM.pinned_account_not_empty
#print axioms Rollup.EVM.address_filter_excludes
#print axioms Rollup.EVM.dead_accounts_exclude_rollup
#print axioms Rollup.EVM.transaction_deletions_refine
#print axioms Rollup.EVM.map_account_values_find
#print axioms Rollup.EVM.reset_transient_find
#print axioms Rollup.EVM.reset_transient_ethLedger
#print axioms Rollup.EVM.reset_transient_read
#print axioms Rollup.EVM.reset_transient_model
#print axioms Rollup.EVM.reset_transient_ready
#print axioms Rollup.EVM.reset_transient_refines
#print axioms Rollup.EVM.transaction_cleanup_refines
#print axioms Rollup.EVM.increase_balance_ledger
#print axioms Rollup.EVM.increase_balance_world
#print axioms Rollup.EVM.increase_balance_storage
#print axioms Rollup.EVM.boundary_bounded_surplus_refines
#print axioms Rollup.EVM.boundary_credit_refines
#print axioms Rollup.EVM.checkpoint_balance
#print axioms Rollup.EVM.checkpoint_world
#print axioms Rollup.EVM.checkpoint_storage
#print axioms Rollup.EVM.checkpoint_refines
#print axioms Rollup.EVM.transaction_fee_credits_refine
#print axioms Rollup.EVM.gas_payment_credits_bound
#print axioms Rollup.EVM.word_min_toNat
#print axioms Rollup.EVM.refund_word_exact
#print axioms Rollup.EVM.refund_word_bound
#print axioms Rollup.EVM.fee_word_credits_bound
#print axioms Rollup.EVM.prepaid_fee_credits_refine
#print axioms Rollup.EVM.transaction_execution_eq
#print axioms Rollup.EVM.transaction_finalization_refines
#print axioms Rollup.EVM.transaction_initial_deletions
#print axioms Rollup.EVM.transaction_provisional_gas_bound
#print axioms Rollup.EVM.transaction_remaining_gas_bound
#print axioms Rollup.EVM.store_keys_ethLedger
#print axioms Rollup.EVM.world_eth_equiv
#print axioms Rollup.EVM.source_world_nonincrease
#print axioms Rollup.EVM.runtime_world_nonincrease
#print axioms Rollup.EVM.rollup_message_world_nonincrease
#print axioms Rollup.EVM.message_tree_budget
#print axioms Rollup.EVM.message_execution_budget
#print axioms Rollup.EVM.creation_tree_budget
#print axioms Rollup.EVM.creation_execution_budget
#print axioms Rollup.EVM.call_site_tree_budget
#print axioms Rollup.EVM.recorded_child_frames_budget
#print axioms Rollup.EVM.call_helper_rollup_budget
#print axioms Rollup.EVM.call_instruction_tree_budget
#print axioms Rollup.EVM.creation_instruction_tree_budget
#print axioms Rollup.EVM.instruction_tree_budget
#print axioms Rollup.EVM.frame_run_budget
#print axioms Rollup.EVM.foreign_execution_budget
#print axioms Rollup.EVM.foreign_message_budget
#print axioms Rollup.EVM.foreign_selected_message_budget
#print axioms Rollup.EVM.selected_message_budget
#print axioms Rollup.EVM.foreign_creation_budget
#print axioms Rollup.EVM.transaction_message_result
#print axioms Rollup.EVM.transaction_creation_result
#print axioms Rollup.EVM.transaction_provisional_preserves
#print axioms Rollup.EVM.legacy_priority_bound
#print axioms Rollup.EVM.dynamic_priority_bound
#print axioms Rollup.EVM.transaction_fee_price_bound
#print axioms Rollup.EVM.checkpoint_nonce_nonzero
#print axioms Rollup.EVM.checkpoint_value_funded
#print axioms Rollup.EVM.transaction_boundary_of_no_deletion
#print axioms Rollup.EVM.sstore_code
#print axioms Rollup.EVM.tstore_code
#print axioms Rollup.EVM.local_step_code
#print axioms Rollup.EVM.precheck_created_set
#print axioms Rollup.EVM.local_step_created_set
#print axioms Rollup.EVM.precheck_survives
#print axioms Rollup.EVM.local_step_survives
#print axioms Rollup.EVM.selfdestruct_created_guard
#print axioms Rollup.EVM.selfdestruct_step_survives
#print axioms Rollup.EVM.local_instruction_survives
#print axioms Rollup.EVM.selfdestruct_instruction_survives
#print axioms Rollup.EVM.account_survives_code_frame
#print axioms Rollup.EVM.message_entry_survives
#print axioms Rollup.EVM.creation_initial_set_excludes
#print axioms Rollup.EVM.creation_entry_survives
#print axioms Rollup.EVM.nonce_survives
#print axioms Rollup.EVM.precompile_substate
#print axioms Rollup.EVM.message_execution_survival_result
#print axioms Rollup.EVM.message_execution_survives
#print axioms Rollup.EVM.precompiled_call_metadata
#print axioms Rollup.EVM.precompiled_call_survives
#print axioms Rollup.EVM.creation_execution_survival_result
#print axioms Rollup.EVM.creation_success_lifecycle
#print axioms Rollup.EVM.creation_execution_survives

#print axioms Rollup.EVM.recorded_child_frames_survive

#print axioms Rollup.EVM.call_site_initial_survives

#print axioms Rollup.EVM.call_site_survival_result

#print axioms Rollup.EVM.call_site_disabled_survives

#print axioms Rollup.EVM.call_site_survives

#print axioms Rollup.EVM.call_opcode_lifecycle

#print axioms Rollup.EVM.creation_opcode_lifecycle

#print axioms Rollup.EVM.creation_opcode_lifecycle_cases

#print axioms Rollup.EVM.call_instruction_survives

#print axioms Rollup.EVM.creation_instruction_survives

#print axioms Rollup.EVM.instruction_tree_survives

#print axioms Rollup.EVM.frame_run_survives

#print axioms Rollup.EVM.execution_survives

#print axioms Rollup.EVM.message_survives

#print axioms Rollup.EVM.selected_message_survives

#print axioms Rollup.EVM.creation_survives

#print axioms Rollup.EVM.transaction_provisional_no_deletion

#print axioms Rollup.EVM.transaction_boundary

#print axioms Rollup.EVM.transaction_sequence_scope_fixed

#print axioms Rollup.EVM.transaction_sequence_scope_covered

#print axioms Rollup.EVM.transaction_sequence_refines

#print axioms Rollup.EVM.deployed_transaction_sequence_correct

#print axioms Rollup.EVM.instruction_survives

#print axioms Rollup.EVM.continuing_prefix_survives

#print axioms Rollup.EVM.instruction_prefix_survives

#print axioms Rollup.EVM.child_call_entry_survives

#print axioms Rollup.EVM.child_creation_entry_survives

#print axioms Rollup.EVM.active_prefix_survives

#print axioms Rollup.EVM.withdrawal_selected_active_safe

#print axioms Rollup.EVM.call_child_binding

#print axioms Rollup.EVM.withdrawal_checks_enabled

#print axioms Rollup.EVM.withdrawal_call_active_safe

#print axioms Rollup.EVM.withdrawal_cursor_active_safe

#print axioms Rollup.EVM.runtime_no_creation_byte
#print axioms Rollup.EVM.parse_creation_byte
#print axioms Rollup.EVM.runtime_no_creation
#print axioms Rollup.EVM.runtime_no_creation_child
#print axioms Rollup.EVM.runtime_prefix_no_creation

#print axioms Rollup.EVM.control_execSload
#print axioms Rollup.EVM.control_sstore_step
#print axioms Rollup.EVM.call_helper_counter
#print axioms Rollup.EVM.call_step_cursor
#print axioms Rollup.EVM.control_call_step
#print axioms Rollup.EVM.control_machineStateOp
#print axioms Rollup.EVM.control_returndatacopy_step
#print axioms Rollup.EVM.control_step_sound
#print axioms Rollup.EVM.control_instruction_sound
#print axioms Rollup.EVM.control_certificate_row
#print axioms Rollup.EVM.control_certificate_call
#print axioms Rollup.EVM.indexed_control_row_sound
#print axioms Rollup.EVM.indexed_control_closed_sound
#print axioms Rollup.EVM.control_table_step
#print axioms Rollup.EVM.control_table_prefix
#print axioms Rollup.EVM.control_table_excludes
#print axioms Rollup.EVM.continuing_prefix_head
#print axioms Rollup.EVM.child_prefix_head
#print axioms Rollup.EVM.child_call_opcode
#print axioms Rollup.EVM.noncall_prefix_head
#print axioms Rollup.EVM.prefix_cursor_initial
#print axioms Rollup.EVM.prefix_cursor_step
#print axioms Rollup.EVM.prefix_cursor_stopped
#print axioms Rollup.EVM.prefix_cursor_step_exists
#print axioms Rollup.EVM.cursor_matches_restore_depth
#print axioms Rollup.EVM.prefix_cursor_guarded
#print axioms Rollup.EVM.prefix_cursor_push0
#print axioms Rollup.EVM.prefix_cursor_push1
#print axioms Rollup.EVM.PCR.initState
#print axioms Rollup.EVM.PCR.stepStack
#print axioms Rollup.EVM.PCR.halt
#print axioms Rollup.EVM.PCR.eq
#print axioms Rollup.EVM.PCR.lt
#print axioms Rollup.EVM.PCR.gt
#print axioms Rollup.EVM.PCR.slt
#print axioms Rollup.EVM.PCR.shr
#print axioms Rollup.EVM.PCR.sub
#print axioms Rollup.EVM.PCR.and
#print axioms Rollup.EVM.PCR.add
#print axioms Rollup.EVM.PCR.shl
#print axioms Rollup.EVM.PCR.swap1
#print axioms Rollup.EVM.PCR.swap2
#print axioms Rollup.EVM.PCR.swap3
#print axioms Rollup.EVM.PCR.swap4
#print axioms Rollup.EVM.PCR.swap5
#print axioms Rollup.EVM.PCR.swap6
#print axioms Rollup.EVM.PCR.swap7
#print axioms Rollup.EVM.PCR.swap8
#print axioms Rollup.EVM.PCR.dup2
#print axioms Rollup.EVM.PCR.dup3
#print axioms Rollup.EVM.PCR.dup4
#print axioms Rollup.EVM.PCR.dup5
#print axioms Rollup.EVM.PCR.dup6
#print axioms Rollup.EVM.PCR.dup7
#print axioms Rollup.EVM.PCR.dup8
#print axioms Rollup.EVM.PCR.dup1
#print axioms Rollup.EVM.PCR.iszero
#print axioms Rollup.EVM.PCR.pop
#print axioms Rollup.EVM.PCR.callvalue
#print axioms Rollup.EVM.PCR.calldatasize
#print axioms Rollup.EVM.PCR.calldataload
#print axioms Rollup.EVM.PCR.jump
#print axioms Rollup.EVM.PCR.jumpiT
#print axioms Rollup.EVM.PCR.jumpiNT
#print axioms Rollup.EVM.PCR.push0
#print axioms Rollup.EVM.PCR.pushConst
#print axioms Rollup.EVM.PCR.jumpdest
#print axioms Rollup.EVM.PCR.push1
#print axioms Rollup.EVM.PCR.push2
#print axioms Rollup.EVM.PCR.push4
#print axioms Rollup.EVM.PCR.mstore
#print axioms Rollup.EVM.PCR.mload
#print axioms Rollup.EVM.PCR.keccak256
#print axioms Rollup.EVM.PCR.sload
#print axioms Rollup.EVM.PCR.sstore
#print axioms Rollup.EVM.PCR.gas
#print axioms Rollup.EVM.PCR.sstore_permission
#print axioms Rollup.EVM.runtime_prefix_prologue
#print axioms Rollup.EVM.runtime_prefix_dispatch
#print axioms Rollup.EVM.runtime_prefix_address_check
#print axioms Rollup.EVM.runtime_prefix_address_check_reject
#print axioms Rollup.EVM.withdrawal_prefix_payment_setup
#print axioms Rollup.EVM.instruction_children_refine
#print axioms Rollup.EVM.instruction_children_covered_of_scope
#print axioms Rollup.EVM.covered_prefix_execution
#print axioms Rollup.EVM.prefix_covered_mono
#print axioms Rollup.EVM.prefix_has_scope
#print axioms Rollup.EVM.continuing_prefix_boundary
#print axioms Rollup.EVM.child_call_entry_boundary
#print axioms Rollup.EVM.indexed_control_chunks_sound
#print axioms Rollup.EVM.withdrawal_prefix_decode
#print axioms Rollup.EVM.withdrawal_prefix_decode_bad_length
#print axioms Rollup.EVM.withdrawal_prefix_decode_bad_owner
#print axioms Rollup.EVM.runtime_prefix_four
#print axioms Rollup.EVM.withdrawal_prefix_entry
#print axioms Rollup.EVM.withdrawal_prefix_credit_load
#print axioms Rollup.EVM.withdrawal_prefix_checks
#print axioms Rollup.EVM.control_indexed_closed
#print axioms Rollup.EVM.blocked_control_indexed_closed

#print axioms Rollup.EVM.array_predicate_chunks_sound
#print axioms Rollup.EVM.blocked_call_certificate
#print axioms Rollup.EVM.blocked_control_paths_closed
#print axioms Rollup.EVM.blocked_control_paths_exclude_call
#print axioms Rollup.EVM.callback_active_storage
#print axioms Rollup.EVM.child_call_entry_bounded
#print axioms Rollup.EVM.child_call_entry_fresh
#print axioms Rollup.EVM.child_call_entry_pinned
#print axioms Rollup.EVM.child_call_entry_storage
#print axioms Rollup.EVM.child_creation_entry_boundary
#print axioms Rollup.EVM.child_creation_entry_bounded
#print axioms Rollup.EVM.child_creation_entry_fresh
#print axioms Rollup.EVM.child_creation_entry_storage
#print axioms Rollup.EVM.child_root_message_origin
#print axioms Rollup.EVM.contract_verification_complete
#print axioms Rollup.EVM.control_call_certificate
#print axioms Rollup.EVM.control_call_enters_blocked
#print axioms Rollup.EVM.control_call_result_blocked
#print axioms Rollup.EVM.control_children_certificate
#print axioms Rollup.EVM.control_frame_call_position
#print axioms Rollup.EVM.control_frame_initial
#print axioms Rollup.EVM.control_frame_step
#print axioms Rollup.EVM.control_paths_children
#print axioms Rollup.EVM.control_paths_closed
#print axioms Rollup.EVM.control_paths_initial
#print axioms Rollup.EVM.control_prefix_ready
#print axioms Rollup.EVM.covered_root_entry_execution
#print axioms Rollup.EVM.creation_entry_fresh
#print axioms Rollup.EVM.deployed_contract_correct
#print axioms Rollup.EVM.fresh_root_payment_bound
#print axioms Rollup.EVM.fresh_root_payment_storage
#print axioms Rollup.EVM.message_code_entry_fresh
#print axioms Rollup.EVM.nonwithdraw_entry_blocked
#print axioms Rollup.EVM.nonwithdraw_prefix_excludes_call
#print axioms Rollup.EVM.payment_control_member
#print axioms Rollup.EVM.payment_control_ready
#print axioms Rollup.EVM.payment_prefix_target
#print axioms Rollup.EVM.root_call_prefix_bound
#print axioms Rollup.EVM.root_entry_binding
#print axioms Rollup.EVM.root_entry_boundary
#print axioms Rollup.EVM.root_entry_bounded
#print axioms Rollup.EVM.root_entry_covered_mono
#print axioms Rollup.EVM.root_entry_fresh
#print axioms Rollup.EVM.root_entry_has_scope
#print axioms Rollup.EVM.root_entry_invalid
#print axioms Rollup.EVM.root_entry_message_origin
#print axioms Rollup.EVM.root_entry_ready
#print axioms Rollup.EVM.root_payment_prefix_safe
#print axioms Rollup.EVM.runtime_call_not_repeated
#print axioms Rollup.EVM.runtime_call_prefix_position
#print axioms Rollup.EVM.transaction_checkpoint_boundary
#print axioms Rollup.EVM.transaction_code_entry_boundary
#print axioms Rollup.EVM.transaction_code_entry_bounded
#print axioms Rollup.EVM.transaction_code_entry_fresh
#print axioms Rollup.EVM.transaction_observations_correct
#print axioms Rollup.EVM.transaction_payment_safe
#print axioms Rollup.EVM.transaction_payment_storage
#print axioms Rollup.EVM.transaction_root_entry_boundary
#print axioms Rollup.EVM.transaction_root_entry_ready
#print axioms Rollup.EVM.transaction_root_message_origin
#print axioms Rollup.EVM.transaction_root_message_refined
#print axioms Rollup.EVM.withdrawal_cursor_active_storage
#print axioms Rollup.EVM.withdrawal_selected_active_storage
