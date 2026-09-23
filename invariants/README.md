# Invariants

The contract tracks three accounting categories over one ETH balance:

  pending deposits → L2 backing → pending withdrawals → paid out

Deposits add ETH and deposit credit. Batches move credit between categories.
Withdrawals pay ETH and remove withdrawal credit.

The core invariants are in `Invariants.lean`.

The main proof target is `ContractCorrect.lean`, which states that the contract 
preserves those invariants. The result covers the pinned creation and runtime 
bytecode. It starts with fresh deployment and proves safety after each transaction.

| Claim | Formal result |
| --- | --- |
| Custody | `Safe` at transaction boundaries and active payment prefixes |
| Accounting | Exact labeled `CallStep` effects; `batch_conserves_liabilities` |
| Authorization | Actual caller in `CallBound`; `successful_batch_authorized` |
| Continuity | `BatchEnabled` requires the old root and next number |
| Isolation | Exact credit updates in `CallStep`; code and storage frames during callbacks |
| Withdrawal | Exact payment label, checked CALL target and amount, single outgoing CALL, failure rollback |
| Callback | Locked storage stays fixed through active calls and creations |
| Arithmetic | `WordBounded` in `Safe`; checked source and bytecode arithmetic |


# Conditions

- The sequencer is nonzero. Deployment is fresh and has the stated funding conditions.
- The rollup address is not a precompile.
- Total ETH in the modeled world is less than 2^256.
- Storage slots are distinct for the finite set of keys used in the trace.
- L2 transition validity and user entitlement remain outside this contract proof.

The proof covers the pinned EVM model. Model conformance and native precompile
implementations are outside scope.
