# fv-rollup

A pathfinder toy formally-verified rollup.

- [x] **Custody contract.** ETH only. Accepts deposits, manages withdrawals and a state root.
- [ ] No ZK verifier yet. A trusted sequencer submits L2 transitions.

We use [EquiVM](https://github.com/argotorg/EquiVM) and Lean 4.

## Files

- `contract/`: Solidity and pinned compiler output.
- `tests/`: Solidity tests, fuzz tests, and callback attacks.
- `semantics/`: contract model, storage and ABI bindings, and EVM execution.
- `invariants/`: safety predicates and correctness statements.
- `proofs/`: proofs, internal helpers, and generated certificates.

## Contract

Main entry point: [contract/Rollup.sol](contract/Rollup.sol)

- `deposit(owner)`: receive ETH and add a pending deposit.
- `executeBatch(...)`: consume deposit credit from at most one account. Add withdrawal credit to at most one account. Update the root. Only the sequencer can call this function.
- `withdrawPendingBalance(owner, amount)`: send ETH to the owner. Any caller can trigger payment. Locks state changes during the receiver call.

A batch can consume part of a deposit balance. There is no queue.

## Invariants

The custody contract obeys the following invariants:

- Custody: ETH, including payments in flight, backs pending deposits, L2 backing, and pending withdrawals.
- Accounting: batches move credit; they cannot create credit.
- Authorization: only the sequencer can execute a batch.
- Continuity: use the current root and the next batch number.
- Isolation: change only the specified account credits.
- Withdrawal: pay available credit once. Restore state if payment fails.
- Callback: reject state changes while payment is in flight.
- Arithmetic: keep stored values within 256 bits.

See [invariants/README](invariants/README.md) for details.

## Proof

Install Foundry and elan. Run:

```sh
lake exe cache get
python3 scripts/check.py
```

The script installs and checks the semantic model patches, then checks compiler output, tests, Lean builds, and proof axioms.

The eight invariants are proved for the pinned EVM model, from deployment through complete transactions and active withdrawal callbacks. Proofs use only Lean's standard logical axioms. [proofs/Completion.lean](proofs/Completion.lean) enforces the final theorem types.

