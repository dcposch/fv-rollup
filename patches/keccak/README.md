# Keccak model patch

Apply to EVMLean `9a4001c549041b0f3bc700ed66af5a5ef599c64a`.
`scripts/dependencies.py` checks the revision and all changed files.

`ffi.KEC` uses the Lean Keccak definition. The unused native FFI functions remain.
This makes selector hashes available to kernel-checked proofs.

The model comes from [LeanCrypto](https://github.com/NethermindEth/LeanCrypto/tree/cc4937cdcab1229fa375964fbcfae82b95576ed8).
The Apache-2.0 license is included. Changes adapt the Rat import, array constructor,
and termination proof to Lean 4.29.0. The byte-extraction helper is renamed to
avoid an EVMLean name conflict. The algorithm is unchanged.

This patch is part of the EVM semantic model. It does not prove collision resistance.
The rollup accounting statements retain their finite non-alias condition.

Use `scripts/hash_certificate.py NAME OUTPUT --text TEXT` or `--hex HEX` to
generate a certificate for an input of fewer than 136 bytes. Compile the output
and add its theorem to the audit. The generator checks its hash against `cast`;
Lean checks every proof step.
