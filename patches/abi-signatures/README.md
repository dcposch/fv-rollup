# ABI signature patch

Apply to EquiVM `4b9fddcb353c69e740f7adf3eec1d5338d7073e4`.
`scripts/dependencies.py` checks the revision and all changed files.

Use `Nat.repr` for numeric ABI type widths and array lengths. The upstream
`reprStr` calls the opaque `Format` pretty-printer. Its output cannot reduce
in Lean's kernel. `Nat.repr` has a total decimal-string definition.

This patch is part of the source semantic model. It does not prove equivalence
to the opaque printer. Kernel-checked certificates establish all nine contract
selectors. Runtime checks compare the two printers for all valid integer and
fixed-point widths, all fixed-byte widths, and representative array lengths.
