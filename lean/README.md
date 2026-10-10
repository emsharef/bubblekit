# Lean formalization

Machine-checked versions of the project's mathematical claims, in Lean 4 with Mathlib.

## Layout

| Path | Contents |
|---|---|
| `Upstream/` | Results taken from the literature (textbook stochastic calculus, diffusion criteria, cited theorems), stated as hypothesis structures, not re-proved. Each corresponds to an entry `AX-nn` in `../ledger/AXIOMS.md`. |
| `Novel/` | The project's own results, proved from the Upstream structures and Mathlib. |
| `Standalone/` | Self-contained deterministic results (inequalities, finite computations) proved from Mathlib alone. |
| `Audit.lean` | Collects the theorems and their axiom dependencies for the audit. |
| `Upstream.lean`, `Novel.lean`, `Standalone.lean` | Root imports for each layer. |

Proofs are conditional on the Upstream structures they assume, never on new axioms or `sorry`. A result's Lean
statement shows exactly which cited inputs it relies on.

## Where to read the verification record

- `../board/FIDELITY.md`: for each formalized claim, a check that the Lean statement says what the claim
  says, including scope differences and whether the claim is conditional.
- `../ledger/AXIOMS.md`: every cited input, with its source and how it is used.
- `../ledger/AUDIT_LOG.md`: the audit of each cited input against its source text, and of each Upstream structure,
  including its sanity-check instance (genuine, degenerate or vacuous).
- `../paper/PROOFMAP.md`: which numbered result in the paper corresponds to which claim file and Lean declaration.
- `../claims/`: the claims, with their proofs in prose, reviews and status.
- The manuscript's Appendix C summarizes what Lean verifies and what it does not.

## Building

```bash
cd lean
lake exe cache get     # Mathlib build cache
lake build
```

The toolchain is pinned in `lean-toolchain`. A full build checks every file; `lake build Novel` or
`lake build Standalone` builds one layer.
