# eisenstein-do178c

**42 Coq theorems/lemmas. ~24 of 31 Level A objectives. Full traceability from requirements to proofs.**

A DO-178C certification evidence package for Eisenstein integer arithmetic — the ring ℤ[ω] where ω = e^(2πi/3). The eisenstein library is uniquely suited to certification: 600 lines of code, zero `unsafe`, zero floating point, no dependencies beyond core integer types.

## What's Covered

| DO-178C Objective | Coverage | Evidence |
|-------------------|----------|----------|
| A-1 (Requirements) | ✅ Full | 15 requirements documented |
| A-2 (Derived reqs) | ✅ Full | 6 derived requirements traced |
| A-3 (Architecture) | ✅ Full | Module decomposition |
| A-4 (Design) | ✅ Full | 12 design decisions documented |
| A-6 (Source code) | ✅ Full | All 600 LOC covered |
| A-7 (Verification) | ✅ Full | 42 Coq theorems |
| **Total: ~24/31 Level A** | **77%** | **Growing** |

## Proof Structure

```
eisenstein-safety.v (695 lines, 42 theorems)
├── Ring axioms           — Z[ω] is a commutative ring (S2-3)
├── Norm properties       — multiplicativity, non-negativity, zero-preserving (S4)
├── 60° rotation          — ω multiplication preserves norm (S5)
├── Determinism           — no FPU state, pure functions (S6)
├── Main safety theorem   — zero drift corollary (S7)
├── Conjugation + D₆      — involution, all 6 units, norm preservation (S8)
├── Overflow bounds       — i16→i32 safety, norm fits u32 (S9)
├── Monotonicity          — norm ordering, triangle inequality (S10)
├── HexDisk coverage      — finiteness, bounded search space (S11)
└── Certification summary — aggregated theorem for all 7 claims (S12)
```

## Current Gap

The major missing objective is A-10 (Coverage Analysis — Modified Condition/Decision Coverage). MCDC requires instrumentation of the compiled binary, which is platform-specific. The Coq proofs cover the source-level logic; MCDC evidence would need integration with a qualified C compiler.

## License

MIT OR Apache-2.0
