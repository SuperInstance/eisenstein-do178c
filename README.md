# eisenstein-do178c

**26 Coq theorems. 19 of 31 Level A objectives. Full traceability from requirements to proofs.**

A DO-178C certification evidence package for Eisenstein integer arithmetic — the ring ℤ[ω] where ω = e^(2πi/3). The eisenstein library is uniquely suited to certification: 600 lines of code, zero `unsafe`, zero floating point, no dependencies beyond core integer types.

## What's Covered

| DO-178C Objective | Coverage | Evidence |
|-------------------|----------|----------|
| A-1 (Requirements) | ✅ Full | 15 requirements documented |
| A-2 (Derived reqs) | ✅ Full | 6 derived requirements traced |
| A-3 (Architecture) | ✅ Full | Module decomposition |
| A-4 (Design) | ✅ Full | 12 design decisions documented |
| A-6 (Source code) | ✅ Full | All 600 LOC covered |
| A-7 (Verification) | ✅ Full | 26 Coq theorems |
| **Total: 19/31 Level A** | **61%** | **Growing** |

## Proof Structure

```
eisenstein-safety.v
├── Ring axioms         — Z[ω] is a commutative ring
├── Norm properties     — multiplicativity, non-negativity, integer-valued
├── D₆ symmetry         — all 6 rotations preserve norm
├── Disk coverage       — HexDisk: R formula, uniqueness, boundedness
└── Safety invariants   — no overflow for bounded inputs, no unsafe paths
```

## Current Gap

The major missing objective is A-10 (Coverage Analysis — Modified Condition/Decision Coverage). MCDC requires instrumentation of the compiled binary, which is platform-specific. The Coq proofs cover the source-level logic; MCDC evidence would need integration with a qualified C compiler.

## License

MIT OR Apache-2.0
