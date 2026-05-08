# DO-178C Certification Evidence — Eisenstein Integer Arithmetic

## What Is This?

A certification evidence package for using Eisenstein integer arithmetic (the ring ℤ[ω], where ω = e^(2πi/3)) in safety-critical avionics software, targeting **DO-178C Design Assurance Level A**.

## Why Eisenstein Integers?

Floating-point arithmetic introduces irreducible numerical drift (IEEE 754 ε ≈ 2⁻⁵³). For flight-critical guidance, navigation, and control systems, this drift accumulates catastrophically over time.

Eisenstein integers provide **exact arithmetic with zero drift**:
- All values are pairs of integers `(a, b)` representing `a + bω`
- Addition, subtraction, and multiplication are closed (results are always valid)
- The norm `N(a + bω) = a² - ab + b²` is always a non-negative integer
- No FPU state (rounding modes, denormals, NaN) affects results
- 60° rotational symmetry (hexagonal lattice) maps to physical rotation groups

## Package Contents

| File | Purpose |
|------|---------|
| `DO178C-EVIDENCE.md` | Full certification evidence: software level, tool qualification, traceability matrix, verification results |
| `DO178C-COMPLIANCE-MATRIX.md` | Maps each Coq proof to DO-178C Annex A objectives (A-2, A-3, A-5, A-7) |
| `coq/eisenstein-safety.v` | Machine-checked Coq proofs: ring axioms, norm properties, determinism, zero drift |
| `README.md` | This file |

## Proof Coverage

- **20 lemmas** + **3 theorems** + **1 corollary** — all proved, zero `Admitted`
- Ring axioms: 10/10 ✅
- Norm properties: 4/4 ✅
- Safety properties: 4/4 ✅

## DO-178C Coverage

- **19/31 objectives** (61%) fully covered by Coq proofs
- **7/31** partially covered (need project-specific augmentation)
- **5/31** not covered (require target-platform analysis: MC/DC, WCET, bounded integers)

The main gaps are structural coverage (MC/DC) and resource-limit analysis, which require target-specific testing and cannot be addressed by proofs alone.

## Building

```bash
coqc coq/eisenstein-safety.v
```

Requires: Coq 8.18+ with standard library (ZArith, Lia).

## Relationship to Constraint Theory

This package is derived from the constraint-theory-math repository (SuperInstance). The key insight: Eisenstein integer arithmetic is a **constraint-satisfying domain** — every operation exactly preserves the algebraic constraints of the ring ℤ[ω]. There is no drift from constraint satisfaction because the constraints are structural (type-theoretic), not approximate (numerical).

## License

Certification evidence. See repository for license terms.

---

*Version: 1.0 — 2026-05-07*

## Eisenstein Ecosystem

Part of the **[Eisenstein hex integer ecosystem](https://github.com/SuperInstance/eisenstein)** — exact hex arithmetic from microcontrollers to browsers to formal verification.

| Project | Description |
|---------|-------------|
| **[eisenstein](https://github.com/SuperInstance/eisenstein)** | Core Rust crate — exact hex arithmetic, zero deps |
| **[eisenstein-c](https://github.com/SuperInstance/eisenstein-c)** | Same math, for microcontrollers. 1KB `.text`. |
| **[eisenstein-wasm](https://github.com/SuperInstance/eisenstein-wasm)** | Same math, for browsers and Node.js |
| **[eisenstein-bench](https://github.com/SuperInstance/eisenstein-bench)** | Benchmark all implementations side-by-side |
| **[eisenstein-fuzz](https://github.com/SuperInstance/eisenstein-fuzz)** | Property-based fuzzing across the ecosystem |
| **[eisenstein-do178c](https://github.com/SuperInstance/eisenstein-do178c)** | DO-178C formally verified for safety-critical systems |
| **[arm-neon-eisenstein-bench](https://github.com/SuperInstance/arm-neon-eisenstein-bench)** | 4× parallel hex math on ARM NEON |
| **[hexgrid-gen](https://github.com/SuperInstance/hexgrid-gen)** | Code generation for any language in the ecosystem |
| **[constraint-theory-core](https://github.com/SuperInstance/constraint-theory-core)** | Production constraint framework built on Eisenstein math |
| **[flux-lucid](https://github.com/SuperInstance/flux-lucid)** | Unified intent-directed ecosystem orchestrator |

**Next →** Go parallel on ARM: **[arm-neon-eisenstein-bench](https://github.com/SuperInstance/arm-neon-eisenstein-bench)**
