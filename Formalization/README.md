# Lean formalization: phase retrieval for the one-dimensional cubic NLS

This directory is the Lean 4 / Mathlib formalization project accompanying Corollary `cor:cubic-NLS` of the primary manuscript. The public theorem is stated in [`Showcase.lean`](Showcase.lean): `CubicNLS.phase_retrieval_interval` proves the interval version, and `CubicNLS.phase_retrieval_cubic_NLS` obtains the all-spacetime corollary.

## Layout

| Path | Contents |
| --- | --- |
| [`CubicNLSPhaseRetrieval.lean`](CubicNLSPhaseRetrieval.lean) | Top-level import for the formalization. |
| [`Showcase.lean`](Showcase.lean) | Statement-of-record and public corollary. |
| [`Check.lean`](Check.lean) | Axiom audit for the interval theorem. |
| [`Lean_Code/`](Lean_Code/) | Dependency-ordered proof modules. |
| [`Lean_Code/PhaseRetrieval.lean`](Lean_Code/PhaseRetrieval.lean) | Assembly of the phase-retrieval theorem. |
| [`Lean_Code/AXIOM_STATUS.md`](Lean_Code/AXIOM_STATUS.md) | Current axiom inventory and elimination plan. |
| [`paper.tex`](paper.tex) | Expanded formalization-ready mathematical proof. |
| [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md) | Map from the paper to Lean statements. |

The main dependency chain is

```text
Fourier / Strichartz estimates
        ↓
cubic flow and current recovery
        ↓
exterior-product and trace arguments
        ↓
Carleman propagation
        ↓
phase_retrieval_interval → phase_retrieval_cubic_NLS
```

## Setup and audit

The project pins Lean in [`lean-toolchain`](lean-toolchain). Once Lean and its Lake package manager are available, initialize dependencies and run the audit from this directory:

```sh
lake update
lake exe cache get
lake build CubicNLSPhaseRetrieval
lake env lean Showcase.lean
lake env lean Check.lean
```

The checked source intentionally records remaining project axioms; their exact status is authoritative in [`Lean_Code/AXIOM_STATUS.md`](Lean_Code/AXIOM_STATUS.md). In particular, this is a verification project for the corollary, not a claim that every analytic ingredient has already been eliminated to Mathlib foundations alone.
