# Phase retrieval for Schrödinger evolutions

This repository contains research manuscripts on phase retrieval for one-dimensional Schrödinger evolutions, together with a Lean verification of the cubic nonlinear Schrödinger equation (NLS) corollary in the primary manuscript.

## Main results

The primary manuscript proves that, in one spatial dimension, equality of the spacetime modulus of two solutions determines the solution up to one constant unimodular factor.  It treats real, time-dependent potentials in the local class
\[
L^1_t L^\infty_x + L^2_{t,x},
\]
derives the corresponding result for the global \(L^2\) cubic NLS flow, and gives counterexamples for the free equation in dimensions at least two.

The stationary manuscript records complementary results for time-independent potentials: a Masuda-class result for finite-energy solutions, an \(L^2\) result for real Faddeev-class potentials, and recovery from measurements on one exterior half-line for a suitable compactly supported potential.

## Repository layout

- [`Article/schrodinger_phase_retrieval_results.tex`](Article/schrodinger_phase_retrieval_results.tex) — primary manuscript, *Phase retrieval for Schrödinger evolutions*.
- [`Article/schrodinger_phase_retrieval_stationary_results.tex`](Article/schrodinger_phase_retrieval_stationary_results.tex) — manuscript on stationary Schrödinger evolutions.
- [`SchrodingerPR_verified/`](SchrodingerPR_verified/) — expanded cubic-NLS proof and Lean formalization workspace.
- [`main.tex`](main.tex) — earlier working draft and bibliography source.
- [`references/`](references/) — source papers used during development.

## Build the manuscripts

The two article sources are self-contained: their bibliographies are included in the `.tex` files.  With a TeX Live installation that provides `latexmk`, run:

```sh
make article
make stationary
```

or build both with:

```sh
make all
```

The resulting PDFs are written next to their sources in `Article/`.  GitHub Actions builds both manuscripts and exposes the PDFs as workflow artifacts.

## Lean verification

[`SchrodingerPR_verified/`](SchrodingerPR_verified/) contains the Lean verification accompanying Corollary `cor:cubic-NLS` in the primary manuscript.  Its entry point, [`showcase.lean`](SchrodingerPR_verified/showcase.lean), formalizes the stronger interval statement `CubicNLS.phase_retrieval_interval`; its theorem `CubicNLS.phase_retrieval_cubic_NLS` derives the corollary's all-spacetime version.

The verification is not yet axiom-free: its current dependencies and remaining project axioms are documented in [`SchrodingerPR_verified/Lean_Code/AXIOM_STATUS.md`](SchrodingerPR_verified/Lean_Code/AXIOM_STATUS.md).  The intended handoff and verification commands are in [`SchrodingerPR_verified/LLM_HANDOFF.md`](SchrodingerPR_verified/LLM_HANDOFF.md).  A Lean toolchain and Mathlib checkout are required before running those commands.

## Contributing

Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) before opening a pull request.  In particular, keep generated TeX artifacts out of commits and make mathematical changes with enough context for careful review.

## Citation

If you use this work, please cite the repository and the relevant manuscript.  Machine-readable metadata is available in [`CITATION.cff`](CITATION.cff).
