# Phase retrieval for Schrödinger evolutions

This repository contains the research manuscript *Phase retrieval for Schrödinger evolutions* and its Lean formalization project. The formalization accompanies Corollary `cor:cubic-NLS`, which establishes phase retrieval for global one-dimensional cubic NLS solutions.

## Repository structure

| Path | Contents |
| --- | --- |
| [`Article/`](Article/) | The primary manuscript source. |
| [`Article/archive/`](Article/archive/) | Archived stationary-results source and a reference PDF. |
| [`Formalization/`](Formalization/) | A dedicated Lean 4 / Mathlib project for the cubic-NLS corollary. |
| [`Formalization/Lean_Code/`](Formalization/Lean_Code/) | Formalization modules, arranged by analytic component. |
| [`Formalization/Showcase.lean`](Formalization/Showcase.lean) | Public theorem statement and the corollary derivation. |
| [`Formalization/Check.lean`](Formalization/Check.lean) | Axiom-audit entry point. |

## Manuscript

The primary result proves that, in one spatial dimension, equality of the spacetime modulus determines a Schrödinger evolution up to a constant unimodular factor. It treats real time-dependent potentials in the local class `L¹_t L∞_x + L²_{t,x}`, gives the global `L²` cubic-NLS corollary, and records counterexamples for the free equation in dimensions at least two.

With TeX Live and `latexmk` installed, build the primary manuscript with:

```sh
make article
```

`make stationary` builds the archived stationary manuscript; `make all` builds both. GitHub Actions compiles both sources and uploads the PDFs as workflow artifacts.

## Lean formalization

[`Formalization/`](Formalization/) follows the Lake-project organization used by contemporary Lean research repositories: top-level entry points expose the public theorem and audit, while `Lean_Code/` contains the dependency-ordered development. See [`Formalization/README.md`](Formalization/README.md) for the module map, build setup, and precise verification status.

## Contributing and citation

Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) before opening a pull request. Citation metadata is in [`CITATION.cff`](CITATION.cff).
